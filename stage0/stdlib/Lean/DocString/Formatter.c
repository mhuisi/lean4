// Lean compiler output
// Module: Lean.DocString.Formatter
// Imports: public import Lean.PrettyPrinter.Formatter public import Lean.DocString.Syntax import Init.Data.Range.Polymorphic.Iterators meta import Init.Data.Range.Polymorphic.GetElemTactic import Lean.DocString.Parser import Lean.DocString.View
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object*);
lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
lean_object* l_String_Slice_lines_lineMap(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_LinebreakView_of(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Doc_BlockView_of(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Doc_ArgValView_of(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Doc_ArgView_of(lean_object*);
lean_object* l_Lean_Doc_LinkTargetView_of(lean_object*);
lean_object* l_Lean_Doc_TextView_getVersoText(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object*);
lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object*);
lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object*);
lean_object* l_Lean_Doc_ImageView_getAlt(lean_object*);
lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
lean_object* l_Lean_Doc_FootnoteView_getName(lean_object*);
lean_object* l_Lean_Doc_TextView_of(lean_object*);
lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object*);
lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object*);
lean_object* l_Lean_Doc_LinkRefView_getName(lean_object*);
lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object*);
lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object*);
lean_object* l_String_lines(lean_object*);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Doc_RoleView_of(lean_object*);
lean_object* l_Lean_Doc_ParaView_of(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NON-ATOM "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NON-IDENT "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "+ "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\t"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\\"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "%%%\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_versoDocumentToString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoDocumentToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_document_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document_formatter___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_document_formatter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_3),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(163, 42, 193, 184, 186, 47, 31, 255)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object* v_x_2_){
_start:
{
lean_object* v_stx_4_; 
switch(lean_obj_tag(v_x_2_))
{
case 1:
{
lean_object* v_args_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_args_13_ = lean_ctor_get(v_x_2_, 2);
v___x_14_ = lean_array_get_size(v_args_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_dec_eq(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_args_13_);
lean_dec_ref_known(v_x_2_, 3);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_array_fget(v_args_13_, v___x_17_);
lean_dec_ref(v_args_13_);
v_x_2_ = v___x_18_;
goto _start;
}
}
case 2:
{
lean_object* v_val_20_; 
v_val_20_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_val_20_);
lean_dec_ref_known(v_x_2_, 2);
return v_val_20_;
}
default: 
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
}
v___jp_3_:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_5_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = 0;
v___x_8_ = l_Lean_Syntax_formatStx(v_stx_4_, v___x_6_, v___x_7_);
v___x_9_ = l_Std_Format_defWidth;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = l_Std_Format_pretty(v___x_8_, v___x_9_, v___x_10_, v___x_10_);
v___x_12_ = lean_string_append(v___x_5_, v___x_11_);
lean_dec_ref(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object* v_x_22_){
_start:
{
lean_object* v_stx_24_; 
switch(lean_obj_tag(v_x_22_))
{
case 1:
{
lean_object* v_args_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_args_33_ = lean_ctor_get(v_x_22_, 2);
v___x_34_ = lean_array_get_size(v_args_33_);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_dec_eq(v___x_34_, v___x_35_);
if (v___x_36_ == 0)
{
v_stx_24_ = v_x_22_;
goto v___jp_23_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc_ref(v_args_33_);
lean_dec_ref_known(v_x_22_, 3);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_fget(v_args_33_, v___x_37_);
lean_dec_ref(v_args_33_);
v_x_22_ = v___x_38_;
goto _start;
}
}
case 3:
{
lean_object* v_val_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; 
v_val_40_ = lean_ctor_get(v_x_22_, 2);
lean_inc(v_val_40_);
lean_dec_ref_known(v_x_22_, 4);
v___x_41_ = l_Lean_Name_eraseMacroScopes(v_val_40_);
lean_dec(v_val_40_);
v___x_42_ = 1;
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_41_, v___x_42_);
return v___x_43_;
}
default: 
{
v_stx_24_ = v_x_22_;
goto v___jp_23_;
}
}
v___jp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_25_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0));
v___x_26_ = lean_box(0);
v___x_27_ = 0;
v___x_28_ = l_Lean_Syntax_formatStx(v_stx_24_, v___x_26_, v___x_27_);
v___x_29_ = l_Std_Format_defWidth;
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Std_Format_pretty(v___x_28_, v___x_29_, v___x_30_, v___x_30_);
v___x_32_ = lean_string_append(v___x_25_, v___x_31_);
lean_dec_ref(v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(uint8_t v_x_46_){
_start:
{
if (v_x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = lean_unsigned_to_nat(0u);
return v___x_47_;
}
else
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(1u);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___boxed(lean_object* v_x_49_){
_start:
{
uint8_t v_x_boxed_50_; lean_object* v_res_51_; 
v_x_boxed_50_ = lean_unbox(v_x_49_);
v_res_51_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_x_boxed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg___boxed(lean_object* v_k_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(v_k_53_);
lean_dec(v_k_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_object* v_motive_55_, lean_object* v_ctorIdx_56_, uint8_t v_t_57_, lean_object* v_h_58_, lean_object* v_k_59_){
_start:
{
lean_inc(v_k_59_);
return v_k_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___boxed(lean_object* v_motive_60_, lean_object* v_ctorIdx_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_k_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(v_motive_60_, v_ctorIdx_61_, v_t_boxed_65_, v_h_63_, v_k_64_);
lean_dec(v_k_64_);
lean_dec(v_ctorIdx_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(lean_object* v_ordered_67_){
_start:
{
lean_inc(v_ordered_67_);
return v_ordered_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg___boxed(lean_object* v_ordered_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(v_ordered_68_);
lean_dec(v_ordered_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_object* v_motive_70_, uint8_t v_t_71_, lean_object* v_h_72_, lean_object* v_ordered_73_){
_start:
{
lean_inc(v_ordered_73_);
return v_ordered_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_ordered_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_ordered_77_);
lean_dec(v_ordered_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(lean_object* v_unordered_80_){
_start:
{
lean_inc(v_unordered_80_);
return v_unordered_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg___boxed(lean_object* v_unordered_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(v_unordered_81_);
lean_dec(v_unordered_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_unordered_86_){
_start:
{
lean_inc(v_unordered_86_);
return v_unordered_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___boxed(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_unordered_90_){
_start:
{
uint8_t v_t_boxed_91_; lean_object* v_res_92_; 
v_t_boxed_91_ = lean_unbox(v_t_88_);
v_res_92_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(v_motive_87_, v_t_boxed_91_, v_h_89_, v_unordered_90_);
lean_dec(v_unordered_90_);
return v_res_92_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(uint8_t v_x_93_, uint8_t v_y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_x_93_);
v___x_96_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_y_94_);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_x_21__boxed_100_; uint8_t v_y_22__boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_x_21__boxed_100_ = lean_unbox(v_x_98_);
v_y_22__boxed_101_ = lean_unbox(v_y_99_);
v_res_102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v_x_21__boxed_100_, v_y_22__boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object* v_stx_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Doc_BlockView_of(v_stx_112_);
if (lean_obj_tag(v___x_113_) == 1)
{
lean_object* v_val_114_; 
v_val_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v___x_113_, 1);
switch(lean_obj_tag(v_val_114_))
{
case 1:
{
lean_object* v___x_115_; 
lean_dec_ref_known(v_val_114_, 1);
v___x_115_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0));
return v___x_115_;
}
case 2:
{
lean_object* v___x_116_; 
lean_dec_ref_known(v_val_114_, 1);
v___x_116_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1));
return v___x_116_;
}
default: 
{
lean_object* v___x_117_; 
lean_dec(v_val_114_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object* v_prev_x3f_119_, lean_object* v_stx_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(v_stx_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_141_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_141_ == 0)
{
v___x_125_ = v___x_121_;
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_val_123_);
lean_dec(v___x_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___y_128_; 
if (lean_obj_tag(v_prev_x3f_119_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 0;
v___y_128_ = v___x_134_;
goto v___jp_127_;
}
else
{
lean_object* v_val_135_; uint8_t v_kind_136_; uint8_t v_alternate_137_; uint8_t v___x_138_; uint8_t v___x_139_; 
v_val_135_ = lean_ctor_get(v_prev_x3f_119_, 0);
v_kind_136_ = lean_ctor_get_uint8(v_val_135_, 0);
v_alternate_137_ = lean_ctor_get_uint8(v_val_135_, 1);
v___x_138_ = lean_unbox(v_val_123_);
v___x_139_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v___x_138_, v_kind_136_);
if (v___x_139_ == 0)
{
v___y_128_ = v___x_139_;
goto v___jp_127_;
}
else
{
if (v_alternate_137_ == 0)
{
v___y_128_ = v___x_139_;
goto v___jp_127_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
v___y_128_ = v___x_140_;
goto v___jp_127_;
}
}
}
v___jp_127_:
{
lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_132_; 
v___x_129_ = lean_alloc_ctor(0, 0, 2);
v___x_130_ = lean_unbox(v_val_123_);
lean_dec(v_val_123_);
lean_ctor_set_uint8(v___x_129_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_129_, 1, v___y_128_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object* v_prev_x3f_142_, lean_object* v_stx_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_prev_x3f_142_, v_stx_143_);
lean_dec(v_prev_x3f_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object* v_s_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_string_append(v_a_146_, v_s_145_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object* v_s_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_150_, v_a_151_);
lean_dec_ref(v_s_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object* v_s_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_153_, v_a_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object* v_s_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(v_s_157_, v_a_158_, v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_s_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_zero_163_; uint8_t v_isZero_164_; 
v_zero_163_ = lean_unsigned_to_nat(0u);
v_isZero_164_ = lean_nat_dec_eq(v_x_161_, v_zero_163_);
if (v_isZero_164_ == 1)
{
lean_dec(v_x_161_);
return v_x_162_;
}
else
{
uint32_t v___x_165_; lean_object* v_one_166_; lean_object* v_n_167_; lean_object* v___x_168_; 
v___x_165_ = 32;
v_one_166_ = lean_unsigned_to_nat(1u);
v_n_167_ = lean_nat_sub(v_x_161_, v_one_166_);
lean_dec(v_x_161_);
v___x_168_ = lean_string_push(v_x_162_, v___x_165_);
v_x_161_ = v_n_167_;
v_x_162_ = v___x_168_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_172_ = lean_string_utf8_byte_size(v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_179_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_180_ = lean_string_utf8_byte_size(v_a_175_);
v___x_181_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_182_ = lean_nat_dec_le(v___x_181_, v___x_180_);
if (v___x_182_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_nat_sub(v___x_180_, v___x_181_);
v___x_185_ = lean_string_memcmp(v_a_175_, v___x_179_, v___x_184_, v___x_183_, v___x_181_);
lean_dec(v___x_184_);
if (v___x_185_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
lean_inc(v_a_174_);
v___x_187_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_174_, v___x_186_);
v___x_188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_187_, v_a_175_);
lean_dec_ref(v___x_187_);
return v___x_188_;
}
}
v___jp_176_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_175_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_189_, v_a_190_);
lean_dec(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t v___x_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v___x_195_, lean_object* v_a_196_, uint8_t v_b_197_){
_start:
{
lean_object* v___x_198_; uint8_t v_decide_199_; 
v___x_198_ = lean_nat_sub(v___x_193_, v___x_194_);
v_decide_199_ = lean_nat_dec_eq(v_a_196_, v___x_198_);
lean_dec(v___x_198_);
if (v_decide_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_nat_add(v___x_194_, v_a_196_);
lean_dec(v_a_196_);
v___x_201_ = lean_string_utf8_next_fast(v___x_195_, v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_nat_sub(v___x_201_, v___x_194_);
if (v_b_197_ == 0)
{
{
lean_object* _tmp_4 = v___x_202_;
uint8_t _tmp_5 = v___x_192_;
v_a_196_ = _tmp_4;
v_b_197_ = _tmp_5;
}
goto _start;
}
else
{
v_a_196_ = v___x_202_;
v_b_197_ = v_decide_199_;
goto _start;
}
}
else
{
lean_dec(v_a_196_);
return v_b_197_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
uint8_t v___x_1740__boxed_211_; uint8_t v_b_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v___x_1740__boxed_211_ = lean_unbox(v___x_205_);
v_b_boxed_212_ = lean_unbox(v_b_210_);
v_res_213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_1740__boxed_211_, v___x_206_, v___x_207_, v___x_208_, v_a_209_, v_b_boxed_212_);
lean_dec_ref(v___x_208_);
lean_dec(v___x_207_);
lean_dec(v___x_206_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object* v_s_215_, lean_object* v_pos_216_){
_start:
{
lean_object* v_str_217_; lean_object* v_startInclusive_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v_decide_222_; 
v_str_217_ = lean_ctor_get(v_s_215_, 0);
v_startInclusive_218_ = lean_ctor_get(v_s_215_, 1);
v___x_219_ = lean_nat_add(v_startInclusive_218_, v_pos_216_);
v___x_220_ = lean_nat_sub(v___x_219_, v_startInclusive_218_);
v___x_221_ = lean_unsigned_to_nat(0u);
v_decide_222_ = lean_nat_dec_eq(v___x_220_, v___x_221_);
if (v_decide_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint32_t v___x_228_; uint32_t v___x_229_; uint8_t v___x_230_; 
lean_inc(v_startInclusive_218_);
lean_inc_ref(v_str_217_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v_str_217_);
lean_ctor_set(v___x_223_, 1, v_startInclusive_218_);
lean_ctor_set(v___x_223_, 2, v___x_219_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_sub(v___x_220_, v___x_224_);
lean_dec(v___x_220_);
v___x_226_ = l_String_Slice_posLE(v___x_223_, v___x_225_);
lean_dec_ref_known(v___x_223_, 3);
v___x_227_ = lean_nat_add(v_startInclusive_218_, v___x_226_);
v___x_228_ = lean_string_utf8_get_fast(v_str_217_, v___x_227_);
lean_dec(v___x_227_);
v___x_229_ = 92;
v___x_230_ = lean_uint32_dec_eq(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_dec(v___x_226_);
return v_pos_216_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_nat_add(v___x_226_, v___x_224_);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_pos_216_);
lean_dec(v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v___x_226_);
return v_pos_216_;
}
else
{
lean_dec(v_pos_216_);
v_pos_216_ = v___x_226_;
goto _start;
}
}
}
else
{
lean_dec(v___x_220_);
lean_dec(v___x_219_);
return v_pos_216_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object* v_s_234_, lean_object* v_pos_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v_s_234_, v_pos_235_);
lean_dec_ref(v_s_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object* v_s_237_){
_start:
{
lean_object* v_str_238_; lean_object* v_startInclusive_239_; lean_object* v_endExclusive_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_str_238_ = lean_ctor_get(v_s_237_, 0);
lean_inc_ref(v_str_238_);
v_startInclusive_239_ = lean_ctor_get(v_s_237_, 1);
lean_inc(v_startInclusive_239_);
v_endExclusive_240_ = lean_ctor_get(v_s_237_, 2);
v___x_241_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_242_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_243_ = lean_nat_sub(v_endExclusive_240_, v_startInclusive_239_);
v___x_244_ = lean_nat_dec_le(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_sub(v___x_243_, v___x_242_);
v___x_247_ = lean_nat_add(v_startInclusive_239_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_string_memcmp(v_str_238_, v___x_241_, v___x_247_, v___x_245_, v___x_242_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_265_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = l_String_Slice_Pos_prevn(v_s_237_, v___x_243_, v___x_249_);
v_isSharedCheck_265_ = !lean_is_exclusive(v_s_237_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_266_ = lean_ctor_get(v_s_237_, 2);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_s_237_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_s_237_, 0);
lean_dec(v_unused_268_);
v___x_252_ = v_s_237_;
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_s_237_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_nat_add(v_startInclusive_239_, v___x_250_);
lean_dec(v___x_250_);
lean_inc(v___x_254_);
lean_inc(v_startInclusive_239_);
lean_inc_ref(v_str_238_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 2, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_str_238_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_startInclusive_239_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v___x_254_);
v___x_256_ = v_reuseFailAlloc_264_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_257_ = lean_nat_sub(v___x_254_, v_startInclusive_239_);
v___x_258_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v___x_256_, v___x_257_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_nat_add(v_startInclusive_239_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v_startInclusive_239_);
lean_inc(v___x_254_);
lean_inc(v___x_259_);
lean_inc_ref(v_str_238_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v_str_238_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v___x_254_);
v___x_261_ = 0;
v___x_262_ = l_String_Slice_positions(v___x_260_);
lean_dec_ref_known(v___x_260_, 3);
v___x_263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_248_, v___x_254_, v___x_259_, v_str_238_, v___x_262_, v___x_261_);
lean_dec_ref(v_str_238_);
lean_dec(v___x_259_);
lean_dec(v___x_254_);
return v___x_263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object* v_s_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t v___x_272_, lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_R_278_, lean_object* v_a_279_, uint8_t v_b_280_, lean_object* v_c_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_272_, v___x_273_, v___x_274_, v___x_276_, v_a_279_, v_b_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v___x_286_, lean_object* v___x_287_, lean_object* v_inst_288_, lean_object* v_R_289_, lean_object* v_a_290_, lean_object* v_b_291_, lean_object* v_c_292_){
_start:
{
uint8_t v___x_1855__boxed_293_; uint8_t v_b_boxed_294_; uint8_t v_res_295_; lean_object* v_r_296_; 
v___x_1855__boxed_293_ = lean_unbox(v___x_283_);
v_b_boxed_294_ = lean_unbox(v_b_291_);
v_res_295_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_1855__boxed_293_, v___x_284_, v___x_285_, v___x_286_, v___x_287_, v_inst_288_, v_R_289_, v_a_290_, v_b_boxed_294_, v_c_292_);
lean_dec_ref(v___x_287_);
lean_dec_ref(v___x_286_);
lean_dec(v___x_285_);
lean_dec(v___x_284_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object* v_s_297_){
_start:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_str_298_ = lean_ctor_get(v_s_297_, 0);
lean_inc_ref(v_str_298_);
v_startInclusive_299_ = lean_ctor_get(v_s_297_, 1);
lean_inc(v_startInclusive_299_);
v_endExclusive_300_ = lean_ctor_get(v_s_297_, 2);
v___x_301_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_302_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_303_ = lean_nat_sub(v_endExclusive_300_, v_startInclusive_299_);
v___x_304_ = lean_nat_dec_le(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec(v___x_303_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
lean_dec_ref(v_s_297_);
v___x_305_ = lean_unsigned_to_nat(0u);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_sub(v___x_303_, v___x_302_);
v___x_308_ = lean_nat_add(v_startInclusive_299_, v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = lean_string_memcmp(v_str_298_, v___x_301_, v___x_308_, v___x_306_, v___x_302_);
lean_dec(v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v___x_303_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
lean_dec_ref(v_s_297_);
return v___x_306_;
}
else
{
uint8_t v___x_310_; 
lean_inc_ref(v_s_297_);
v___x_310_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_297_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_327_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = l_String_Slice_Pos_prevn(v_s_297_, v___x_303_, v___x_311_);
v_isSharedCheck_327_ = !lean_is_exclusive(v_s_297_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_328_ = lean_ctor_get(v_s_297_, 2);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_s_297_, 1);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_s_297_, 0);
lean_dec(v_unused_330_);
v___x_314_ = v_s_297_;
v_isShared_315_ = v_isSharedCheck_327_;
goto v_resetjp_313_;
}
else
{
lean_dec(v_s_297_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_327_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_nat_add(v_startInclusive_299_, v___x_312_);
lean_dec(v___x_312_);
v___x_317_ = lean_nat_sub(v___x_316_, v_startInclusive_299_);
v___x_318_ = lean_nat_dec_le(v___x_302_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v___x_317_);
lean_dec(v___x_316_);
lean_del_object(v___x_314_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
return v___x_311_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = lean_nat_sub(v___x_317_, v___x_302_);
lean_dec(v___x_317_);
v___x_320_ = lean_nat_add(v_startInclusive_299_, v___x_319_);
lean_dec(v___x_319_);
v___x_321_ = lean_string_memcmp(v_str_298_, v___x_301_, v___x_320_, v___x_306_, v___x_302_);
lean_dec(v___x_320_);
if (v___x_321_ == 0)
{
lean_dec(v___x_316_);
lean_del_object(v___x_314_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
return v___x_311_;
}
else
{
if (v___x_310_ == 0)
{
lean_object* v_s_323_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 2, v___x_316_);
v_s_323_ = v___x_314_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_str_298_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_startInclusive_299_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v___x_316_);
v_s_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
uint8_t v___x_324_; 
v___x_324_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(2u);
return v___x_325_;
}
else
{
return v___x_311_;
}
}
}
else
{
lean_dec(v___x_316_);
lean_del_object(v___x_314_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
return v___x_311_;
}
}
}
}
}
else
{
lean_dec(v___x_303_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
lean_dec_ref(v_s_297_);
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_zero_333_; uint8_t v_isZero_334_; 
v_zero_333_ = lean_unsigned_to_nat(0u);
v_isZero_334_ = lean_nat_dec_eq(v_x_331_, v_zero_333_);
if (v_isZero_334_ == 1)
{
lean_dec(v_x_331_);
return v_x_332_;
}
else
{
uint32_t v___x_335_; lean_object* v_one_336_; lean_object* v_n_337_; lean_object* v___x_338_; 
v___x_335_ = 10;
v_one_336_ = lean_unsigned_to_nat(1u);
v_n_337_ = lean_nat_sub(v_x_331_, v_one_336_);
lean_dec(v_x_331_);
v___x_338_ = lean_string_push(v_x_332_, v___x_335_);
v_x_331_ = v_n_337_;
v_x_332_ = v___x_338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_341_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_342_ = lean_unsigned_to_nat(2u);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_utf8_byte_size(v_a_340_);
lean_inc_ref(v_a_340_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v_a_340_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
v___x_346_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(v___x_345_);
v___x_347_ = lean_nat_sub(v___x_342_, v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_347_, v___x_341_);
v___x_349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_348_, v_a_340_);
lean_dec_ref(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_a_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(v_a_353_, v_a_354_);
lean_dec(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t v_a_356_){
_start:
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 92;
v___x_358_ = lean_uint32_dec_eq(v_a_356_, v___x_357_);
if (v___x_358_ == 0)
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 42;
v___x_360_ = lean_uint32_dec_eq(v_a_356_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 95;
v___x_362_ = lean_uint32_dec_eq(v_a_356_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 91;
v___x_364_ = lean_uint32_dec_eq(v_a_356_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 93;
v___x_366_ = lean_uint32_dec_eq(v_a_356_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 123;
v___x_368_ = lean_uint32_dec_eq(v_a_356_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 125;
v___x_370_ = lean_uint32_dec_eq(v_a_356_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 96;
v___x_372_ = lean_uint32_dec_eq(v_a_356_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 33;
v___x_374_ = lean_uint32_dec_eq(v_a_356_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 36;
v___x_376_ = lean_uint32_dec_eq(v_a_356_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 10;
v___x_378_ = lean_uint32_dec_eq(v_a_356_, v___x_377_);
return v___x_378_;
}
else
{
return v___x_376_;
}
}
else
{
return v___x_374_;
}
}
else
{
return v___x_372_;
}
}
else
{
return v___x_370_;
}
}
else
{
return v___x_368_;
}
}
else
{
return v___x_366_;
}
}
else
{
return v___x_364_;
}
}
else
{
return v___x_362_;
}
}
else
{
return v___x_360_;
}
}
else
{
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object* v_a_379_){
_start:
{
uint32_t v_a_242__boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_a_242__boxed_380_ = lean_unbox_uint32(v_a_379_);
lean_dec(v_a_379_);
v_res_381_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_242__boxed_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object* v___x_383_, lean_object* v_value_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
uint8_t v_decide_387_; 
v_decide_387_ = lean_nat_dec_eq(v_a_385_, v___x_383_);
if (v_decide_387_ == 0)
{
uint32_t v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_string_utf8_get_fast(v_value_384_, v_a_385_);
v___x_389_ = lean_string_utf8_next_fast(v_value_384_, v_a_385_);
lean_dec(v_a_385_);
v___x_390_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v___x_388_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_string_push(v_b_386_, v___x_388_);
v_a_385_ = v___x_389_;
v_b_386_ = v___x_391_;
goto _start;
}
else
{
uint32_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = 92;
v___x_394_ = lean_string_push(v_b_386_, v___x_393_);
v___x_395_ = lean_string_push(v___x_394_, v___x_388_);
v_a_385_ = v___x_389_;
v_b_386_ = v___x_395_;
goto _start;
}
}
else
{
lean_dec(v_a_385_);
return v_b_386_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object* v___x_397_, lean_object* v_value_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_397_, v_value_398_, v_a_399_, v_b_400_);
lean_dec_ref(v_value_398_);
lean_dec(v___x_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object* v_value_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_string_utf8_byte_size(v_value_402_);
lean_inc_ref(v_value_402_);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v_value_402_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
v___x_407_ = l_String_Slice_positions(v___x_406_);
lean_dec_ref_known(v___x_406_, 3);
v___x_408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_405_, v_value_402_, v___x_407_, v___x_403_);
lean_dec_ref(v_value_402_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_value_411_, lean_object* v_inst_412_, lean_object* v_R_413_, lean_object* v_a_414_, lean_object* v_b_415_, lean_object* v_c_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_410_, v_value_411_, v_a_414_, v_b_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_value_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(v___x_418_, v___x_419_, v_value_420_, v_inst_421_, v_R_422_, v_a_423_, v_b_424_, v_c_425_);
lean_dec_ref(v_value_420_);
lean_dec(v___x_419_);
lean_dec_ref(v___x_418_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object* v_s_427_, lean_object* v_pos_428_){
_start:
{
lean_object* v_str_429_; lean_object* v_startInclusive_430_; lean_object* v_endExclusive_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v_decide_435_; 
v_str_429_ = lean_ctor_get(v_s_427_, 0);
v_startInclusive_430_ = lean_ctor_get(v_s_427_, 1);
v_endExclusive_431_ = lean_ctor_get(v_s_427_, 2);
v___x_432_ = lean_nat_add(v_startInclusive_430_, v_pos_428_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_sub(v_endExclusive_431_, v___x_432_);
v_decide_435_ = lean_nat_dec_eq(v___x_433_, v___x_434_);
lean_dec(v___x_434_);
if (v_decide_435_ == 0)
{
uint32_t v___x_436_; uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_string_utf8_get_fast(v_str_429_, v___x_432_);
v___x_437_ = 48;
v___x_438_ = lean_uint32_dec_le(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
lean_dec(v___x_432_);
return v_pos_428_;
}
else
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 57;
v___x_440_ = lean_uint32_dec_le(v___x_436_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v___x_432_);
return v_pos_428_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_441_ = lean_string_utf8_next_fast(v_str_429_, v___x_432_);
v___x_442_ = lean_nat_sub(v___x_441_, v___x_432_);
lean_dec(v___x_432_);
v___x_443_ = lean_nat_add(v_pos_428_, v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_pos_428_, v___x_444_);
v___x_446_ = lean_nat_dec_le(v___x_445_, v___x_443_);
lean_dec(v___x_445_);
if (v___x_446_ == 0)
{
lean_dec(v___x_443_);
return v_pos_428_;
}
else
{
lean_dec(v_pos_428_);
v_pos_428_ = v___x_443_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_432_);
return v_pos_428_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object* v_s_448_, lean_object* v_pos_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v_s_448_, v_pos_449_);
lean_dec_ref(v_s_448_);
return v_res_450_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_453_ = lean_string_utf8_byte_size(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_456_ = lean_string_utf8_byte_size(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_459_ = lean_string_utf8_byte_size(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_462_ = lean_string_utf8_byte_size(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_465_ = lean_string_utf8_byte_size(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_469_ = lean_string_utf8_byte_size(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___x_473_ = lean_string_utf8_byte_size(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___x_476_ = lean_string_utf8_byte_size(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_479_ = lean_string_utf8_byte_size(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20));
v___x_482_ = lean_string_utf8_byte_size(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_485_ = lean_string_utf8_byte_size(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object* v_text_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_afterDigits_491_; uint8_t v___y_493_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_string_utf8_byte_size(v_text_486_);
lean_inc_ref_n(v_text_486_, 2);
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v_text_486_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
v___x_490_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v___x_489_, v___x_487_);
lean_inc(v___x_490_);
v_afterDigits_491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_afterDigits_491_, 0, v_text_486_);
lean_ctor_set(v_afterDigits_491_, 1, v___x_490_);
lean_ctor_set(v_afterDigits_491_, 2, v___x_488_);
v___x_568_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_569_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23);
v___x_570_ = lean_nat_dec_le(v___x_569_, v___x_488_);
if (v___x_570_ == 0)
{
goto v___jp_563_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = lean_string_memcmp(v_text_486_, v___x_568_, v___x_487_, v___x_487_, v___x_569_);
if (v___x_571_ == 0)
{
goto v___jp_563_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_571_;
}
}
v___jp_492_:
{
if (v___y_493_ == 0)
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref(v_text_486_);
return v___y_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_String_Slice_Pos_nextn(v_afterDigits_491_, v___x_487_, v___x_494_);
lean_dec_ref_known(v_afterDigits_491_, 3);
v___x_496_ = lean_nat_add(v___x_490_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_490_);
v___x_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_497_, 0, v_text_486_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
lean_ctor_set(v___x_497_, 2, v___x_488_);
v___x_498_ = l_String_Slice_Pos_get_x3f(v___x_497_, v___x_487_);
lean_dec_ref_known(v___x_497_, 3);
if (lean_obj_tag(v___x_498_) == 0)
{
return v___y_493_;
}
else
{
lean_object* v_val_499_; uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v_val_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = 32;
v___x_501_ = lean_unbox_uint32(v_val_499_);
lean_dec(v_val_499_);
v___x_502_ = lean_uint32_dec_eq(v___x_501_, v___x_500_);
return v___x_502_;
}
}
}
v___jp_503_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_505_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1);
v___x_506_ = lean_nat_sub(v___x_488_, v___x_490_);
v___x_507_ = lean_nat_dec_le(v___x_505_, v___x_506_);
lean_dec(v___x_506_);
if (v___x_507_ == 0)
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref(v_text_486_);
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = lean_string_memcmp(v_text_486_, v___x_504_, v___x_490_, v___x_487_, v___x_505_);
v___y_493_ = v___x_508_;
goto v___jp_492_;
}
}
v___jp_509_:
{
lean_object* v___x_510_; 
v___x_510_ = l_String_Slice_Pos_get_x3f(v___x_489_, v___x_487_);
lean_dec_ref_known(v___x_489_, 3);
if (lean_obj_tag(v___x_510_) == 0)
{
uint8_t v___x_511_; 
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref(v_text_486_);
v___x_511_ = 0;
return v___x_511_;
}
else
{
lean_object* v_val_512_; uint32_t v___x_513_; uint32_t v___x_514_; uint8_t v___x_515_; 
v_val_512_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v___x_510_, 1);
v___x_513_ = 48;
v___x_514_ = lean_unbox_uint32(v_val_512_);
v___x_515_ = lean_uint32_dec_le(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v_val_512_);
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref(v_text_486_);
return v___x_515_;
}
else
{
uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = 57;
v___x_517_ = lean_unbox_uint32(v_val_512_);
lean_dec(v_val_512_);
v___x_518_ = lean_uint32_dec_le(v___x_517_, v___x_516_);
if (v___x_518_ == 0)
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref(v_text_486_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_519_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_520_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3);
v___x_521_ = lean_nat_sub(v___x_488_, v___x_490_);
v___x_522_ = lean_nat_dec_le(v___x_520_, v___x_521_);
lean_dec(v___x_521_);
if (v___x_522_ == 0)
{
goto v___jp_503_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = lean_string_memcmp(v_text_486_, v___x_519_, v___x_490_, v___x_487_, v___x_520_);
if (v___x_523_ == 0)
{
goto v___jp_503_;
}
else
{
v___y_493_ = v___x_523_;
goto v___jp_492_;
}
}
}
}
}
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_526_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5);
v___x_527_ = lean_nat_dec_le(v___x_526_, v___x_488_);
if (v___x_527_ == 0)
{
goto v___jp_509_;
}
else
{
uint8_t v___x_528_; 
v___x_528_ = lean_string_memcmp(v_text_486_, v___x_525_, v___x_487_, v___x_487_, v___x_526_);
if (v___x_528_ == 0)
{
goto v___jp_509_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_528_;
}
}
}
v___jp_529_:
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_531_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7);
v___x_532_ = lean_nat_dec_le(v___x_531_, v___x_488_);
if (v___x_532_ == 0)
{
goto v___jp_524_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_string_memcmp(v_text_486_, v___x_530_, v___x_487_, v___x_487_, v___x_531_);
if (v___x_533_ == 0)
{
goto v___jp_524_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_533_;
}
}
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_536_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9);
v___x_537_ = lean_nat_dec_le(v___x_536_, v___x_488_);
if (v___x_537_ == 0)
{
goto v___jp_529_;
}
else
{
uint8_t v___x_538_; 
v___x_538_ = lean_string_memcmp(v_text_486_, v___x_535_, v___x_487_, v___x_487_, v___x_536_);
if (v___x_538_ == 0)
{
goto v___jp_529_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_538_;
}
}
}
v___jp_539_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_541_ = lean_string_dec_eq(v_text_486_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_543_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12);
v___x_544_ = lean_nat_dec_le(v___x_543_, v___x_488_);
if (v___x_544_ == 0)
{
goto v___jp_534_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = lean_string_memcmp(v_text_486_, v___x_542_, v___x_487_, v___x_487_, v___x_543_);
if (v___x_545_ == 0)
{
goto v___jp_534_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_545_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_541_;
}
}
v___jp_546_:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13));
v___x_548_ = lean_string_dec_eq(v_text_486_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___x_550_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15);
v___x_551_ = lean_nat_dec_le(v___x_550_, v___x_488_);
if (v___x_551_ == 0)
{
goto v___jp_539_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = lean_string_memcmp(v_text_486_, v___x_549_, v___x_487_, v___x_487_, v___x_550_);
if (v___x_552_ == 0)
{
goto v___jp_539_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_552_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_548_;
}
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___x_555_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17);
v___x_556_ = lean_nat_dec_le(v___x_555_, v___x_488_);
if (v___x_556_ == 0)
{
goto v___jp_546_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = lean_string_memcmp(v_text_486_, v___x_554_, v___x_487_, v___x_487_, v___x_555_);
if (v___x_557_ == 0)
{
goto v___jp_546_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_557_;
}
}
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_560_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19);
v___x_561_ = lean_nat_dec_le(v___x_560_, v___x_488_);
if (v___x_561_ == 0)
{
goto v___jp_553_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = lean_string_memcmp(v_text_486_, v___x_559_, v___x_487_, v___x_487_, v___x_560_);
if (v___x_562_ == 0)
{
goto v___jp_553_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_562_;
}
}
}
v___jp_563_:
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20));
v___x_565_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21);
v___x_566_ = lean_nat_dec_le(v___x_565_, v___x_488_);
if (v___x_566_ == 0)
{
goto v___jp_558_;
}
else
{
uint8_t v___x_567_; 
v___x_567_ = lean_string_memcmp(v_text_486_, v___x_564_, v___x_487_, v___x_487_, v___x_565_);
if (v___x_567_ == 0)
{
goto v___jp_558_;
}
else
{
lean_dec_ref_known(v_afterDigits_491_, 3);
lean_dec(v___x_490_);
lean_dec_ref_known(v___x_489_, 3);
lean_dec_ref(v_text_486_);
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_572_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_576_, lean_object* v_value_577_){
_start:
{
lean_object* v_text_578_; 
lean_inc_ref(v_value_577_);
v_text_578_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_577_);
if (v_atLineStart_576_ == 0)
{
lean_dec_ref(v_value_577_);
return v_text_578_;
}
else
{
uint8_t v___x_579_; 
v___x_579_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_577_);
if (v___x_579_ == 0)
{
return v_text_578_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_581_ = lean_string_append(v___x_580_, v_text_578_);
lean_dec_ref(v_text_578_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_582_, lean_object* v_value_583_){
_start:
{
uint8_t v_atLineStart_boxed_584_; lean_object* v_res_585_; 
v_atLineStart_boxed_584_ = lean_unbox(v_atLineStart_582_);
v_res_585_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_584_, v_value_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_586_, lean_object* v_pos_587_){
_start:
{
lean_object* v_str_588_; lean_object* v_startInclusive_589_; lean_object* v_endExclusive_590_; lean_object* v___x_591_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v_decide_602_; 
v_str_588_ = lean_ctor_get(v_s_586_, 0);
v_startInclusive_589_ = lean_ctor_get(v_s_586_, 1);
v_endExclusive_590_ = lean_ctor_get(v_s_586_, 2);
v___x_591_ = lean_nat_add(v_startInclusive_589_, v_pos_587_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_sub(v_endExclusive_590_, v___x_591_);
v_decide_602_ = lean_nat_dec_eq(v___x_600_, v___x_601_);
lean_dec(v___x_601_);
if (v_decide_602_ == 0)
{
uint32_t v___x_603_; uint32_t v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_string_utf8_get_fast(v_str_588_, v___x_591_);
v___x_604_ = 32;
v___x_605_ = lean_uint32_dec_eq(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 9;
v___x_607_ = lean_uint32_dec_eq(v___x_603_, v___x_606_);
if (v___x_607_ == 0)
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 13;
v___x_609_ = lean_uint32_dec_eq(v___x_603_, v___x_608_);
if (v___x_609_ == 0)
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 10;
v___x_611_ = lean_uint32_dec_eq(v___x_603_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v___x_591_);
return v_pos_587_;
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
else
{
lean_dec(v___x_591_);
return v_pos_587_;
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_593_ = lean_string_utf8_next_fast(v_str_588_, v___x_591_);
v___x_594_ = lean_nat_sub(v___x_593_, v___x_591_);
lean_dec(v___x_591_);
v___x_595_ = lean_nat_add(v_pos_587_, v___x_594_);
lean_dec(v___x_594_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_pos_587_, v___x_596_);
v___x_598_ = lean_nat_dec_le(v___x_597_, v___x_595_);
lean_dec(v___x_597_);
if (v___x_598_ == 0)
{
lean_dec(v___x_595_);
return v_pos_587_;
}
else
{
lean_dec(v_pos_587_);
v_pos_587_ = v___x_595_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_612_, lean_object* v_pos_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_612_, v_pos_613_);
lean_dec_ref(v_s_612_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_615_){
_start:
{
lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v_decide_621_; 
v_startInclusive_616_ = lean_ctor_get(v_s_615_, 1);
v_endExclusive_617_ = lean_ctor_get(v_s_615_, 2);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_615_, v___x_618_);
v___x_620_ = lean_nat_sub(v_endExclusive_617_, v_startInclusive_616_);
v_decide_621_ = lean_nat_dec_eq(v___x_619_, v___x_620_);
lean_dec(v___x_620_);
lean_dec(v___x_619_);
return v_decide_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_622_);
lean_dec_ref(v_s_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
lean_object* v_str_628_; lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; lean_object* v___x_631_; uint8_t v_decide_632_; 
v_str_628_ = lean_ctor_get(v_s_625_, 0);
v_startInclusive_629_ = lean_ctor_get(v_s_625_, 1);
v_endExclusive_630_ = lean_ctor_get(v_s_625_, 2);
v___x_631_ = lean_nat_sub(v_endExclusive_630_, v_startInclusive_629_);
v_decide_632_ = lean_nat_dec_eq(v_a_626_, v___x_631_);
lean_dec(v___x_631_);
if (v_decide_632_ == 0)
{
lean_object* v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_nat_add(v_startInclusive_629_, v_a_626_);
lean_dec(v_a_626_);
v___x_634_ = lean_string_utf8_get_fast(v_str_628_, v___x_633_);
v___x_635_ = 32;
v___x_636_ = lean_uint32_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v___x_633_);
return v_b_627_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_string_utf8_next_fast(v_str_628_, v___x_633_);
lean_dec(v___x_633_);
v___x_638_ = lean_nat_sub(v___x_637_, v_startInclusive_629_);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_b_627_, v___x_639_);
lean_dec(v_b_627_);
v_a_626_ = v___x_638_;
v_b_627_ = v___x_640_;
goto _start;
}
}
else
{
lean_dec(v_a_626_);
return v_b_627_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_642_, v_a_643_, v_b_644_);
lean_dec_ref(v_s_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_646_){
_start:
{
lean_object* v_n_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_n_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_String_Slice_positions(v_s_646_);
v___x_649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_646_, v___x_648_, v_n_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_650_);
lean_dec_ref(v_s_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_652_, lean_object* v_inst_653_, lean_object* v_R_654_, lean_object* v_a_655_, lean_object* v_b_656_, lean_object* v_c_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_652_, v_a_655_, v_b_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_a_662_, lean_object* v_b_663_, lean_object* v_c_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_659_, v_inst_660_, v_R_661_, v_a_662_, v_b_663_, v_c_664_);
lean_dec_ref(v_s_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_src_668_, lean_object* v___x_669_, lean_object* v_a_670_, lean_object* v_b_671_){
_start:
{
lean_object* v_it_673_; lean_object* v_out_674_; 
if (lean_obj_tag(v_a_670_) == 0)
{
lean_object* v_currPos_693_; lean_object* v_searcher_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_723_; 
v_currPos_693_ = lean_ctor_get(v_a_670_, 0);
v_searcher_694_ = lean_ctor_get(v_a_670_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_723_ == 0)
{
v___x_696_ = v_a_670_;
v_isShared_697_ = v_isSharedCheck_723_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_searcher_694_);
lean_inc(v_currPos_693_);
lean_dec(v_a_670_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_723_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_str_698_; lean_object* v_startInclusive_699_; lean_object* v_endExclusive_700_; lean_object* v___x_701_; uint8_t v_decide_702_; 
v_str_698_ = lean_ctor_get(v___x_666_, 0);
v_startInclusive_699_ = lean_ctor_get(v___x_666_, 1);
v_endExclusive_700_ = lean_ctor_get(v___x_666_, 2);
v___x_701_ = lean_nat_sub(v_endExclusive_700_, v_startInclusive_699_);
v_decide_702_ = lean_nat_dec_eq(v_searcher_694_, v___x_701_);
lean_dec(v___x_701_);
if (v_decide_702_ == 0)
{
uint32_t v___x_703_; lean_object* v___x_704_; uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_703_ = 10;
v___x_704_ = lean_nat_add(v_startInclusive_699_, v_searcher_694_);
v___x_705_ = lean_string_utf8_get_fast(v_str_698_, v___x_704_);
v___x_706_ = lean_uint32_dec_eq(v___x_705_, v___x_703_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_searcher_694_);
v___x_707_ = lean_string_utf8_next_fast(v_str_698_, v___x_704_);
lean_dec(v___x_704_);
v___x_708_ = lean_nat_sub(v___x_707_, v_startInclusive_699_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_708_);
v___x_710_ = v___x_696_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_currPos_693_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_712_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v_a_670_ = v___x_710_;
goto _start;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_slice_716_; lean_object* v_nextIt_718_; 
v___x_713_ = lean_string_utf8_next_fast(v_str_698_, v___x_704_);
v___x_714_ = lean_nat_sub(v___x_713_, v___x_704_);
lean_dec(v___x_704_);
v___x_715_ = lean_nat_add(v_searcher_694_, v___x_714_);
lean_dec(v___x_714_);
lean_dec(v_searcher_694_);
lean_inc_ref(v___x_666_);
v_slice_716_ = l_String_Slice_slice_x21(v___x_666_, v_currPos_693_, v___x_715_);
lean_dec(v_currPos_693_);
lean_inc(v___x_715_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_715_);
lean_ctor_set(v___x_696_, 0, v___x_715_);
v_nextIt_718_ = v___x_696_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_715_);
v_nextIt_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_it_673_ = v_nextIt_718_;
v_out_674_ = v_slice_716_;
goto v___jp_672_;
}
}
}
else
{
uint8_t v_decide_720_; 
lean_del_object(v___x_696_);
lean_dec(v_searcher_694_);
v_decide_720_ = lean_nat_dec_eq(v_currPos_693_, v___x_667_);
if (v_decide_720_ == 0)
{
lean_object* v_slice_721_; lean_object* v___x_722_; 
lean_inc(v___x_669_);
lean_inc_ref(v_src_668_);
v_slice_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_721_, 0, v_src_668_);
lean_ctor_set(v_slice_721_, 1, v_currPos_693_);
lean_ctor_set(v_slice_721_, 2, v___x_669_);
v___x_722_ = lean_box(1);
v_it_673_ = v___x_722_;
v_out_674_ = v_slice_721_;
goto v___jp_672_;
}
else
{
lean_dec(v_currPos_693_);
lean_dec(v___x_669_);
lean_dec_ref(v_src_668_);
lean_dec_ref(v___x_666_);
return v_b_671_;
}
}
}
}
else
{
lean_dec(v___x_669_);
lean_dec_ref(v_src_668_);
lean_dec_ref(v___x_666_);
return v_b_671_;
}
v___jp_672_:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = l_String_Slice_lines_lineMap(v_out_674_);
v___x_676_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_675_);
lean_dec_ref(v___x_675_);
if (lean_obj_tag(v_b_671_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v_a_670_ = v_it_673_;
v_b_671_ = v___x_678_;
goto _start;
}
else
{
lean_object* v_val_680_; uint8_t v___x_681_; 
v_val_680_ = lean_ctor_get(v_b_671_, 0);
v___x_681_ = lean_nat_dec_le(v___x_677_, v_val_680_);
if (v___x_681_ == 0)
{
lean_dec(v___x_677_);
v_a_670_ = v_it_673_;
goto _start;
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_690_; 
v_isSharedCheck_690_ = !lean_is_exclusive(v_b_671_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_b_671_, 0);
lean_dec(v_unused_691_);
v___x_684_ = v_b_671_;
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_b_671_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_677_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_677_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v_a_670_ = v_it_673_;
v_b_671_ = v___x_687_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_675_);
v_a_670_ = v_it_673_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_src_726_, lean_object* v___x_727_, lean_object* v_a_728_, lean_object* v_b_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_724_, v___x_725_, v_src_726_, v___x_727_, v_a_728_, v_b_729_);
lean_dec(v___x_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v_src_733_, lean_object* v___x_734_, lean_object* v_a_735_, lean_object* v_b_736_){
_start:
{
lean_object* v_it_738_; lean_object* v_out_739_; 
if (lean_obj_tag(v_a_735_) == 0)
{
lean_object* v_currPos_758_; lean_object* v_searcher_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_788_; 
v_currPos_758_ = lean_ctor_get(v_a_735_, 0);
v_searcher_759_ = lean_ctor_get(v_a_735_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_788_ == 0)
{
v___x_761_ = v_a_735_;
v_isShared_762_ = v_isSharedCheck_788_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_searcher_759_);
lean_inc(v_currPos_758_);
lean_dec(v_a_735_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_788_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_str_763_; lean_object* v_startInclusive_764_; lean_object* v_endExclusive_765_; lean_object* v___x_766_; uint8_t v_decide_767_; 
v_str_763_ = lean_ctor_get(v___x_731_, 0);
v_startInclusive_764_ = lean_ctor_get(v___x_731_, 1);
v_endExclusive_765_ = lean_ctor_get(v___x_731_, 2);
v___x_766_ = lean_nat_sub(v_endExclusive_765_, v_startInclusive_764_);
v_decide_767_ = lean_nat_dec_eq(v_searcher_759_, v___x_766_);
lean_dec(v___x_766_);
if (v_decide_767_ == 0)
{
lean_object* v___x_768_; uint32_t v___x_769_; uint32_t v___x_770_; uint8_t v___x_771_; 
v___x_768_ = lean_nat_add(v_startInclusive_764_, v_searcher_759_);
v___x_769_ = lean_string_utf8_get_fast(v_str_763_, v___x_768_);
v___x_770_ = 10;
v___x_771_ = lean_uint32_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_searcher_759_);
v___x_772_ = lean_string_utf8_next_fast(v_str_763_, v___x_768_);
lean_dec(v___x_768_);
v___x_773_ = lean_nat_sub(v___x_772_, v_startInclusive_764_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_773_);
v___x_775_ = v___x_761_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_currPos_758_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_731_, v___x_732_, v_src_733_, v___x_734_, v___x_775_, v_b_736_);
return v___x_776_;
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_slice_781_; lean_object* v_nextIt_783_; 
v___x_778_ = lean_string_utf8_next_fast(v_str_763_, v___x_768_);
v___x_779_ = lean_nat_sub(v___x_778_, v___x_768_);
lean_dec(v___x_768_);
v___x_780_ = lean_nat_add(v_searcher_759_, v___x_779_);
lean_dec(v___x_779_);
lean_dec(v_searcher_759_);
lean_inc_ref(v___x_731_);
v_slice_781_ = l_String_Slice_slice_x21(v___x_731_, v_currPos_758_, v___x_780_);
lean_dec(v_currPos_758_);
lean_inc(v___x_780_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_780_);
lean_ctor_set(v___x_761_, 0, v___x_780_);
v_nextIt_783_ = v___x_761_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_780_);
v_nextIt_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
v_it_738_ = v_nextIt_783_;
v_out_739_ = v_slice_781_;
goto v___jp_737_;
}
}
}
else
{
uint8_t v_decide_785_; 
lean_del_object(v___x_761_);
lean_dec(v_searcher_759_);
v_decide_785_ = lean_nat_dec_eq(v_currPos_758_, v___x_732_);
if (v_decide_785_ == 0)
{
lean_object* v_slice_786_; lean_object* v___x_787_; 
lean_inc(v___x_734_);
lean_inc_ref(v_src_733_);
v_slice_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_786_, 0, v_src_733_);
lean_ctor_set(v_slice_786_, 1, v_currPos_758_);
lean_ctor_set(v_slice_786_, 2, v___x_734_);
v___x_787_ = lean_box(1);
v_it_738_ = v___x_787_;
v_out_739_ = v_slice_786_;
goto v___jp_737_;
}
else
{
lean_dec(v_currPos_758_);
lean_dec(v___x_734_);
lean_dec_ref(v_src_733_);
lean_dec_ref(v___x_731_);
return v_b_736_;
}
}
}
}
else
{
lean_dec(v___x_734_);
lean_dec_ref(v_src_733_);
lean_dec_ref(v___x_731_);
return v_b_736_;
}
v___jp_737_:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = l_String_Slice_lines_lineMap(v_out_739_);
v___x_741_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_740_);
lean_dec_ref(v___x_740_);
if (lean_obj_tag(v_b_736_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_731_, v___x_732_, v_src_733_, v___x_734_, v_it_738_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; uint8_t v___x_746_; 
v_val_745_ = lean_ctor_get(v_b_736_, 0);
v___x_746_ = lean_nat_dec_le(v___x_742_, v_val_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v___x_742_);
v___x_747_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_731_, v___x_732_, v_src_733_, v___x_734_, v_it_738_, v_b_736_);
return v___x_747_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_isSharedCheck_755_ = !lean_is_exclusive(v_b_736_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_b_736_, 0);
lean_dec(v_unused_756_);
v___x_749_ = v_b_736_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_b_736_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_742_);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_742_);
v___x_752_ = v_reuseFailAlloc_754_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_731_, v___x_732_, v_src_733_, v___x_734_, v_it_738_, v___x_752_);
return v___x_753_;
}
}
}
}
}
else
{
lean_object* v___x_757_; 
lean_dec_ref(v___x_740_);
v___x_757_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_731_, v___x_732_, v_src_733_, v___x_734_, v_it_738_, v_b_736_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_789_, lean_object* v___x_790_, lean_object* v_src_791_, lean_object* v___x_792_, lean_object* v_a_793_, lean_object* v_b_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_789_, v___x_790_, v_src_791_, v___x_792_, v_a_793_, v_b_794_);
lean_dec(v___x_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_796_, lean_object* v_i_797_, lean_object* v_out_798_, lean_object* v_pending_799_, lean_object* v___y_800_, lean_object* v_____r_801_, lean_object* v_out_802_){
_start:
{
lean_object* v_str_803_; lean_object* v_startInclusive_804_; lean_object* v_endExclusive_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_str_803_ = lean_ctor_get(v___x_796_, 0);
v_startInclusive_804_ = lean_ctor_get(v___x_796_, 1);
v_endExclusive_805_ = lean_ctor_get(v___x_796_, 2);
v___x_806_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_797_, v_out_798_);
v___x_807_ = lean_string_append(v_out_802_, v___x_806_);
lean_dec_ref(v___x_806_);
lean_inc(v_pending_799_);
v___x_808_ = l_String_Slice_Pos_nextn(v___x_796_, v_pending_799_, v___y_800_);
v___x_809_ = lean_nat_add(v_startInclusive_804_, v___x_808_);
lean_dec(v___x_808_);
v___x_810_ = lean_string_utf8_extract_fast(v_str_803_, v___x_809_, v_endExclusive_805_);
lean_dec(v___x_809_);
v___x_811_ = lean_string_append(v___x_807_, v___x_810_);
lean_dec_ref(v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_pending_799_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_814_, lean_object* v_i_815_, lean_object* v_out_816_, lean_object* v_pending_817_, lean_object* v___y_818_, lean_object* v_____r_819_, lean_object* v_out_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_814_, v_i_815_, v_out_816_, v_pending_817_, v___y_818_, v_____r_819_, v_out_820_);
lean_dec_ref(v___x_814_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_822_, lean_object* v___y_823_, lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_src_826_, lean_object* v___x_827_, lean_object* v_a_828_, lean_object* v_b_829_){
_start:
{
lean_object* v___y_831_; lean_object* v_val_832_; 
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v_currPos_836_; lean_object* v_searcher_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_900_; 
v_currPos_836_ = lean_ctor_get(v_a_828_, 0);
v_searcher_837_ = lean_ctor_get(v_a_828_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_900_ == 0)
{
v___x_839_ = v_a_828_;
v_isShared_840_ = v_isSharedCheck_900_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_searcher_837_);
lean_inc(v_currPos_836_);
lean_dec(v_a_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_900_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_str_841_; lean_object* v_startInclusive_842_; lean_object* v_endExclusive_843_; lean_object* v_out_844_; lean_object* v_pending_845_; lean_object* v_it_847_; lean_object* v_out_848_; lean_object* v___x_878_; uint8_t v_decide_879_; 
v_str_841_ = lean_ctor_get(v___x_824_, 0);
v_startInclusive_842_ = lean_ctor_get(v___x_824_, 1);
v_endExclusive_843_ = lean_ctor_get(v___x_824_, 2);
v_out_844_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_pending_845_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_nat_sub(v_endExclusive_843_, v_startInclusive_842_);
v_decide_879_ = lean_nat_dec_eq(v_searcher_837_, v___x_878_);
lean_dec(v___x_878_);
if (v_decide_879_ == 0)
{
uint32_t v___x_880_; lean_object* v___x_881_; uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_880_ = 10;
v___x_881_ = lean_nat_add(v_startInclusive_842_, v_searcher_837_);
v___x_882_ = lean_string_utf8_get_fast(v_str_841_, v___x_881_);
v___x_883_ = lean_uint32_dec_eq(v___x_882_, v___x_880_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v_searcher_837_);
v___x_884_ = lean_string_utf8_next_fast(v_str_841_, v___x_881_);
lean_dec(v___x_881_);
v___x_885_ = lean_nat_sub(v___x_884_, v_startInclusive_842_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_885_);
v___x_887_ = v___x_839_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_currPos_836_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_889_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
v_a_828_ = v___x_887_;
goto _start;
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_slice_893_; lean_object* v_nextIt_895_; 
v___x_890_ = lean_string_utf8_next_fast(v_str_841_, v___x_881_);
v___x_891_ = lean_nat_sub(v___x_890_, v___x_881_);
lean_dec(v___x_881_);
v___x_892_ = lean_nat_add(v_searcher_837_, v___x_891_);
lean_dec(v___x_891_);
lean_dec(v_searcher_837_);
lean_inc_ref(v___x_824_);
v_slice_893_ = l_String_Slice_slice_x21(v___x_824_, v_currPos_836_, v___x_892_);
lean_dec(v_currPos_836_);
lean_inc(v___x_892_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_892_);
lean_ctor_set(v___x_839_, 0, v___x_892_);
v_nextIt_895_ = v___x_839_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_892_);
v_nextIt_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v_it_847_ = v_nextIt_895_;
v_out_848_ = v_slice_893_;
goto v___jp_846_;
}
}
}
else
{
uint8_t v_decide_897_; 
lean_del_object(v___x_839_);
lean_dec(v_searcher_837_);
v_decide_897_ = lean_nat_dec_eq(v_currPos_836_, v___x_825_);
if (v_decide_897_ == 0)
{
lean_object* v_slice_898_; lean_object* v___x_899_; 
lean_inc(v___x_827_);
lean_inc_ref(v_src_826_);
v_slice_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_898_, 0, v_src_826_);
lean_ctor_set(v_slice_898_, 1, v_currPos_836_);
lean_ctor_set(v_slice_898_, 2, v___x_827_);
v___x_899_ = lean_box(1);
v_it_847_ = v___x_899_;
v_out_848_ = v_slice_898_;
goto v___jp_846_;
}
else
{
lean_dec(v_currPos_836_);
lean_dec(v___x_827_);
lean_dec_ref(v_src_826_);
lean_dec_ref(v___x_824_);
lean_dec(v___y_823_);
lean_dec(v_i_822_);
return v_b_829_;
}
}
v___jp_846_:
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_877_; 
v_fst_849_ = lean_ctor_get(v_b_829_, 0);
v_snd_850_ = lean_ctor_get(v_b_829_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_b_829_);
if (v_isSharedCheck_877_ == 0)
{
v___x_852_ = v_b_829_;
v_isShared_853_ = v_isSharedCheck_877_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_b_829_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_877_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = l_String_Slice_lines_lineMap(v_out_848_);
v___x_855_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; uint8_t v___x_857_; 
lean_del_object(v___x_852_);
v___x_856_ = lean_string_utf8_byte_size(v_fst_849_);
v___x_857_ = lean_nat_dec_eq(v___x_856_, v_pending_845_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_snd_850_, v___x_858_);
lean_dec(v_snd_850_);
v___x_860_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_859_, v_fst_849_);
v___x_861_ = lean_box(0);
lean_inc(v___y_823_);
lean_inc(v_i_822_);
v___x_862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_854_, v_i_822_, v_out_844_, v_pending_845_, v___y_823_, v___x_861_, v___x_860_);
lean_dec_ref(v___x_854_);
v___y_831_ = v_it_847_;
v_val_832_ = v___x_862_;
goto v___jp_830_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_snd_850_);
v___x_863_ = lean_box(0);
lean_inc(v___y_823_);
lean_inc(v_i_822_);
v___x_864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_854_, v_i_822_, v_out_844_, v_pending_845_, v___y_823_, v___x_863_, v_fst_849_);
lean_dec_ref(v___x_854_);
v___y_831_ = v_it_847_;
v_val_832_ = v___x_864_;
goto v___jp_830_;
}
}
else
{
lean_object* v___x_865_; uint8_t v___x_866_; 
lean_dec_ref(v___x_854_);
v___x_865_ = lean_string_utf8_byte_size(v_fst_849_);
v___x_866_ = lean_nat_dec_eq(v___x_865_, v_pending_845_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_snd_850_, v___x_867_);
lean_dec(v_snd_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_868_);
v___x_870_ = v___x_852_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_828_ = v_it_847_;
v_b_829_ = v___x_870_;
goto _start;
}
}
else
{
lean_object* v___x_874_; 
if (v_isShared_853_ == 0)
{
v___x_874_ = v___x_852_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_snd_850_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v_a_828_ = v_it_847_;
v_b_829_ = v___x_874_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_827_);
lean_dec_ref(v_src_826_);
lean_dec_ref(v___x_824_);
lean_dec(v___y_823_);
lean_dec(v_i_822_);
return v_b_829_;
}
v___jp_830_:
{
if (lean_obj_tag(v_val_832_) == 0)
{
lean_object* v_a_833_; 
lean_dec(v___y_831_);
lean_dec(v___x_827_);
lean_dec_ref(v_src_826_);
lean_dec_ref(v___x_824_);
lean_dec(v___y_823_);
lean_dec(v_i_822_);
v_a_833_ = lean_ctor_get(v_val_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v_val_832_, 1);
return v_a_833_;
}
else
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v_val_832_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v_val_832_, 1);
v_a_828_ = v___y_831_;
v_b_829_ = v_a_834_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_901_, lean_object* v___y_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_src_905_, lean_object* v___x_906_, lean_object* v_a_907_, lean_object* v_b_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_901_, v___y_902_, v___x_903_, v___x_904_, v_src_905_, v___x_906_, v_a_907_, v_b_908_);
lean_dec(v___x_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_910_, lean_object* v___y_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_src_914_, lean_object* v___x_915_, lean_object* v_a_916_, lean_object* v_b_917_){
_start:
{
lean_object* v___y_919_; lean_object* v_val_920_; 
if (lean_obj_tag(v_a_916_) == 0)
{
lean_object* v_currPos_924_; lean_object* v_searcher_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_988_; 
v_currPos_924_ = lean_ctor_get(v_a_916_, 0);
v_searcher_925_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_988_ == 0)
{
v___x_927_ = v_a_916_;
v_isShared_928_ = v_isSharedCheck_988_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_searcher_925_);
lean_inc(v_currPos_924_);
lean_dec(v_a_916_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_988_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_str_929_; lean_object* v_startInclusive_930_; lean_object* v_endExclusive_931_; lean_object* v_out_932_; lean_object* v_pending_933_; lean_object* v_it_935_; lean_object* v_out_936_; lean_object* v___x_966_; uint8_t v_decide_967_; 
v_str_929_ = lean_ctor_get(v___x_912_, 0);
v_startInclusive_930_ = lean_ctor_get(v___x_912_, 1);
v_endExclusive_931_ = lean_ctor_get(v___x_912_, 2);
v_out_932_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_pending_933_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_nat_sub(v_endExclusive_931_, v_startInclusive_930_);
v_decide_967_ = lean_nat_dec_eq(v_searcher_925_, v___x_966_);
lean_dec(v___x_966_);
if (v_decide_967_ == 0)
{
lean_object* v___x_968_; uint32_t v___x_969_; uint32_t v___x_970_; uint8_t v___x_971_; 
v___x_968_ = lean_nat_add(v_startInclusive_930_, v_searcher_925_);
v___x_969_ = lean_string_utf8_get_fast(v_str_929_, v___x_968_);
v___x_970_ = 10;
v___x_971_ = lean_uint32_dec_eq(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_searcher_925_);
v___x_972_ = lean_string_utf8_next_fast(v_str_929_, v___x_968_);
lean_dec(v___x_968_);
v___x_973_ = lean_nat_sub(v___x_972_, v_startInclusive_930_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_973_);
v___x_975_ = v___x_927_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_currPos_924_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_910_, v___y_911_, v___x_912_, v___x_913_, v_src_914_, v___x_915_, v___x_975_, v_b_917_);
return v___x_976_;
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_slice_981_; lean_object* v_nextIt_983_; 
v___x_978_ = lean_string_utf8_next_fast(v_str_929_, v___x_968_);
v___x_979_ = lean_nat_sub(v___x_978_, v___x_968_);
lean_dec(v___x_968_);
v___x_980_ = lean_nat_add(v_searcher_925_, v___x_979_);
lean_dec(v___x_979_);
lean_dec(v_searcher_925_);
lean_inc_ref(v___x_912_);
v_slice_981_ = l_String_Slice_slice_x21(v___x_912_, v_currPos_924_, v___x_980_);
lean_dec(v_currPos_924_);
lean_inc(v___x_980_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_980_);
lean_ctor_set(v___x_927_, 0, v___x_980_);
v_nextIt_983_ = v___x_927_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_980_);
v_nextIt_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_it_935_ = v_nextIt_983_;
v_out_936_ = v_slice_981_;
goto v___jp_934_;
}
}
}
else
{
uint8_t v_decide_985_; 
lean_del_object(v___x_927_);
lean_dec(v_searcher_925_);
v_decide_985_ = lean_nat_dec_eq(v_currPos_924_, v___x_913_);
if (v_decide_985_ == 0)
{
lean_object* v_slice_986_; lean_object* v___x_987_; 
lean_inc(v___x_915_);
lean_inc_ref(v_src_914_);
v_slice_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_986_, 0, v_src_914_);
lean_ctor_set(v_slice_986_, 1, v_currPos_924_);
lean_ctor_set(v_slice_986_, 2, v___x_915_);
v___x_987_ = lean_box(1);
v_it_935_ = v___x_987_;
v_out_936_ = v_slice_986_;
goto v___jp_934_;
}
else
{
lean_dec(v_currPos_924_);
lean_dec(v___x_915_);
lean_dec_ref(v_src_914_);
lean_dec_ref(v___x_912_);
lean_dec(v___y_911_);
lean_dec(v_i_910_);
return v_b_917_;
}
}
v___jp_934_:
{
lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_965_; 
v_fst_937_ = lean_ctor_get(v_b_917_, 0);
v_snd_938_ = lean_ctor_get(v_b_917_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_b_917_);
if (v_isSharedCheck_965_ == 0)
{
v___x_940_ = v_b_917_;
v_isShared_941_ = v_isSharedCheck_965_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_inc(v_fst_937_);
lean_dec(v_b_917_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_965_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = l_String_Slice_lines_lineMap(v_out_936_);
v___x_943_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; uint8_t v___x_945_; 
lean_del_object(v___x_940_);
v___x_944_ = lean_string_utf8_byte_size(v_fst_937_);
v___x_945_ = lean_nat_dec_eq(v___x_944_, v_pending_933_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_snd_938_, v___x_946_);
lean_dec(v_snd_938_);
v___x_948_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_947_, v_fst_937_);
v___x_949_ = lean_box(0);
lean_inc(v___y_911_);
lean_inc(v_i_910_);
v___x_950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_942_, v_i_910_, v_out_932_, v_pending_933_, v___y_911_, v___x_949_, v___x_948_);
lean_dec_ref(v___x_942_);
v___y_919_ = v_it_935_;
v_val_920_ = v___x_950_;
goto v___jp_918_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_snd_938_);
v___x_951_ = lean_box(0);
lean_inc(v___y_911_);
lean_inc(v_i_910_);
v___x_952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_942_, v_i_910_, v_out_932_, v_pending_933_, v___y_911_, v___x_951_, v_fst_937_);
lean_dec_ref(v___x_942_);
v___y_919_ = v_it_935_;
v_val_920_ = v___x_952_;
goto v___jp_918_;
}
}
else
{
lean_object* v___x_953_; uint8_t v___x_954_; 
lean_dec_ref(v___x_942_);
v___x_953_ = lean_string_utf8_byte_size(v_fst_937_);
v___x_954_ = lean_nat_dec_eq(v___x_953_, v_pending_933_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_add(v_snd_938_, v___x_955_);
lean_dec(v_snd_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_956_);
v___x_958_ = v___x_940_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_910_, v___y_911_, v___x_912_, v___x_913_, v_src_914_, v___x_915_, v_it_935_, v___x_958_);
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; 
if (v_isShared_941_ == 0)
{
v___x_962_ = v___x_940_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_snd_938_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_910_, v___y_911_, v___x_912_, v___x_913_, v_src_914_, v___x_915_, v_it_935_, v___x_962_);
return v___x_963_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_915_);
lean_dec_ref(v_src_914_);
lean_dec_ref(v___x_912_);
lean_dec(v___y_911_);
lean_dec(v_i_910_);
return v_b_917_;
}
v___jp_918_:
{
if (lean_obj_tag(v_val_920_) == 0)
{
lean_object* v_a_921_; 
lean_dec(v___y_919_);
lean_dec(v___x_915_);
lean_dec_ref(v_src_914_);
lean_dec_ref(v___x_912_);
lean_dec(v___y_911_);
lean_dec(v_i_910_);
v_a_921_ = lean_ctor_get(v_val_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v_val_920_, 1);
return v_a_921_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v_val_920_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v_val_920_, 1);
v___x_923_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_910_, v___y_911_, v___x_912_, v___x_913_, v_src_914_, v___x_915_, v___y_919_, v_a_922_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_989_, lean_object* v___y_990_, lean_object* v___x_991_, lean_object* v___x_992_, lean_object* v_src_993_, lean_object* v___x_994_, lean_object* v_a_995_, lean_object* v_b_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_989_, v___y_990_, v___x_991_, v___x_992_, v_src_993_, v___x_994_, v_a_995_, v_b_996_);
lean_dec(v___x_992_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_1001_, lean_object* v_src_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___y_1009_; lean_object* v___x_1013_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_string_utf8_byte_size(v_src_1002_);
lean_inc_ref_n(v_src_1002_, 3);
v___x_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_src_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
v___x_1006_ = lean_box(0);
v___x_1007_ = l_String_lines(v_src_1002_);
lean_inc(v___x_1007_);
lean_inc_ref(v___x_1005_);
v___x_1013_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1005_, v___x_1004_, v_src_1002_, v___x_1004_, v___x_1007_, v___x_1006_);
if (lean_obj_tag(v___x_1013_) == 0)
{
v___y_1009_ = v___x_1003_;
goto v___jp_1008_;
}
else
{
lean_object* v_val_1014_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___y_1009_ = v_val_1014_;
goto v___jp_1008_;
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_1001_, v___y_1009_, v___x_1005_, v___x_1004_, v_src_1002_, v___x_1004_, v___x_1007_, v___x_1010_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_fst_1012_);
lean_dec_ref(v___x_1011_);
return v_fst_1012_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_1015_, lean_object* v___y_1016_, lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_src_1019_, lean_object* v___x_1020_, lean_object* v_inst_1021_, lean_object* v_R_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_, lean_object* v_c_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_1015_, v___y_1016_, v___x_1017_, v___x_1018_, v_src_1019_, v___x_1020_, v_a_1023_, v_b_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_1027_, lean_object* v___y_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_src_1031_, lean_object* v___x_1032_, lean_object* v_inst_1033_, lean_object* v_R_1034_, lean_object* v_a_1035_, lean_object* v_b_1036_, lean_object* v_c_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_1027_, v___y_1028_, v___x_1029_, v___x_1030_, v_src_1031_, v___x_1032_, v_inst_1033_, v_R_1034_, v_a_1035_, v_b_1036_, v_c_1037_);
lean_dec(v___x_1030_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_src_1041_, lean_object* v___x_1042_, lean_object* v_inst_1043_, lean_object* v_R_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_c_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1039_, v___x_1040_, v_src_1041_, v___x_1042_, v_a_1045_, v_b_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_src_1051_, lean_object* v___x_1052_, lean_object* v_inst_1053_, lean_object* v_R_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_, lean_object* v_c_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1049_, v___x_1050_, v_src_1051_, v___x_1052_, v_inst_1053_, v_R_1054_, v_a_1055_, v_b_1056_, v_c_1057_);
lean_dec(v___x_1050_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1059_, lean_object* v___y_1060_, lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_src_1063_, lean_object* v___x_1064_, lean_object* v_inst_1065_, lean_object* v_R_1066_, lean_object* v_a_1067_, lean_object* v_b_1068_, lean_object* v_c_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1059_, v___y_1060_, v___x_1061_, v___x_1062_, v_src_1063_, v___x_1064_, v_a_1067_, v_b_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1071_, lean_object* v___y_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_src_1075_, lean_object* v___x_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v_c_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1071_, v___y_1072_, v___x_1073_, v___x_1074_, v_src_1075_, v___x_1076_, v_inst_1077_, v_R_1078_, v_a_1079_, v_b_1080_, v_c_1081_);
lean_dec(v___x_1074_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_src_1085_, lean_object* v___x_1086_, lean_object* v_inst_1087_, lean_object* v_R_1088_, lean_object* v_a_1089_, lean_object* v_b_1090_, lean_object* v_c_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1083_, v___x_1084_, v_src_1085_, v___x_1086_, v_a_1089_, v_b_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v_src_1095_, lean_object* v___x_1096_, lean_object* v_inst_1097_, lean_object* v_R_1098_, lean_object* v_a_1099_, lean_object* v_b_1100_, lean_object* v_c_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1093_, v___x_1094_, v_src_1095_, v___x_1096_, v_inst_1097_, v_R_1098_, v_a_1099_, v_b_1100_, v_c_1101_);
lean_dec(v___x_1094_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_zero_1105_; uint8_t v_isZero_1106_; 
v_zero_1105_ = lean_unsigned_to_nat(0u);
v_isZero_1106_ = lean_nat_dec_eq(v_x_1103_, v_zero_1105_);
if (v_isZero_1106_ == 1)
{
lean_dec(v_x_1103_);
return v_x_1104_;
}
else
{
uint32_t v___x_1107_; lean_object* v_one_1108_; lean_object* v_n_1109_; lean_object* v___x_1110_; 
v___x_1107_ = 96;
v_one_1108_ = lean_unsigned_to_nat(1u);
v_n_1109_ = lean_nat_sub(v_x_1103_, v_one_1108_);
lean_dec(v_x_1103_);
v___x_1110_ = lean_string_push(v_x_1104_, v___x_1107_);
v_x_1103_ = v_n_1109_;
v_x_1104_ = v___x_1110_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1114_ = lean_string_utf8_byte_size(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1115_){
_start:
{
lean_object* v___y_1117_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1139_; 
v___x_1131_ = lean_string_utf8_byte_size(v_value_1115_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1141_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1);
v___x_1142_ = lean_nat_dec_le(v___x_1141_, v___x_1131_);
if (v___x_1142_ == 0)
{
goto v___jp_1133_;
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_string_memcmp(v_value_1115_, v___x_1140_, v___x_1132_, v___x_1132_, v___x_1141_);
if (v___x_1143_ == 0)
{
goto v___jp_1133_;
}
else
{
goto v___jp_1125_;
}
}
}
else
{
lean_object* v___x_1144_; 
lean_dec_ref(v_value_1115_);
v___x_1144_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___y_1117_ = v___x_1144_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_delim_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
lean_inc_ref(v___y_1117_);
v___x_1119_ = l_Lean_Doc_longestBacktickRun(v___y_1117_);
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v___x_1119_, v___x_1120_);
lean_dec(v___x_1119_);
v_delim_1122_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1121_, v___x_1118_);
lean_inc_ref(v_delim_1122_);
v___x_1123_ = lean_string_append(v_delim_1122_, v___y_1117_);
lean_dec_ref(v___y_1117_);
v___x_1124_ = lean_string_append(v___x_1123_, v_delim_1122_);
lean_dec_ref(v_delim_1122_);
return v___x_1124_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_1127_ = lean_string_append(v___x_1126_, v_value_1115_);
lean_dec_ref(v_value_1115_);
v___x_1128_ = lean_string_append(v___x_1127_, v___x_1126_);
v___y_1117_ = v___x_1128_;
goto v___jp_1116_;
}
v___jp_1129_:
{
uint8_t v___x_1130_; 
lean_inc_ref(v_value_1115_);
v___x_1130_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1115_);
if (v___x_1130_ == 0)
{
v___y_1117_ = v_value_1115_;
goto v___jp_1116_;
}
else
{
goto v___jp_1125_;
}
}
v___jp_1133_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1135_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1);
v___x_1136_ = lean_nat_dec_le(v___x_1135_, v___x_1131_);
if (v___x_1136_ == 0)
{
goto v___jp_1129_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_nat_sub(v___x_1131_, v___x_1135_);
v___x_1138_ = lean_string_memcmp(v_value_1115_, v___x_1134_, v___x_1137_, v___x_1132_, v___x_1135_);
lean_dec(v___x_1137_);
if (v___x_1138_ == 0)
{
goto v___jp_1129_;
}
else
{
goto v___jp_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1145_, lean_object* v_as_1146_, size_t v_i_1147_, size_t v_stop_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v___y_1151_; uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_eq(v_i_1147_, v_stop_1148_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_array_uget_borrowed(v_as_1146_, v_i_1147_);
lean_inc(v___x_1156_);
v___x_1157_ = l_Lean_Doc_InlineView_of(v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 1)
{
lean_object* v_val_1158_; 
v_val_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v___x_1157_, 1);
switch(lean_obj_tag(v_val_1158_))
{
case 1:
{
lean_object* v_view_1159_; lean_object* v___y_1161_; uint32_t v___x_1166_; uint8_t v___x_1167_; 
v_view_1159_ = lean_ctor_get(v_val_1158_, 0);
lean_inc_ref(v_view_1159_);
lean_dec_ref_known(v_val_1158_, 1);
v___x_1166_ = 95;
v___x_1167_ = lean_uint32_dec_eq(v_char_1145_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___y_1161_ = v___x_1168_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_unsigned_to_nat(1u);
v___y_1161_ = v___x_1169_;
goto v___jp_1160_;
}
v___jp_1160_:
{
lean_object* v_content_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_content_1162_ = lean_ctor_get(v_view_1159_, 2);
lean_inc_ref(v_content_1162_);
lean_dec_ref(v_view_1159_);
v___x_1163_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1145_, v_content_1162_);
lean_dec_ref(v_content_1162_);
v___x_1164_ = lean_nat_add(v___y_1161_, v___x_1163_);
lean_dec(v___x_1163_);
v___x_1165_ = lean_nat_dec_le(v_b_1149_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v___x_1164_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
else
{
lean_dec(v_b_1149_);
v___y_1151_ = v___x_1164_;
goto v___jp_1150_;
}
}
}
case 2:
{
lean_object* v_view_1170_; lean_object* v___y_1172_; uint32_t v___x_1177_; uint8_t v___x_1178_; 
v_view_1170_ = lean_ctor_get(v_val_1158_, 0);
lean_inc_ref(v_view_1170_);
lean_dec_ref_known(v_val_1158_, 1);
v___x_1177_ = 42;
v___x_1178_ = lean_uint32_dec_eq(v_char_1145_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___y_1172_ = v___x_1179_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___y_1172_ = v___x_1180_;
goto v___jp_1171_;
}
v___jp_1171_:
{
lean_object* v_content_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_content_1173_ = lean_ctor_get(v_view_1170_, 2);
lean_inc_ref(v_content_1173_);
lean_dec_ref(v_view_1170_);
v___x_1174_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1145_, v_content_1173_);
lean_dec_ref(v_content_1173_);
v___x_1175_ = lean_nat_add(v___y_1172_, v___x_1174_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_nat_dec_le(v_b_1149_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v___x_1175_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
else
{
lean_dec(v_b_1149_);
v___y_1151_ = v___x_1175_;
goto v___jp_1150_;
}
}
}
case 5:
{
lean_object* v_view_1181_; lean_object* v_content_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_view_1181_ = lean_ctor_get(v_val_1158_, 0);
lean_inc_ref(v_view_1181_);
lean_dec_ref_known(v_val_1158_, 1);
v_content_1182_ = lean_ctor_get(v_view_1181_, 2);
lean_inc_ref(v_content_1182_);
lean_dec_ref(v_view_1181_);
v___x_1183_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1145_, v_content_1182_);
lean_dec_ref(v_content_1182_);
v___x_1184_ = lean_nat_dec_le(v_b_1149_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_dec(v___x_1183_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
else
{
lean_dec(v_b_1149_);
v___y_1151_ = v___x_1183_;
goto v___jp_1150_;
}
}
case 9:
{
lean_object* v_view_1185_; lean_object* v_content_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_view_1185_ = lean_ctor_get(v_val_1158_, 0);
lean_inc_ref(v_view_1185_);
lean_dec_ref_known(v_val_1158_, 1);
v_content_1186_ = lean_ctor_get(v_view_1185_, 6);
lean_inc_ref(v_content_1186_);
lean_dec_ref(v_view_1185_);
v___x_1187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1145_, v_content_1186_);
lean_dec_ref(v_content_1186_);
v___x_1188_ = lean_nat_dec_le(v_b_1149_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec(v___x_1187_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
else
{
lean_dec(v_b_1149_);
v___y_1151_ = v___x_1187_;
goto v___jp_1150_;
}
}
default: 
{
lean_dec(v_val_1158_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
}
}
else
{
lean_dec(v___x_1157_);
v___y_1151_ = v_b_1149_;
goto v___jp_1150_;
}
}
else
{
return v_b_1149_;
}
v___jp_1150_:
{
size_t v___x_1152_; size_t v___x_1153_; 
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_add(v_i_1147_, v___x_1152_);
v_i_1147_ = v___x_1153_;
v_b_1149_ = v___y_1151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1189_, lean_object* v_inls_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_array_get_size(v_inls_1190_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
return v___x_1191_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_nat_dec_le(v___x_1192_, v___x_1192_);
if (v___x_1194_ == 0)
{
if (v___x_1193_ == 0)
{
return v___x_1191_;
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_of_nat(v___x_1192_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1189_, v_inls_1190_, v___x_1195_, v___x_1196_, v___x_1191_);
return v___x_1197_;
}
}
else
{
size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = lean_usize_of_nat(v___x_1192_);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1189_, v_inls_1190_, v___x_1198_, v___x_1199_, v___x_1191_);
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1201_, lean_object* v_inls_1202_){
_start:
{
uint32_t v_char_boxed_1203_; lean_object* v_res_1204_; 
v_char_boxed_1203_ = lean_unbox_uint32(v_char_1201_);
lean_dec(v_char_1201_);
v_res_1204_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1203_, v_inls_1202_);
lean_dec_ref(v_inls_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1205_, lean_object* v_as_1206_, lean_object* v_i_1207_, lean_object* v_stop_1208_, lean_object* v_b_1209_){
_start:
{
uint32_t v_char_boxed_1210_; size_t v_i_boxed_1211_; size_t v_stop_boxed_1212_; lean_object* v_res_1213_; 
v_char_boxed_1210_ = lean_unbox_uint32(v_char_1205_);
lean_dec(v_char_1205_);
v_i_boxed_1211_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_stop_boxed_1212_ = lean_unbox_usize(v_stop_1208_);
lean_dec(v_stop_1208_);
v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1210_, v_as_1206_, v_i_boxed_1211_, v_stop_boxed_1212_, v_b_1209_);
lean_dec_ref(v_as_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1214_, lean_object* v_inls_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1214_, v_inls_1215_);
v___x_1218_ = lean_nat_add(v___x_1216_, v___x_1217_);
lean_dec(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1219_, lean_object* v_inls_1220_){
_start:
{
uint32_t v_char_boxed_1221_; lean_object* v_res_1222_; 
v_char_boxed_1221_ = lean_unbox_uint32(v_char_1219_);
lean_dec(v_char_1219_);
v_res_1222_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1221_, v_inls_1220_);
lean_dec_ref(v_inls_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1223_, size_t v_i_1224_, size_t v_stop_1225_, lean_object* v_b_1226_){
_start:
{
lean_object* v___y_1228_; uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_eq(v_i_1224_, v_stop_1225_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v_contents_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = lean_array_uget_borrowed(v_as_1223_, v_i_1224_);
v_contents_1234_ = lean_ctor_get(v___x_1233_, 2);
v___x_1235_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1234_);
v___x_1236_ = lean_nat_dec_le(v_b_1226_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v___x_1235_);
v___y_1228_ = v_b_1226_;
goto v___jp_1227_;
}
else
{
lean_dec(v_b_1226_);
v___y_1228_ = v___x_1235_;
goto v___jp_1227_;
}
}
else
{
return v_b_1226_;
}
v___jp_1227_:
{
size_t v___x_1229_; size_t v___x_1230_; 
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1224_, v___x_1229_);
v_i_1224_ = v___x_1230_;
v_b_1226_ = v___y_1228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1237_, size_t v_i_1238_, size_t v_stop_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v___y_1242_; uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_eq(v_i_1238_, v_stop_1239_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v_desc_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_array_uget_borrowed(v_as_1237_, v_i_1238_);
v_desc_1248_ = lean_ctor_get(v___x_1247_, 3);
v___x_1249_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1248_);
v___x_1250_ = lean_nat_dec_le(v_b_1240_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v___x_1249_);
v___y_1242_ = v_b_1240_;
goto v___jp_1241_;
}
else
{
lean_dec(v_b_1240_);
v___y_1242_ = v___x_1249_;
goto v___jp_1241_;
}
}
else
{
return v_b_1240_;
}
v___jp_1241_:
{
size_t v___x_1243_; size_t v___x_1244_; 
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1238_, v___x_1243_);
v_i_1238_ = v___x_1244_;
v_b_1240_ = v___y_1242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1251_, size_t v_i_1252_, size_t v_stop_1253_, lean_object* v_b_1254_){
_start:
{
lean_object* v___y_1256_; lean_object* v___y_1261_; uint8_t v___x_1265_; 
v___x_1265_ = lean_usize_dec_eq(v_i_1252_, v_stop_1253_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_array_uget_borrowed(v_as_1251_, v_i_1252_);
lean_inc(v___x_1266_);
v___x_1267_ = l_Lean_Doc_BlockView_of(v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 1)
{
lean_object* v_val_1268_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v___x_1267_, 1);
switch(lean_obj_tag(v_val_1268_))
{
case 6:
{
lean_object* v_view_1269_; lean_object* v_content_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_view_1269_ = lean_ctor_get(v_val_1268_, 0);
lean_inc_ref(v_view_1269_);
lean_dec_ref_known(v_val_1268_, 1);
v_content_1270_ = lean_ctor_get(v_view_1269_, 4);
lean_inc_ref(v_content_1270_);
lean_dec_ref(v_view_1269_);
v___x_1271_ = lean_unsigned_to_nat(3u);
v___x_1272_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1270_);
lean_dec_ref(v_content_1270_);
v___x_1273_ = lean_nat_dec_le(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec(v___x_1272_);
v___y_1261_ = v___x_1271_;
goto v___jp_1260_;
}
else
{
v___y_1261_ = v___x_1272_;
goto v___jp_1260_;
}
}
case 4:
{
lean_object* v_view_1274_; lean_object* v_content_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_view_1274_ = lean_ctor_get(v_val_1268_, 0);
lean_inc_ref(v_view_1274_);
lean_dec_ref_known(v_val_1268_, 1);
v_content_1275_ = lean_ctor_get(v_view_1274_, 2);
lean_inc_ref(v_content_1275_);
lean_dec_ref(v_view_1274_);
v___x_1276_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1275_);
lean_dec_ref(v_content_1275_);
v___x_1277_ = lean_nat_dec_le(v_b_1254_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v___x_1276_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
lean_dec(v_b_1254_);
v___y_1256_ = v___x_1276_;
goto v___jp_1255_;
}
}
case 1:
{
lean_object* v_view_1278_; lean_object* v_items_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_view_1278_ = lean_ctor_get(v_val_1268_, 0);
lean_inc_ref(v_view_1278_);
lean_dec_ref_known(v_val_1268_, 1);
v_items_1279_ = lean_ctor_get(v_view_1278_, 1);
lean_inc_ref(v_items_1279_);
lean_dec_ref(v_view_1278_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_size(v_items_1279_);
v___x_1282_ = lean_nat_dec_lt(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_items_1279_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_nat_dec_le(v___x_1281_, v___x_1281_);
if (v___x_1283_ == 0)
{
if (v___x_1282_ == 0)
{
lean_dec_ref(v_items_1279_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1281_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1279_, v___x_1284_, v___x_1285_, v_b_1254_);
lean_dec_ref(v_items_1279_);
v___y_1256_ = v___x_1286_;
goto v___jp_1255_;
}
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = lean_usize_of_nat(v___x_1281_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1279_, v___x_1287_, v___x_1288_, v_b_1254_);
lean_dec_ref(v_items_1279_);
v___y_1256_ = v___x_1289_;
goto v___jp_1255_;
}
}
}
case 2:
{
lean_object* v_view_1290_; lean_object* v_items_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_view_1290_ = lean_ctor_get(v_val_1268_, 0);
lean_inc_ref(v_view_1290_);
lean_dec_ref_known(v_val_1268_, 1);
v_items_1291_ = lean_ctor_get(v_view_1290_, 2);
lean_inc_ref(v_items_1291_);
lean_dec_ref(v_view_1290_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_array_get_size(v_items_1291_);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_items_1291_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_le(v___x_1293_, v___x_1293_);
if (v___x_1295_ == 0)
{
if (v___x_1294_ == 0)
{
lean_dec_ref(v_items_1291_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1293_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1291_, v___x_1296_, v___x_1297_, v_b_1254_);
lean_dec_ref(v_items_1291_);
v___y_1256_ = v___x_1298_;
goto v___jp_1255_;
}
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = lean_usize_of_nat(v___x_1293_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1291_, v___x_1299_, v___x_1300_, v_b_1254_);
lean_dec_ref(v_items_1291_);
v___y_1256_ = v___x_1301_;
goto v___jp_1255_;
}
}
}
case 3:
{
lean_object* v_view_1302_; lean_object* v_items_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_view_1302_ = lean_ctor_get(v_val_1268_, 0);
lean_inc_ref(v_view_1302_);
lean_dec_ref_known(v_val_1268_, 1);
v_items_1303_ = lean_ctor_get(v_view_1302_, 1);
lean_inc_ref(v_items_1303_);
lean_dec_ref(v_view_1302_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_array_get_size(v_items_1303_);
v___x_1306_ = lean_nat_dec_lt(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_items_1303_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_le(v___x_1305_, v___x_1305_);
if (v___x_1307_ == 0)
{
if (v___x_1306_ == 0)
{
lean_dec_ref(v_items_1303_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1305_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1303_, v___x_1308_, v___x_1309_, v_b_1254_);
lean_dec_ref(v_items_1303_);
v___y_1256_ = v___x_1310_;
goto v___jp_1255_;
}
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1305_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1303_, v___x_1311_, v___x_1312_, v_b_1254_);
lean_dec_ref(v_items_1303_);
v___y_1256_ = v___x_1313_;
goto v___jp_1255_;
}
}
}
default: 
{
lean_dec(v_val_1268_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
}
}
else
{
lean_dec(v___x_1267_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
}
else
{
return v_b_1254_;
}
v___jp_1255_:
{
size_t v___x_1257_; size_t v___x_1258_; 
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_add(v_i_1252_, v___x_1257_);
v_i_1252_ = v___x_1258_;
v_b_1254_ = v___y_1256_;
goto _start;
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v___y_1261_, v___x_1262_);
lean_dec(v___y_1261_);
v___x_1264_ = lean_nat_dec_le(v_b_1254_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec(v___x_1263_);
v___y_1256_ = v_b_1254_;
goto v___jp_1255_;
}
else
{
lean_dec(v_b_1254_);
v___y_1256_ = v___x_1263_;
goto v___jp_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_array_get_size(v_blks_1314_);
v___x_1317_ = lean_nat_dec_lt(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
return v___x_1315_;
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v___x_1316_, v___x_1316_);
if (v___x_1318_ == 0)
{
if (v___x_1317_ == 0)
{
return v___x_1315_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1316_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1314_, v___x_1319_, v___x_1320_, v___x_1315_);
return v___x_1321_;
}
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1316_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1314_, v___x_1322_, v___x_1323_, v___x_1315_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1325_, size_t v_i_1326_, size_t v_stop_1327_, lean_object* v_b_1328_){
_start:
{
lean_object* v___y_1330_; uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_eq(v_i_1326_, v_stop_1327_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v_contents_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1335_ = lean_array_uget_borrowed(v_as_1325_, v_i_1326_);
v_contents_1336_ = lean_ctor_get(v___x_1335_, 2);
v___x_1337_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1336_);
v___x_1338_ = lean_nat_dec_le(v_b_1328_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec(v___x_1337_);
v___y_1330_ = v_b_1328_;
goto v___jp_1329_;
}
else
{
lean_dec(v_b_1328_);
v___y_1330_ = v___x_1337_;
goto v___jp_1329_;
}
}
else
{
return v_b_1328_;
}
v___jp_1329_:
{
size_t v___x_1331_; size_t v___x_1332_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1326_, v___x_1331_);
v_i_1326_ = v___x_1332_;
v_b_1328_ = v___y_1330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1339_, lean_object* v_i_1340_, lean_object* v_stop_1341_, lean_object* v_b_1342_){
_start:
{
size_t v_i_boxed_1343_; size_t v_stop_boxed_1344_; lean_object* v_res_1345_; 
v_i_boxed_1343_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_stop_boxed_1344_ = lean_unbox_usize(v_stop_1341_);
lean_dec(v_stop_1341_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1339_, v_i_boxed_1343_, v_stop_boxed_1344_, v_b_1342_);
lean_dec_ref(v_as_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1346_, lean_object* v_i_1347_, lean_object* v_stop_1348_, lean_object* v_b_1349_){
_start:
{
size_t v_i_boxed_1350_; size_t v_stop_boxed_1351_; lean_object* v_res_1352_; 
v_i_boxed_1350_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_stop_boxed_1351_ = lean_unbox_usize(v_stop_1348_);
lean_dec(v_stop_1348_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1346_, v_i_boxed_1350_, v_stop_boxed_1351_, v_b_1349_);
lean_dec_ref(v_as_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1353_, lean_object* v_i_1354_, lean_object* v_stop_1355_, lean_object* v_b_1356_){
_start:
{
size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; lean_object* v_res_1359_; 
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1355_);
lean_dec(v_stop_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1353_, v_i_boxed_1357_, v_stop_boxed_1358_, v_b_1356_);
lean_dec_ref(v_as_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1360_);
lean_dec_ref(v_blks_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1362_, lean_object* v_i_1363_, lean_object* v_stop_1364_, lean_object* v_b_1365_){
_start:
{
size_t v_i_boxed_1366_; size_t v_stop_boxed_1367_; lean_object* v_res_1368_; 
v_i_boxed_1366_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_stop_boxed_1367_ = lean_unbox_usize(v_stop_1364_);
lean_dec(v_stop_1364_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1362_, v_i_boxed_1366_, v_stop_boxed_1367_, v_b_1365_);
lean_dec_ref(v_as_1362_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_unsigned_to_nat(3u);
v___x_1371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1369_);
v___x_1372_ = lean_nat_dec_le(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec(v___x_1371_);
return v___x_1370_;
}
else
{
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1373_);
lean_dec_ref(v_blks_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1375_){
_start:
{
lean_object* v___x_1376_; 
lean_inc(v_inl_1375_);
v___x_1376_ = l_Lean_Doc_LinebreakView_of(v_inl_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
uint8_t v___x_1377_; 
lean_dec_ref_known(v___x_1376_, 1);
lean_dec(v_inl_1375_);
v___x_1377_ = 1;
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
lean_dec(v___x_1376_);
v___x_1378_ = l_Lean_Doc_TextView_of(v_inl_1375_);
if (lean_obj_tag(v___x_1378_) == 1)
{
lean_object* v_val_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v_decide_1387_; 
v_val_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = 1;
v___x_1381_ = l_Lean_Doc_TextView_getVersoText(v_val_1379_);
lean_dec(v_val_1379_);
v___x_1382_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1380_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_string_utf8_byte_size(v___x_1382_);
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1382_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1385_, v___x_1383_);
lean_dec_ref_known(v___x_1385_, 3);
v_decide_1387_ = lean_nat_dec_eq(v___x_1386_, v___x_1384_);
lean_dec(v___x_1386_);
return v_decide_1387_;
}
else
{
uint8_t v___x_1388_; 
lean_dec(v___x_1378_);
v___x_1388_ = 0;
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Doc_BlockView_of(v_stx_1392_);
if (lean_obj_tag(v___x_1393_) == 1)
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1393_, 1);
switch(lean_obj_tag(v_val_1394_))
{
case 8:
{
uint8_t v___x_1395_; 
lean_dec_ref_known(v_val_1394_, 1);
v___x_1395_ = 1;
return v___x_1395_;
}
case 9:
{
uint8_t v___x_1396_; 
lean_dec_ref_known(v_val_1394_, 1);
v___x_1396_ = 1;
return v___x_1396_;
}
case 10:
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_val_1394_, 1);
v___x_1397_ = 1;
return v___x_1397_;
}
case 11:
{
uint8_t v___x_1398_; 
lean_dec_ref_known(v_val_1394_, 1);
v___x_1398_ = 1;
return v___x_1398_;
}
default: 
{
uint8_t v___x_1399_; 
lean_dec(v_val_1394_);
v___x_1399_ = 0;
return v___x_1399_;
}
}
}
else
{
uint8_t v___x_1400_; 
lean_dec(v___x_1393_);
v___x_1400_ = 0;
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1401_){
_start:
{
uint8_t v_res_1402_; lean_object* v_r_1403_; 
v_res_1402_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1401_);
v_r_1403_ = lean_box(v_res_1402_);
return v_r_1403_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1404_){
_start:
{
lean_object* v___x_1405_; 
lean_inc(v_inl_1404_);
v___x_1405_ = l_Lean_Doc_LinebreakView_of(v_inl_1404_);
if (lean_obj_tag(v___x_1405_) == 1)
{
uint8_t v___x_1406_; 
lean_dec_ref_known(v___x_1405_, 1);
lean_dec(v_inl_1404_);
v___x_1406_ = 1;
return v___x_1406_;
}
else
{
lean_object* v___x_1407_; 
lean_dec(v___x_1405_);
v___x_1407_ = l_Lean_Doc_TextView_of(v_inl_1404_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v_decide_1414_; 
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1408_);
lean_dec(v_val_1408_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_string_utf8_byte_size(v___x_1409_);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1411_);
v___x_1413_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1412_, v___x_1410_);
lean_dec_ref_known(v___x_1412_, 3);
v_decide_1414_ = lean_nat_dec_eq(v___x_1413_, v___x_1411_);
lean_dec(v___x_1413_);
return v_decide_1414_;
}
else
{
uint8_t v___x_1415_; 
lean_dec(v___x_1407_);
v___x_1415_ = 0;
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1416_){
_start:
{
uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_res_1417_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1416_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_array_uget_borrowed(v_as_1419_, v_i_1420_);
lean_inc(v___x_1423_);
v___x_1424_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1423_);
if (v___x_1424_ == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 1;
return v___x_1425_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; 
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1420_, v___x_1426_);
v_i_1420_ = v___x_1427_;
goto _start;
}
}
else
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1430_, lean_object* v_i_1431_, lean_object* v_stop_1432_){
_start:
{
size_t v_i_boxed_1433_; size_t v_stop_boxed_1434_; uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_i_boxed_1433_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_stop_boxed_1434_ = lean_unbox_usize(v_stop_1432_);
lean_dec(v_stop_1432_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1430_, v_i_boxed_1433_, v_stop_boxed_1434_);
lean_dec_ref(v_as_1430_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Doc_ParaView_of(v_stx_1437_);
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; lean_object* v_content_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v_content_1440_ = lean_ctor_get(v_val_1439_, 1);
lean_inc_ref(v_content_1440_);
lean_dec(v_val_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_array_get_size(v_content_1440_);
v___x_1443_ = lean_nat_dec_lt(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; 
lean_dec_ref(v_content_1440_);
v___x_1444_ = 1;
return v___x_1444_;
}
else
{
if (v___x_1443_ == 0)
{
lean_dec_ref(v_content_1440_);
return v___x_1443_;
}
else
{
size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1442_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1440_, v___x_1445_, v___x_1446_);
lean_dec_ref(v_content_1440_);
if (v___x_1447_ == 0)
{
return v___x_1443_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = 0;
return v___x_1448_;
}
}
}
}
else
{
uint8_t v___x_1449_; 
lean_dec(v___x_1438_);
v___x_1449_ = 0;
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Doc_LinebreakView_of(v_stx_1453_);
if (lean_obj_tag(v___x_1454_) == 1)
{
uint8_t v___x_1455_; 
lean_dec_ref_known(v___x_1454_, 1);
v___x_1455_ = 1;
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
lean_dec(v___x_1454_);
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1457_){
_start:
{
uint8_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1457_);
v_r_1459_ = lean_box(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_array_get_size(v_inls_1460_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_box(0);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; lean_object* v_inl_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v_inl_1466_ = lean_array_fget_borrowed(v_inls_1460_, v___x_1465_);
lean_inc(v_inl_1466_);
v___x_1467_ = l_Lean_Doc_InlineView_of(v_inl_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_box(0);
return v___x_1468_;
}
else
{
lean_object* v_val_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1480_; 
v_val_1469_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_val_1469_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
switch(lean_obj_tag(v_val_1469_))
{
case 0:
{
lean_object* v___x_1473_; 
lean_dec_ref_known(v_val_1469_, 1);
lean_del_object(v___x_1471_);
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
case 5:
{
lean_object* v___x_1474_; 
lean_dec_ref_known(v_val_1469_, 1);
lean_del_object(v___x_1471_);
v___x_1474_ = lean_box(0);
return v___x_1474_;
}
case 7:
{
lean_object* v___x_1475_; 
lean_dec_ref_known(v_val_1469_, 1);
lean_del_object(v___x_1471_);
v___x_1475_ = lean_box(0);
return v___x_1475_;
}
case 8:
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v_val_1469_, 1);
lean_del_object(v___x_1471_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
default: 
{
lean_object* v___x_1478_; 
lean_dec(v_val_1469_);
lean_inc(v_inl_1466_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_inl_1466_);
v___x_1478_ = v___x_1471_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_inl_1466_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1481_);
lean_dec_ref(v_inls_1481_);
return v_res_1482_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = 41;
v___x_1484_ = lean_box_uint32(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = 93;
v___x_1488_ = lean_box_uint32(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1491_){
_start:
{
if (lean_obj_tag(v_a_1491_) == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1494_);
lean_dec_ref(v_a_1494_);
return v_res_1495_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = 95;
v___x_1497_ = lean_box_uint32(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = 42;
v___x_1501_ = lean_box_uint32(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = 96;
v___x_1505_ = lean_box_uint32(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Doc_InlineView_of(v_inl_1508_);
if (lean_obj_tag(v___x_1509_) == 1)
{
lean_object* v_val_1510_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v___x_1509_, 1);
switch(lean_obj_tag(v_val_1510_))
{
case 1:
{
lean_object* v___x_1511_; 
lean_dec_ref_known(v_val_1510_, 1);
v___x_1511_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1511_;
}
case 2:
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v_val_1510_, 1);
v___x_1512_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1512_;
}
case 3:
{
lean_object* v___x_1513_; 
lean_dec_ref_known(v_val_1510_, 1);
v___x_1513_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1513_;
}
case 4:
{
lean_object* v___x_1514_; 
lean_dec_ref_known(v_val_1510_, 1);
v___x_1514_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1514_;
}
case 5:
{
lean_object* v_view_1515_; lean_object* v_target_1516_; lean_object* v___x_1517_; 
v_view_1515_ = lean_ctor_get(v_val_1510_, 0);
lean_inc_ref(v_view_1515_);
lean_dec_ref_known(v_val_1510_, 1);
v_target_1516_ = lean_ctor_get(v_view_1515_, 4);
lean_inc_ref(v_target_1516_);
lean_dec_ref(v_view_1515_);
v___x_1517_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1516_);
lean_dec_ref(v_target_1516_);
return v___x_1517_;
}
case 6:
{
lean_object* v_view_1518_; lean_object* v_target_1519_; lean_object* v___x_1520_; 
v_view_1518_ = lean_ctor_get(v_val_1510_, 0);
lean_inc_ref(v_view_1518_);
lean_dec_ref_known(v_val_1510_, 1);
v_target_1519_ = lean_ctor_get(v_view_1518_, 4);
lean_inc_ref(v_target_1519_);
lean_dec_ref(v_view_1518_);
v___x_1520_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1519_);
lean_dec_ref(v_target_1519_);
return v___x_1520_;
}
case 7:
{
lean_object* v___x_1521_; 
lean_dec_ref_known(v_val_1510_, 1);
v___x_1521_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1521_;
}
case 9:
{
lean_object* v_view_1522_; lean_object* v_content_1523_; lean_object* v___x_1524_; 
v_view_1522_ = lean_ctor_get(v_val_1510_, 0);
lean_inc_ref(v_view_1522_);
lean_dec_ref_known(v_val_1510_, 1);
v_content_1523_ = lean_ctor_get(v_view_1522_, 6);
lean_inc_ref(v_content_1523_);
lean_dec_ref(v_view_1522_);
v___x_1524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1523_);
lean_dec_ref(v_content_1523_);
if (lean_obj_tag(v___x_1524_) == 1)
{
lean_object* v_val_1525_; 
v_val_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_inl_1508_ = v_val_1525_;
goto _start;
}
else
{
lean_object* v___x_1527_; 
lean_dec(v___x_1524_);
v___x_1527_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1527_;
}
}
default: 
{
lean_object* v___x_1528_; 
lean_dec(v_val_1510_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
}
}
else
{
lean_object* v___x_1529_; 
lean_dec(v___x_1509_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = 36;
v___x_1531_ = lean_box_uint32(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Doc_InlineView_of(v_stx_1534_);
if (lean_obj_tag(v___x_1535_) == 1)
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1535_, 1);
switch(lean_obj_tag(v_val_1536_))
{
case 1:
{
lean_object* v___x_1537_; 
lean_dec_ref_known(v_val_1536_, 1);
v___x_1537_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1537_;
}
case 2:
{
lean_object* v___x_1538_; 
lean_dec_ref_known(v_val_1536_, 1);
v___x_1538_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1538_;
}
case 3:
{
lean_object* v___x_1539_; 
lean_dec_ref_known(v_val_1536_, 1);
v___x_1539_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1539_;
}
case 4:
{
lean_object* v___x_1540_; 
lean_dec_ref_known(v_val_1536_, 1);
v___x_1540_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1540_;
}
default: 
{
lean_object* v___x_1541_; 
lean_dec(v_val_1536_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v___x_1535_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1543_, lean_object* v_next_x3f_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1543_);
if (lean_obj_tag(v___x_1545_) == 1)
{
if (lean_obj_tag(v_next_x3f_1544_) == 0)
{
uint8_t v___x_1546_; 
lean_dec_ref_known(v___x_1545_, 1);
v___x_1546_ = 0;
return v___x_1546_;
}
else
{
lean_object* v_val_1547_; lean_object* v_val_1548_; lean_object* v___x_1549_; 
v_val_1547_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v___x_1545_, 1);
v_val_1548_ = lean_ctor_get(v_next_x3f_1544_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_next_x3f_1544_, 1);
v___x_1549_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1548_);
if (lean_obj_tag(v___x_1549_) == 1)
{
lean_object* v_val_1550_; uint32_t v___x_1551_; uint32_t v___x_1552_; uint8_t v___x_1553_; 
v_val_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_unbox_uint32(v_val_1547_);
lean_dec(v_val_1547_);
v___x_1552_ = lean_unbox_uint32(v_val_1550_);
lean_dec(v_val_1550_);
v___x_1553_ = lean_uint32_dec_eq(v___x_1551_, v___x_1552_);
return v___x_1553_;
}
else
{
uint8_t v___x_1554_; 
lean_dec(v___x_1549_);
lean_dec(v_val_1547_);
v___x_1554_ = 0;
return v___x_1554_;
}
}
}
else
{
uint8_t v___x_1555_; 
lean_dec(v___x_1545_);
lean_dec(v_next_x3f_1544_);
v___x_1555_ = 0;
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1556_, lean_object* v_next_x3f_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1556_, v_next_x3f_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1560_, lean_object* v_next_x3f_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1560_);
if (lean_obj_tag(v___x_1562_) == 1)
{
lean_object* v_val_1563_; uint32_t v___x_1564_; uint32_t v___x_1565_; uint8_t v___x_1566_; 
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = 96;
v___x_1565_ = lean_unbox_uint32(v_val_1563_);
lean_dec(v_val_1563_);
v___x_1566_ = lean_uint32_dec_eq(v___x_1565_, v___x_1564_);
if (v___x_1566_ == 0)
{
lean_dec(v_next_x3f_1561_);
return v___x_1566_;
}
else
{
if (lean_obj_tag(v_next_x3f_1561_) == 0)
{
uint8_t v___x_1567_; 
v___x_1567_ = 0;
return v___x_1567_;
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1569_; 
v_val_1568_ = lean_ctor_get(v_next_x3f_1561_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v_next_x3f_1561_, 1);
v___x_1569_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1568_);
if (lean_obj_tag(v___x_1569_) == 1)
{
lean_object* v_val_1570_; uint32_t v___x_1571_; uint8_t v___x_1572_; 
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_unbox_uint32(v_val_1570_);
lean_dec(v_val_1570_);
v___x_1572_ = lean_uint32_dec_eq(v___x_1571_, v___x_1564_);
return v___x_1572_;
}
else
{
uint8_t v___x_1573_; 
lean_dec(v___x_1569_);
v___x_1573_ = 0;
return v___x_1573_;
}
}
}
}
else
{
uint8_t v___x_1574_; 
lean_dec(v___x_1562_);
lean_dec(v_next_x3f_1561_);
v___x_1574_ = 0;
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1575_, lean_object* v_next_x3f_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1575_, v_next_x3f_1576_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = lean_array_get_size(v_inls_1579_);
v___x_1582_ = lean_nat_dec_lt(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_array_fget_borrowed(v_inls_1579_, v___x_1580_);
lean_inc(v___x_1583_);
v___x_1584_ = l_Lean_Doc_TextView_of(v___x_1583_);
if (lean_obj_tag(v___x_1584_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_val_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l_Lean_Doc_TextView_getVersoText(v_val_1585_);
lean_dec(v_val_1585_);
v___x_1587_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_1588_ = lean_string_utf8_byte_size(v___x_1586_);
v___x_1589_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23);
v___x_1590_ = lean_nat_dec_le(v___x_1589_, v___x_1588_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v___x_1586_);
return v___x_1590_;
}
else
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_string_memcmp(v___x_1586_, v___x_1587_, v___x_1580_, v___x_1580_, v___x_1589_);
lean_dec_ref(v___x_1586_);
return v___x_1591_;
}
}
else
{
uint8_t v___x_1592_; 
lean_dec(v___x_1584_);
v___x_1592_ = 0;
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1593_);
lean_dec_ref(v_inls_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1599_, lean_object* v_a_1600_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
lean_object* v_url_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_snd_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_snd_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_url_1601_ = lean_ctor_get(v_x_1599_, 2);
v___x_1602_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1603_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1602_, v_a_1600_);
v_snd_1604_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_snd_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1601_);
v___x_1606_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1605_);
v___x_1607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1606_, v_snd_1604_);
lean_dec_ref(v___x_1606_);
v_snd_1608_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1608_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1609_, v_snd_1608_);
return v___x_1610_;
}
else
{
lean_object* v_name_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_snd_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_name_1611_ = lean_ctor_get(v_x_1599_, 2);
v___x_1612_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1613_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1612_, v_a_1600_);
v_snd_1614_ = lean_ctor_get(v___x_1613_, 1);
lean_inc(v_snd_1614_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = l_Lean_TSyntax_getVersoRefName(v_name_1611_);
v___x_1616_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1615_, v_snd_1614_);
lean_dec_ref(v___x_1615_);
v_snd_1617_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1619_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1618_, v_snd_1617_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1620_, v_a_1621_);
lean_dec_ref(v_x_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1623_, v_a_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_x_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1631_, lean_object* v_pos_1632_){
_start:
{
lean_object* v_str_1633_; lean_object* v_startInclusive_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v_decide_1638_; 
v_str_1633_ = lean_ctor_get(v_s_1631_, 0);
v_startInclusive_1634_ = lean_ctor_get(v_s_1631_, 1);
v___x_1635_ = lean_nat_add(v_startInclusive_1634_, v_pos_1632_);
v___x_1636_ = lean_nat_sub(v___x_1635_, v_startInclusive_1634_);
v___x_1637_ = lean_unsigned_to_nat(0u);
v_decide_1638_ = lean_nat_dec_eq(v___x_1636_, v___x_1637_);
if (v_decide_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint32_t v___x_1644_; uint32_t v___x_1645_; uint8_t v___x_1646_; 
lean_inc(v_startInclusive_1634_);
lean_inc_ref(v_str_1633_);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_str_1633_);
lean_ctor_set(v___x_1639_, 1, v_startInclusive_1634_);
lean_ctor_set(v___x_1639_, 2, v___x_1635_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_nat_sub(v___x_1636_, v___x_1640_);
lean_dec(v___x_1636_);
v___x_1642_ = l_String_Slice_posLE(v___x_1639_, v___x_1641_);
lean_dec_ref_known(v___x_1639_, 3);
v___x_1643_ = lean_nat_add(v_startInclusive_1634_, v___x_1642_);
v___x_1644_ = lean_string_utf8_get_fast(v_str_1633_, v___x_1643_);
lean_dec(v___x_1643_);
v___x_1645_ = 32;
v___x_1646_ = lean_uint32_dec_eq(v___x_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_dec(v___x_1642_);
return v_pos_1632_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = lean_nat_add(v___x_1642_, v___x_1640_);
v___x_1648_ = lean_nat_dec_le(v___x_1647_, v_pos_1632_);
lean_dec(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec(v___x_1642_);
return v_pos_1632_;
}
else
{
lean_dec(v_pos_1632_);
v_pos_1632_ = v___x_1642_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1636_);
lean_dec(v___x_1635_);
return v_pos_1632_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1650_, lean_object* v_pos_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1650_, v_pos_1651_);
lean_dec_ref(v_s_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1653_, lean_object* v_contents_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_alone_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_string_utf8_byte_size(v_marker_1653_);
lean_inc_ref(v_marker_1653_);
v___x_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1658_, 0, v_marker_1653_);
lean_ctor_set(v___x_1658_, 1, v___x_1656_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
v___x_1659_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1658_, v___x_1657_);
lean_dec_ref_known(v___x_1658_, 3);
v_alone_1660_ = lean_string_utf8_extract_fast(v_marker_1653_, v___x_1656_, v___x_1659_);
lean_dec(v___x_1659_);
v___x_1661_ = lean_array_get_size(v_contents_1654_);
v___x_1662_ = lean_nat_dec_lt(v___x_1656_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v_marker_1653_);
v___x_1663_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1660_, v_a_1655_);
lean_dec_ref(v_alone_1660_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_array_fget_borrowed(v_contents_1654_, v___x_1656_);
lean_inc(v___x_1664_);
v___x_1665_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref(v_alone_1660_);
v___x_1666_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1653_, v_a_1655_);
lean_dec_ref(v_marker_1653_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_marker_1653_);
v___x_1667_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1668_ = lean_string_append(v_alone_1660_, v___x_1667_);
v___x_1669_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1668_, v_a_1655_);
lean_dec_ref(v___x_1668_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1670_, lean_object* v_contents_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1670_, v_contents_1671_, v_a_1672_);
lean_dec_ref(v_contents_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1674_, lean_object* v_contents_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1674_, v_contents_1675_, v_a_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1679_, lean_object* v_contents_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1679_, v_contents_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_contents_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1684_, size_t v_i_1685_, size_t v_stop_1686_, lean_object* v_b_1687_){
_start:
{
lean_object* v___y_1689_; uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_eq(v_i_1685_, v_stop_1686_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = lean_array_uget_borrowed(v_as_1684_, v_i_1685_);
lean_inc(v___x_1694_);
v___x_1695_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
lean_inc(v___x_1694_);
v___x_1696_ = lean_array_push(v_b_1687_, v___x_1694_);
v___y_1689_ = v___x_1696_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v_b_1687_;
goto v___jp_1688_;
}
}
else
{
return v_b_1687_;
}
v___jp_1688_:
{
size_t v___x_1690_; size_t v___x_1691_; 
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_i_1685_, v___x_1690_);
v_i_1685_ = v___x_1691_;
v_b_1687_ = v___y_1689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v_stop_1699_, lean_object* v_b_1700_){
_start:
{
size_t v_i_boxed_1701_; size_t v_stop_boxed_1702_; lean_object* v_res_1703_; 
v_i_boxed_1701_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_stop_boxed_1702_ = lean_unbox_usize(v_stop_1699_);
lean_dec(v_stop_1699_);
v_res_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1697_, v_i_boxed_1701_, v_stop_boxed_1702_, v_b_1700_);
lean_dec_ref(v_as_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_bs_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1707_ == 0)
{
return v_bs_1706_;
}
else
{
lean_object* v_v_1708_; lean_object* v___x_1709_; lean_object* v_bs_x27_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_v_1708_ = lean_array_uget(v_bs_1706_, v_i_1705_);
v___x_1709_ = lean_unsigned_to_nat(0u);
v_bs_x27_1710_ = lean_array_uset(v_bs_1706_, v_i_1705_, v___x_1709_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1705_, v___x_1711_);
v___x_1713_ = lean_array_uset(v_bs_x27_1710_, v_i_1705_, v_v_1708_);
v_i_1705_ = v___x_1712_;
v_bs_1706_ = v___x_1713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_zero_1723_; uint8_t v_isZero_1724_; 
v_zero_1723_ = lean_unsigned_to_nat(0u);
v_isZero_1724_ = lean_nat_dec_eq(v_x_1721_, v_zero_1723_);
if (v_isZero_1724_ == 1)
{
lean_dec(v_x_1721_);
return v_x_1722_;
}
else
{
uint32_t v___x_1725_; lean_object* v_one_1726_; lean_object* v_n_1727_; lean_object* v___x_1728_; 
v___x_1725_ = 35;
v_one_1726_ = lean_unsigned_to_nat(1u);
v_n_1727_ = lean_nat_sub(v_x_1721_, v_one_1726_);
lean_dec(v_x_1721_);
v___x_1728_ = lean_string_push(v_x_1722_, v___x_1725_);
v_x_1721_ = v_n_1727_;
v_x_1722_ = v___x_1728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
lean_object* v_zero_1732_; uint8_t v_isZero_1733_; 
v_zero_1732_ = lean_unsigned_to_nat(0u);
v_isZero_1733_ = lean_nat_dec_eq(v_x_1730_, v_zero_1732_);
if (v_isZero_1733_ == 1)
{
lean_dec(v_x_1730_);
return v_x_1731_;
}
else
{
uint32_t v___x_1734_; lean_object* v_one_1735_; lean_object* v_n_1736_; lean_object* v___x_1737_; 
v___x_1734_ = 58;
v_one_1735_ = lean_unsigned_to_nat(1u);
v_n_1736_ = lean_nat_sub(v_x_1730_, v_one_1735_);
lean_dec(v_x_1730_);
v___x_1737_ = lean_string_push(v_x_1731_, v___x_1734_);
v_x_1730_ = v_n_1736_;
v_x_1731_ = v___x_1737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_zero_1742_; uint8_t v_isZero_1743_; 
v_zero_1742_ = lean_unsigned_to_nat(0u);
v_isZero_1743_ = lean_nat_dec_eq(v_x_1740_, v_zero_1742_);
if (v_isZero_1743_ == 1)
{
lean_dec(v_x_1740_);
return v_x_1741_;
}
else
{
lean_object* v_one_1744_; lean_object* v_n_1745_; lean_object* v___x_1746_; 
v_one_1744_ = lean_unsigned_to_nat(1u);
v_n_1745_ = lean_nat_sub(v_x_1740_, v_one_1744_);
lean_dec(v_x_1740_);
v___x_1746_ = lean_string_push(v_x_1741_, v_char_1739_);
v_x_1740_ = v_n_1745_;
v_x_1741_ = v___x_1746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
uint32_t v_char_boxed_1751_; lean_object* v_res_1752_; 
v_char_boxed_1751_ = lean_unbox_uint32(v_char_1748_);
lean_dec(v_char_1748_);
v_res_1752_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1751_, v_x_1749_, v_x_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
if (lean_obj_tag(v_x_1754_) == 0)
{
uint8_t v___x_1755_; 
v___x_1755_ = 1;
return v___x_1755_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = 0;
return v___x_1756_;
}
}
else
{
if (lean_obj_tag(v_x_1754_) == 0)
{
uint8_t v___x_1757_; 
v___x_1757_ = 0;
return v___x_1757_;
}
else
{
lean_object* v_val_1758_; lean_object* v_val_1759_; uint32_t v___x_1760_; uint32_t v___x_1761_; uint8_t v___x_1762_; 
v_val_1758_ = lean_ctor_get(v_x_1753_, 0);
v_val_1759_ = lean_ctor_get(v_x_1754_, 0);
v___x_1760_ = lean_unbox_uint32(v_val_1758_);
v___x_1761_ = lean_unbox_uint32(v_val_1759_);
v___x_1762_ = lean_uint32_dec_eq(v___x_1760_, v___x_1761_);
return v___x_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1763_, v_x_1764_);
lean_dec(v_x_1764_);
lean_dec(v_x_1763_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___closed__0));
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_1771_);
lean_dec_ref(v_s_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1773_, lean_object* v_as_1774_, size_t v_i_1775_, size_t v_stop_1776_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_eq(v_i_1775_, v_stop_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1778_ = 1;
v___x_1779_ = lean_array_uget_borrowed(v_as_1774_, v_i_1775_);
lean_inc(v___x_1779_);
v___x_1780_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1779_);
if (v___x_1780_ == 0)
{
return v___x_1778_;
}
else
{
if (v___x_1773_ == 0)
{
size_t v___x_1781_; size_t v___x_1782_; 
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_add(v_i_1775_, v___x_1781_);
v_i_1775_ = v___x_1782_;
goto _start;
}
else
{
return v___x_1778_;
}
}
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = 0;
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1785_, lean_object* v_as_1786_, lean_object* v_i_1787_, lean_object* v_stop_1788_){
_start:
{
uint8_t v___x_60175__boxed_1789_; size_t v_i_boxed_1790_; size_t v_stop_boxed_1791_; uint8_t v_res_1792_; lean_object* v_r_1793_; 
v___x_60175__boxed_1789_ = lean_unbox(v___x_1785_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_stop_boxed_1791_ = lean_unbox_usize(v_stop_1788_);
lean_dec(v_stop_1788_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_60175__boxed_1789_, v_as_1786_, v_i_boxed_1790_, v_stop_boxed_1791_);
lean_dec_ref(v_as_1786_);
v_r_1793_ = lean_box(v_res_1792_);
return v_r_1793_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1794_, uint8_t v___x_1795_, lean_object* v_as_1796_, size_t v_i_1797_, size_t v_stop_1798_){
_start:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_usize_dec_eq(v_i_1797_, v_stop_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; uint8_t v___y_1802_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1800_ = 1;
v___x_1806_ = lean_array_uget_borrowed(v_as_1796_, v_i_1797_);
lean_inc(v___x_1806_);
v___x_1807_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1806_);
if (v___x_1807_ == 0)
{
v___y_1802_ = v___x_1794_;
goto v___jp_1801_;
}
else
{
v___y_1802_ = v___x_1795_;
goto v___jp_1801_;
}
v___jp_1801_:
{
if (v___y_1802_ == 0)
{
size_t v___x_1803_; size_t v___x_1804_; 
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1797_, v___x_1803_);
v_i_1797_ = v___x_1804_;
goto _start;
}
else
{
return v___x_1800_;
}
}
}
else
{
uint8_t v___x_1808_; 
v___x_1808_ = 0;
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1809_, lean_object* v___x_1810_, lean_object* v_as_1811_, lean_object* v_i_1812_, lean_object* v_stop_1813_){
_start:
{
uint8_t v___x_60194__boxed_1814_; uint8_t v___x_60195__boxed_1815_; size_t v_i_boxed_1816_; size_t v_stop_boxed_1817_; uint8_t v_res_1818_; lean_object* v_r_1819_; 
v___x_60194__boxed_1814_ = lean_unbox(v___x_1809_);
v___x_60195__boxed_1815_ = lean_unbox(v___x_1810_);
v_i_boxed_1816_ = lean_unbox_usize(v_i_1812_);
lean_dec(v_i_1812_);
v_stop_boxed_1817_ = lean_unbox_usize(v_stop_1813_);
lean_dec(v_stop_1813_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_60194__boxed_1814_, v___x_60195__boxed_1815_, v_as_1811_, v_i_boxed_1816_, v_stop_boxed_1817_);
lean_dec_ref(v_as_1811_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___x_1822_, lean_object* v___x_1823_, lean_object* v_a_1824_, lean_object* v_b_1825_){
_start:
{
if (lean_obj_tag(v_a_1824_) == 0)
{
lean_object* v_currPos_1826_; lean_object* v_searcher_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1860_; 
v_currPos_1826_ = lean_ctor_get(v_a_1824_, 0);
v_searcher_1827_ = lean_ctor_get(v_a_1824_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_a_1824_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1829_ = v_a_1824_;
v_isShared_1830_ = v_isSharedCheck_1860_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_searcher_1827_);
lean_inc(v_currPos_1826_);
lean_dec(v_a_1824_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1860_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v_it_1833_; lean_object* v_startInclusive_1834_; lean_object* v_endExclusive_1835_; uint8_t v_decide_1841_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_decide_1841_ = lean_nat_dec_eq(v_searcher_1827_, v___x_1823_);
if (v_decide_1841_ == 0)
{
uint32_t v___x_1842_; uint32_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = 10;
v___x_1843_ = lean_string_utf8_get_fast(v___y_1821_, v_searcher_1827_);
v___x_1844_ = lean_uint32_dec_eq(v___x_1843_, v___x_1842_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = lean_string_utf8_next_fast(v___y_1821_, v_searcher_1827_);
lean_dec(v_searcher_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1845_);
v___x_1847_ = v___x_1829_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_currPos_1826_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v_a_1824_ = v___x_1847_;
goto _start;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_slice_1853_; lean_object* v_nextIt_1855_; 
v___x_1850_ = lean_string_utf8_next_fast(v___y_1821_, v_searcher_1827_);
v___x_1851_ = lean_nat_sub(v___x_1850_, v_searcher_1827_);
v___x_1852_ = lean_nat_add(v_searcher_1827_, v___x_1851_);
lean_dec(v___x_1851_);
v_slice_1853_ = l_String_Slice_subslice_x21(v___x_1822_, v_currPos_1826_, v_searcher_1827_);
lean_inc(v___x_1852_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1852_);
lean_ctor_set(v___x_1829_, 0, v___x_1852_);
v_nextIt_1855_ = v___x_1829_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1852_);
v_nextIt_1855_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v_startInclusive_1856_; lean_object* v_endExclusive_1857_; 
v_startInclusive_1856_ = lean_ctor_get(v_slice_1853_, 0);
lean_inc(v_startInclusive_1856_);
v_endExclusive_1857_ = lean_ctor_get(v_slice_1853_, 1);
lean_inc(v_endExclusive_1857_);
lean_dec_ref(v_slice_1853_);
v_it_1833_ = v_nextIt_1855_;
v_startInclusive_1834_ = v_startInclusive_1856_;
v_endExclusive_1835_ = v_endExclusive_1857_;
goto v___jp_1832_;
}
}
}
else
{
lean_object* v___x_1859_; 
lean_del_object(v___x_1829_);
lean_dec(v_searcher_1827_);
v___x_1859_ = lean_box(1);
lean_inc(v___x_1823_);
v_it_1833_ = v___x_1859_;
v_startInclusive_1834_ = v_currPos_1826_;
v_endExclusive_1835_ = v___x_1823_;
goto v___jp_1832_;
}
v___jp_1832_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc(v___y_1820_);
v___x_1836_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1820_, v___x_1831_);
v___x_1837_ = lean_string_utf8_extract_fast(v___y_1821_, v_startInclusive_1834_, v_endExclusive_1835_);
lean_dec(v_endExclusive_1835_);
lean_dec(v_startInclusive_1834_);
v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_array_push(v_b_1825_, v___x_1838_);
v_a_1824_ = v_it_1833_;
v_b_1825_ = v___x_1839_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1823_);
return v_b_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___x_1863_, lean_object* v___x_1864_, lean_object* v_a_1865_, lean_object* v_b_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1861_, v___y_1862_, v___x_1863_, v___x_1864_, v_a_1865_, v_b_1866_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1868_, lean_object* v___x_1869_, lean_object* v_____r_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1873_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1868_);
v___x_1874_ = lean_box(v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1869_);
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___y_1872_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1878_, lean_object* v___x_1879_, lean_object* v_____r_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1878_, v___x_1879_, v_____r_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1890_, lean_object* v___y_1891_, lean_object* v_a_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___y_1897_; uint8_t v___x_1914_; 
v___x_1914_ = lean_nat_dec_lt(v_a_1892_, v_upperBound_1890_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec(v_a_1892_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1893_);
lean_ctor_set(v___x_1915_, 1, v___y_1895_);
return v___x_1915_;
}
else
{
lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___y_1921_; lean_object* v___y_1925_; uint8_t v___y_1926_; lean_object* v___y_1941_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_fst_1916_ = lean_ctor_get(v_b_1893_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v_b_1893_, 1);
lean_inc(v_snd_1917_);
lean_dec_ref(v_b_1893_);
v___x_1918_ = lean_array_fget_borrowed(v___y_1891_, v_a_1892_);
lean_inc(v___x_1918_);
v___x_1919_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1917_, v___x_1918_);
lean_dec(v_snd_1917_);
v___x_1945_ = lean_unsigned_to_nat(1u);
v___x_1946_ = lean_nat_add(v_a_1892_, v___x_1945_);
v___x_1947_ = lean_array_get_size(v___y_1891_);
v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v___y_1941_ = v___x_1949_;
goto v___jp_1940_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_array_fget_borrowed(v___y_1891_, v___x_1946_);
lean_dec(v___x_1946_);
lean_inc(v___x_1950_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
v___y_1941_ = v___x_1951_;
goto v___jp_1940_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_box(0);
lean_inc(v___x_1918_);
v___x_1923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1918_, v___x_1919_, v___x_1922_, v___y_1894_, v___y_1921_);
v___y_1897_ = v___x_1923_;
goto v___jp_1896_;
}
v___jp_1924_:
{
uint8_t v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_unbox(v_fst_1916_);
lean_dec(v_fst_1916_);
lean_inc(v___y_1925_);
lean_inc(v___x_1918_);
v___x_1928_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1918_, v___y_1925_, v___x_1927_, v___y_1926_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___y_1925_) == 1)
{
lean_object* v_snd_1929_; lean_object* v___x_1930_; 
v_snd_1929_ = lean_ctor_get(v___x_1928_, 1);
lean_inc(v_snd_1929_);
lean_dec_ref(v___x_1928_);
lean_inc(v___x_1918_);
v___x_1930_ = l_Lean_Doc_RoleView_of(v___x_1918_);
if (lean_obj_tag(v___x_1930_) == 1)
{
lean_dec_ref_known(v___x_1930_, 1);
lean_dec_ref_known(v___y_1925_, 1);
v___y_1921_ = v_snd_1929_;
goto v___jp_1920_;
}
else
{
uint8_t v___x_1931_; 
lean_dec(v___x_1930_);
lean_inc(v___x_1918_);
v___x_1931_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1918_, v___y_1925_);
if (v___x_1931_ == 0)
{
v___y_1921_ = v_snd_1929_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1936_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1933_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1932_, v_snd_1929_);
v_fst_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_fst_1934_);
v_snd_1935_ = lean_ctor_get(v___x_1933_, 1);
lean_inc(v_snd_1935_);
lean_dec_ref(v___x_1933_);
lean_inc(v___x_1918_);
v___x_1936_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1918_, v___x_1919_, v_fst_1934_, v___y_1894_, v_snd_1935_);
v___y_1897_ = v___x_1936_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v_snd_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v___y_1925_);
v_snd_1937_ = lean_ctor_get(v___x_1928_, 1);
lean_inc(v_snd_1937_);
lean_dec_ref(v___x_1928_);
v___x_1938_ = lean_box(0);
lean_inc(v___x_1918_);
v___x_1939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1918_, v___x_1919_, v___x_1938_, v___y_1894_, v_snd_1937_);
v___y_1897_ = v___x_1939_;
goto v___jp_1896_;
}
}
v___jp_1940_:
{
if (lean_obj_tag(v___x_1919_) == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = 0;
v___y_1925_ = v___y_1941_;
v___y_1926_ = v___x_1942_;
goto v___jp_1924_;
}
else
{
lean_object* v_val_1943_; uint8_t v_alternate_1944_; 
v_val_1943_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_val_1943_);
v_alternate_1944_ = lean_ctor_get_uint8(v_val_1943_, 1);
lean_dec(v_val_1943_);
v___y_1925_ = v___y_1941_;
v___y_1926_ = v_alternate_1944_;
goto v___jp_1924_;
}
}
}
v___jp_1896_:
{
lean_object* v_fst_1898_; 
v_fst_1898_ = lean_ctor_get(v___y_1897_, 0);
lean_inc(v_fst_1898_);
if (lean_obj_tag(v_fst_1898_) == 0)
{
lean_object* v_snd_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_a_1892_);
v_snd_1899_ = lean_ctor_get(v___y_1897_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___y_1897_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___y_1897_, 0);
lean_dec(v_unused_1908_);
v___x_1901_ = v___y_1897_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snd_1899_);
lean_dec(v___y_1897_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_a_1903_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v_fst_1898_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v_fst_1898_, 1);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_a_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1903_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_snd_1899_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_snd_1909_; lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_snd_1909_ = lean_ctor_get(v___y_1897_, 1);
lean_inc(v_snd_1909_);
lean_dec_ref(v___y_1897_);
v_a_1910_ = lean_ctor_get(v_fst_1898_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v_fst_1898_, 1);
v___x_1911_ = lean_unsigned_to_nat(1u);
v___x_1912_ = lean_nat_add(v_a_1892_, v___x_1911_);
lean_dec(v_a_1892_);
v_a_1892_ = v___x_1912_;
v_b_1893_ = v_a_1910_;
v___y_1895_ = v_snd_1909_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1954_, uint8_t v_lineStart_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___y_1960_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_array_get_size(v_stxs_1954_);
v___x_1977_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1978_ = lean_nat_dec_lt(v___x_1958_, v___x_1976_);
if (v___x_1978_ == 0)
{
v___y_1960_ = v___x_1977_;
goto v___jp_1959_;
}
else
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_le(v___x_1976_, v___x_1976_);
if (v___x_1979_ == 0)
{
if (v___x_1978_ == 0)
{
v___y_1960_ = v___x_1977_;
goto v___jp_1959_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_of_nat(v___x_1976_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1954_, v___x_1980_, v___x_1981_, v___x_1977_);
v___y_1960_ = v___x_1982_;
goto v___jp_1959_;
}
}
else
{
size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_of_nat(v___x_1976_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1954_, v___x_1983_, v___x_1984_, v___x_1977_);
v___y_1960_ = v___x_1985_;
goto v___jp_1959_;
}
}
v___jp_1959_:
{
lean_object* v___x_1961_; lean_object* v_prev_x3f_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v___x_1961_ = lean_array_get_size(v___y_1960_);
v_prev_x3f_1962_ = lean_box(0);
v___x_1963_ = lean_box(v_lineStart_1955_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_prev_x3f_1962_);
v___x_1965_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1961_, v___y_1960_, v___x_1958_, v___x_1964_, v_a_1956_, v_a_1957_);
lean_dec_ref(v___y_1960_);
v_snd_1966_ = lean_ctor_get(v___x_1965_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1965_, 0);
lean_dec(v_unused_1975_);
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_snd_1966_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_1986_, lean_object* v_inls_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_delim_1992_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___x_2003_; lean_object* v_snd_2004_; lean_object* v___y_2006_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_1990_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_1991_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1986_, v_inls_1987_);
v_delim_1992_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1986_, v___x_1991_, v___x_1990_);
v___x_2003_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1992_, v_a_1989_);
v_snd_2004_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_snd_2004_);
lean_dec_ref(v___x_2003_);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_array_get_size(v_inls_1987_);
v___x_2015_ = lean_nat_dec_lt(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_box(0);
v___y_2006_ = v___x_2016_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_array_fget_borrowed(v_inls_1987_, v___x_2013_);
lean_inc(v___x_2017_);
v___x_2018_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_2017_);
v___y_2006_ = v___x_2018_;
goto v___jp_2005_;
}
v___jp_1993_:
{
size_t v_sz_1996_; size_t v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v_snd_2001_; lean_object* v___x_2002_; 
v_sz_1996_ = lean_array_size(v_inls_1987_);
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1996_, v___x_1997_, v_inls_1987_);
v___x_1999_ = 0;
v___x_2000_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_1998_, v___x_1999_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___x_1998_);
v_snd_2001_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_snd_2001_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1992_, v_snd_2001_);
lean_dec_ref(v_delim_1992_);
return v___x_2002_;
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = lean_box_uint32(v_char_1986_);
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
v___x_2009_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_2006_, v___x_2008_);
lean_dec_ref_known(v___x_2008_, 1);
lean_dec(v___y_2006_);
if (v___x_2009_ == 0)
{
v___y_1994_ = v_a_1988_;
v___y_1995_ = v_snd_2004_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v_snd_2012_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_2011_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2010_, v_snd_2004_);
v_snd_2012_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2011_);
v___y_1994_ = v_a_1988_;
v___y_1995_ = v_snd_2012_;
goto v___jp_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_2025_, uint8_t v___x_2026_, lean_object* v_as_2027_, size_t v_sz_2028_, size_t v_i_2029_, lean_object* v_b_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_usize_dec_lt(v_i_2029_, v_sz_2028_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref(v___y_2025_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_b_2030_);
lean_ctor_set(v___x_2034_, 1, v___y_2032_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v_snd_2036_; lean_object* v_a_2037_; lean_object* v_contents_2038_; lean_object* v___x_2039_; lean_object* v_snd_2040_; size_t v_sz_2041_; size_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; size_t v___x_2051_; size_t v___x_2052_; 
v___x_2035_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2031_, v___y_2032_);
v_snd_2036_ = lean_ctor_get(v___x_2035_, 1);
lean_inc(v_snd_2036_);
lean_dec_ref(v___x_2035_);
v_a_2037_ = lean_array_uget_borrowed(v_as_2027_, v_i_2029_);
v_contents_2038_ = lean_ctor_get(v_a_2037_, 2);
lean_inc_ref(v___y_2025_);
v___x_2039_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2025_, v_contents_2038_, v_snd_2036_);
v_snd_2040_ = lean_ctor_get(v___x_2039_, 1);
lean_inc(v_snd_2040_);
lean_dec_ref(v___x_2039_);
v_sz_2041_ = lean_array_size(v_contents_2038_);
v___x_2042_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2038_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2041_, v___x_2042_, v_contents_2038_);
v___x_2044_ = lean_string_length(v___y_2025_);
v___x_2045_ = lean_nat_add(v___y_2031_, v___x_2044_);
v___x_2046_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2043_, v___x_2026_, v___x_2045_, v_snd_2040_);
lean_dec(v___x_2045_);
lean_dec_ref(v___x_2043_);
v_snd_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2047_);
v_snd_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_box(0);
v___x_2051_ = ((size_t)1ULL);
v___x_2052_ = lean_usize_add(v_i_2029_, v___x_2051_);
v_i_2029_ = v___x_2052_;
v_b_2030_ = v___x_2050_;
v___y_2032_ = v_snd_2049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2057_, uint8_t v_alternate_2058_, lean_object* v_as_2059_, size_t v_sz_2060_, size_t v_i_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2061_, v_sz_2060_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_b_2062_);
lean_ctor_set(v___x_2066_, 1, v___y_2064_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; lean_object* v_snd_2068_; lean_object* v_a_2069_; lean_object* v___y_2071_; 
v___x_2067_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2063_, v___y_2064_);
v_snd_2068_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2068_);
lean_dec_ref(v___x_2067_);
v_a_2069_ = lean_array_uget_borrowed(v_as_2059_, v_i_2061_);
if (v_alternate_2058_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_inc(v_b_2062_);
v___x_2089_ = l_Nat_reprFast(v_b_2062_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2091_ = lean_string_append(v___x_2089_, v___x_2090_);
v___y_2071_ = v___x_2091_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_inc(v_b_2062_);
v___x_2092_ = l_Nat_reprFast(v_b_2062_);
v___x_2093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
v___y_2071_ = v___x_2094_;
goto v___jp_2070_;
}
v___jp_2070_:
{
lean_object* v_contents_2072_; lean_object* v___x_2073_; lean_object* v_snd_2074_; size_t v_sz_2075_; size_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; lean_object* v_snd_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; 
v_contents_2072_ = lean_ctor_get(v_a_2069_, 2);
lean_inc_ref(v___y_2071_);
v___x_2073_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2071_, v_contents_2072_, v_snd_2068_);
v_snd_2074_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_snd_2074_);
lean_dec_ref(v___x_2073_);
v_sz_2075_ = lean_array_size(v_contents_2072_);
v___x_2076_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2072_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2075_, v___x_2076_, v_contents_2072_);
v___x_2078_ = lean_string_length(v___y_2071_);
lean_dec_ref(v___y_2071_);
v___x_2079_ = lean_nat_add(v___y_2063_, v___x_2078_);
v___x_2080_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2077_, v___x_2057_, v___x_2079_, v_snd_2074_);
lean_dec(v___x_2079_);
lean_dec_ref(v___x_2077_);
v_snd_2081_ = lean_ctor_get(v___x_2080_, 1);
lean_inc(v_snd_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2081_);
v_snd_2083_ = lean_ctor_get(v___x_2082_, 1);
lean_inc(v_snd_2083_);
lean_dec_ref(v___x_2082_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_b_2062_, v___x_2084_);
lean_dec(v_b_2062_);
v___x_2086_ = ((size_t)1ULL);
v___x_2087_ = lean_usize_add(v_i_2061_, v___x_2086_);
v_i_2061_ = v___x_2087_;
v_b_2062_ = v___x_2085_;
v___y_2064_ = v_snd_2083_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2096_, lean_object* v_as_2097_, size_t v_sz_2098_, size_t v_i_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2099_, v_sz_2098_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_b_2100_);
lean_ctor_set(v___x_2104_, 1, v___y_2102_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v_snd_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_snd_2109_; lean_object* v_a_2110_; lean_object* v_term_2111_; lean_object* v___x_2112_; lean_object* v___y_2114_; lean_object* v___y_2115_; uint8_t v___x_2136_; 
v___x_2105_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2101_, v___y_2102_);
v_snd_2106_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_snd_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___closed__0));
v___x_2108_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2107_, v_snd_2106_);
v_snd_2109_ = lean_ctor_get(v___x_2108_, 1);
lean_inc(v_snd_2109_);
lean_dec_ref(v___x_2108_);
v_a_2110_ = lean_array_uget_borrowed(v_as_2097_, v_i_2099_);
v_term_2111_ = lean_ctor_get(v_a_2110_, 2);
v___x_2112_ = lean_box(0);
v___x_2136_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2111_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_snd_2139_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2138_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2137_, v_snd_2109_);
v_snd_2139_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2139_);
lean_dec_ref(v___x_2138_);
v___y_2114_ = v___y_2101_;
v___y_2115_ = v_snd_2139_;
goto v___jp_2113_;
}
else
{
v___y_2114_ = v___y_2101_;
v___y_2115_ = v_snd_2109_;
goto v___jp_2113_;
}
v___jp_2113_:
{
lean_object* v_term_2116_; lean_object* v_desc_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_snd_2122_; lean_object* v___x_2123_; lean_object* v_snd_2124_; size_t v_sz_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_snd_2130_; lean_object* v___x_2131_; lean_object* v_snd_2132_; size_t v___x_2133_; size_t v___x_2134_; 
v_term_2116_ = lean_ctor_get(v_a_2110_, 2);
v_desc_2117_ = lean_ctor_get(v_a_2110_, 3);
v_sz_2118_ = lean_array_size(v_term_2116_);
v___x_2119_ = ((size_t)0ULL);
lean_inc_ref(v_term_2116_);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2118_, v___x_2119_, v_term_2116_);
v___x_2121_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2120_, v___x_2096_, v___y_2114_, v___y_2115_);
lean_dec_ref(v___x_2120_);
v_snd_2122_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_snd_2122_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2122_);
v_snd_2124_ = lean_ctor_get(v___x_2123_, 1);
lean_inc(v_snd_2124_);
lean_dec_ref(v___x_2123_);
v_sz_2125_ = lean_array_size(v_desc_2117_);
lean_inc_ref(v_desc_2117_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2125_, v___x_2119_, v_desc_2117_);
v___x_2127_ = lean_unsigned_to_nat(2u);
v___x_2128_ = lean_nat_add(v___y_2114_, v___x_2127_);
v___x_2129_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2126_, v___x_2096_, v___x_2128_, v_snd_2124_);
lean_dec(v___x_2128_);
lean_dec_ref(v___x_2126_);
v_snd_2130_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_snd_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2130_);
v_snd_2132_ = lean_ctor_get(v___x_2131_, 1);
lean_inc(v_snd_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2099_, v___x_2133_);
v_i_2099_ = v___x_2134_;
v_b_2100_ = v___x_2112_;
v___y_2102_ = v_snd_2132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2143_, lean_object* v_next_x3f_2144_, uint8_t v_atLineStart_2145_, uint8_t v_alternate_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___y_2150_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
lean_inc(v_stx_2143_);
v___x_2180_ = l_Lean_Syntax_getKind(v_stx_2143_);
v___x_2181_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2));
v___x_2182_ = lean_name_eq(v___x_2180_, v___x_2181_);
lean_dec(v___x_2180_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_inc(v_stx_2143_);
v___x_2183_ = l_Lean_Doc_ArgValView_of(v_stx_2143_);
if (lean_obj_tag(v___x_2183_) == 1)
{
lean_object* v_val_2184_; 
lean_dec(v_next_x3f_2144_);
lean_dec(v_stx_2143_);
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
if (lean_obj_tag(v_val_2184_) == 1)
{
lean_object* v_x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_x_2185_ = lean_ctor_get(v_val_2184_, 0);
lean_inc(v_x_2185_);
lean_dec_ref_known(v_val_2184_, 1);
v___x_2186_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2185_);
v___x_2187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2186_, v_a_2148_);
lean_dec_ref(v___x_2186_);
return v___x_2187_;
}
else
{
lean_object* v_lit_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_lit_2188_ = lean_ctor_get(v_val_2184_, 0);
lean_inc(v_lit_2188_);
lean_dec(v_val_2184_);
v___x_2189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2188_);
v___x_2190_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2189_, v_a_2148_);
lean_dec_ref(v___x_2189_);
return v___x_2190_;
}
}
else
{
lean_object* v___x_2191_; 
lean_dec(v___x_2183_);
lean_inc(v_stx_2143_);
v___x_2191_ = l_Lean_Doc_ArgView_of(v_stx_2143_);
if (lean_obj_tag(v___x_2191_) == 1)
{
lean_object* v_val_2192_; 
lean_dec(v_next_x3f_2144_);
lean_dec(v_stx_2143_);
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
switch(lean_obj_tag(v_val_2192_))
{
case 0:
{
lean_object* v_val_2193_; lean_object* v___x_2194_; 
v_val_2193_ = lean_ctor_get(v_val_2192_, 1);
lean_inc(v_val_2193_);
lean_dec_ref_known(v_val_2192_, 2);
v___x_2194_ = lean_box(0);
v_stx_2143_ = v_val_2193_;
v_next_x3f_2144_ = v___x_2194_;
v_atLineStart_2145_ = v___x_2182_;
v_alternate_2146_ = v___x_2182_;
goto _start;
}
case 1:
{
lean_object* v_name_2196_; lean_object* v_val_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_snd_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_snd_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_name_2196_ = lean_ctor_get(v_val_2192_, 2);
lean_inc(v_name_2196_);
v_val_2197_ = lean_ctor_get(v_val_2192_, 4);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_val_2192_, 5);
v___x_2198_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2198_, v_a_2148_);
v_snd_2200_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2196_);
v___x_2202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2201_, v_snd_2200_);
lean_dec_ref(v___x_2201_);
v_snd_2203_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_snd_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2205_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2204_, v_snd_2203_);
v_snd_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = lean_box(0);
v___x_2208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2197_, v___x_2207_, v___x_2182_, v___x_2182_, v_a_2147_, v_snd_2206_);
v_snd_2209_ = lean_ctor_get(v___x_2208_, 1);
lean_inc(v_snd_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2211_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2210_, v_snd_2209_);
return v___x_2211_;
}
default: 
{
lean_object* v_name_2212_; uint8_t v_isOn_2213_; lean_object* v___y_2215_; 
v_name_2212_ = lean_ctor_get(v_val_2192_, 2);
lean_inc(v_name_2212_);
v_isOn_2213_ = lean_ctor_get_uint8(v_val_2192_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2192_, 3);
if (v_isOn_2213_ == 0)
{
lean_object* v___x_2220_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13));
v___y_2215_ = v___x_2220_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___y_2215_ = v___x_2221_;
goto v___jp_2214_;
}
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v_snd_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2215_, v_a_2148_);
v_snd_2217_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_snd_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2212_);
v___x_2219_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2218_, v_snd_2217_);
lean_dec_ref(v___x_2218_);
return v___x_2219_;
}
}
}
}
else
{
lean_object* v___x_2222_; 
lean_dec(v___x_2191_);
lean_inc(v_stx_2143_);
v___x_2222_ = l_Lean_Doc_LinkTargetView_of(v_stx_2143_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2224_; 
lean_dec(v_next_x3f_2144_);
lean_dec(v_stx_2143_);
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2224_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2223_, v_a_2148_);
lean_dec(v_val_2223_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; 
lean_dec(v___x_2222_);
lean_inc(v_stx_2143_);
v___x_2225_ = l_Lean_Doc_InlineView_of(v_stx_2143_);
if (lean_obj_tag(v___x_2225_) == 1)
{
lean_object* v_val_2226_; 
lean_dec(v_stx_2143_);
v_val_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v___x_2225_, 1);
switch(lean_obj_tag(v_val_2226_))
{
case 0:
{
lean_object* v_view_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v_next_x3f_2144_);
v_view_2227_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2227_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2228_ = l_Lean_Doc_TextView_getVersoText(v_view_2227_);
lean_dec_ref(v_view_2227_);
v___x_2229_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2145_, v___x_2228_);
v___x_2230_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2229_, v_a_2148_);
lean_dec_ref(v___x_2229_);
return v___x_2230_;
}
case 1:
{
lean_object* v_view_2231_; lean_object* v_content_2232_; uint32_t v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_next_x3f_2144_);
v_view_2231_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2231_);
lean_dec_ref_known(v_val_2226_, 1);
v_content_2232_ = lean_ctor_get(v_view_2231_, 2);
lean_inc_ref(v_content_2232_);
lean_dec_ref(v_view_2231_);
v___x_2233_ = 95;
v___x_2234_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2233_, v_content_2232_, v_a_2147_, v_a_2148_);
return v___x_2234_;
}
case 2:
{
lean_object* v_view_2235_; lean_object* v_content_2236_; uint32_t v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_next_x3f_2144_);
v_view_2235_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2235_);
lean_dec_ref_known(v_val_2226_, 1);
v_content_2236_ = lean_ctor_get(v_view_2235_, 2);
lean_inc_ref(v_content_2236_);
lean_dec_ref(v_view_2235_);
v___x_2237_ = 42;
v___x_2238_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2237_, v_content_2236_, v_a_2147_, v_a_2148_);
return v___x_2238_;
}
case 3:
{
lean_object* v_view_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec(v_next_x3f_2144_);
v_view_2239_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2239_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2240_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2239_);
lean_dec_ref(v_view_2239_);
v___x_2241_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2240_);
v___x_2242_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2241_, v_a_2148_);
lean_dec_ref(v___x_2241_);
return v___x_2242_;
}
case 4:
{
lean_object* v_view_2243_; lean_object* v___y_2245_; uint8_t v_mode_2251_; 
lean_dec(v_next_x3f_2144_);
v_view_2243_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2243_);
lean_dec_ref_known(v_val_2226_, 1);
v_mode_2251_ = lean_ctor_get_uint8(v_view_2243_, sizeof(void*)*3);
if (v_mode_2251_ == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___y_2245_ = v___x_2252_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2245_ = v___x_2253_;
goto v___jp_2244_;
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2245_, v_a_2148_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = l_Lean_Doc_MathView_getVersoCode(v_view_2243_);
lean_dec_ref(v_view_2243_);
v___x_2249_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2248_);
v___x_2250_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2249_, v_snd_2247_);
lean_dec_ref(v___x_2249_);
return v___x_2250_;
}
}
case 5:
{
lean_object* v_view_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_snd_2257_; lean_object* v_content_2258_; lean_object* v_target_2259_; size_t v_sz_2260_; size_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_snd_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_snd_2267_; lean_object* v___x_2268_; 
lean_dec(v_next_x3f_2144_);
v_view_2254_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2254_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2255_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2256_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2255_, v_a_2148_);
v_snd_2257_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_snd_2257_);
lean_dec_ref(v___x_2256_);
v_content_2258_ = lean_ctor_get(v_view_2254_, 2);
lean_inc_ref(v_content_2258_);
v_target_2259_ = lean_ctor_get(v_view_2254_, 4);
lean_inc_ref(v_target_2259_);
lean_dec_ref(v_view_2254_);
v_sz_2260_ = lean_array_size(v_content_2258_);
v___x_2261_ = ((size_t)0ULL);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2260_, v___x_2261_, v_content_2258_);
v___x_2263_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2262_, v___x_2182_, v_a_2147_, v_snd_2257_);
lean_dec_ref(v___x_2262_);
v_snd_2264_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_snd_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2266_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2265_, v_snd_2264_);
v_snd_2267_ = lean_ctor_get(v___x_2266_, 1);
lean_inc(v_snd_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2259_, v_snd_2267_);
lean_dec_ref(v_target_2259_);
return v___x_2268_;
}
case 6:
{
lean_object* v_view_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v_snd_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_snd_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_snd_2279_; lean_object* v_target_2280_; lean_object* v___x_2281_; 
lean_dec(v_next_x3f_2144_);
v_view_2269_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2269_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2270_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___x_2271_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2270_, v_a_2148_);
v_snd_2272_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_snd_2272_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = l_Lean_Doc_ImageView_getAlt(v_view_2269_);
v___x_2274_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2273_);
v___x_2275_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2274_, v_snd_2272_);
lean_dec_ref(v___x_2274_);
v_snd_2276_ = lean_ctor_get(v___x_2275_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2278_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2277_, v_snd_2276_);
v_snd_2279_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_snd_2279_);
lean_dec_ref(v___x_2278_);
v_target_2280_ = lean_ctor_get(v_view_2269_, 4);
lean_inc_ref(v_target_2280_);
lean_dec_ref(v_view_2269_);
v___x_2281_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2280_, v_snd_2279_);
lean_dec_ref(v_target_2280_);
return v___x_2281_;
}
case 7:
{
lean_object* v_view_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v_snd_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec(v_next_x3f_2144_);
v_view_2282_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2282_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2283_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2284_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2283_, v_a_2148_);
v_snd_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = l_Lean_Doc_FootnoteView_getName(v_view_2282_);
lean_dec_ref(v_view_2282_);
v___x_2287_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2286_, v_snd_2285_);
lean_dec_ref(v___x_2286_);
v_snd_2288_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_snd_2288_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2290_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2289_, v_snd_2288_);
return v___x_2290_;
}
case 8:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref_known(v_val_2226_, 1);
lean_dec(v_next_x3f_2144_);
v___x_2291_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2292_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2291_, v_a_2148_);
return v___x_2292_;
}
default: 
{
lean_object* v_view_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_snd_2296_; lean_object* v_name_2297_; lean_object* v_args_2298_; lean_object* v_content_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v_snd_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_snd_2310_; lean_object* v___x_2321_; 
v_view_2293_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_view_2293_);
lean_dec_ref_known(v_val_2226_, 1);
v___x_2294_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2295_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2294_, v_a_2148_);
v_snd_2296_ = lean_ctor_get(v___x_2295_, 1);
lean_inc(v_snd_2296_);
lean_dec_ref(v___x_2295_);
v_name_2297_ = lean_ctor_get(v_view_2293_, 2);
lean_inc(v_name_2297_);
v_args_2298_ = lean_ctor_get(v_view_2293_, 3);
lean_inc_ref(v_args_2298_);
v_content_2299_ = lean_ctor_get(v_view_2293_, 6);
lean_inc_ref(v_content_2299_);
lean_dec_ref(v_view_2293_);
v___x_2300_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2297_);
v___x_2301_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2300_, v_snd_2296_);
lean_dec_ref(v___x_2300_);
v_snd_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = lean_box(0);
v_sz_2304_ = lean_array_size(v_args_2298_);
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2182_, v_args_2298_, v_sz_2304_, v___x_2305_, v___x_2303_, v_a_2147_, v_snd_2302_);
lean_dec_ref(v_args_2298_);
v_snd_2307_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_snd_2307_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2309_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2308_, v_snd_2307_);
v_snd_2310_ = lean_ctor_get(v___x_2309_, 1);
lean_inc(v_snd_2310_);
lean_dec_ref(v___x_2309_);
v___x_2321_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2299_);
if (lean_obj_tag(v___x_2321_) == 1)
{
lean_object* v_val_2322_; uint8_t v___x_2323_; 
v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2322_, v_next_x3f_2144_);
if (v___x_2323_ == 0)
{
size_t v_sz_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_sz_2324_ = lean_array_size(v_content_2299_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2324_, v___x_2305_, v_content_2299_);
v___x_2326_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2325_, v___x_2323_, v_a_2147_, v_snd_2310_);
lean_dec_ref(v___x_2325_);
return v___x_2326_;
}
else
{
goto v___jp_2311_;
}
}
else
{
lean_dec(v___x_2321_);
lean_dec(v_next_x3f_2144_);
goto v___jp_2311_;
}
v___jp_2311_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_snd_2314_; size_t v_sz_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2313_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2312_, v_snd_2310_);
v_snd_2314_ = lean_ctor_get(v___x_2313_, 1);
lean_inc(v_snd_2314_);
lean_dec_ref(v___x_2313_);
v_sz_2315_ = lean_array_size(v_content_2299_);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2315_, v___x_2305_, v_content_2299_);
v___x_2317_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2316_, v___x_2182_, v_a_2147_, v_snd_2314_);
lean_dec_ref(v___x_2316_);
v_snd_2318_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_snd_2318_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2320_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2319_, v_snd_2318_);
return v___x_2320_;
}
}
}
}
else
{
lean_object* v___x_2327_; 
lean_dec(v___x_2225_);
lean_dec(v_next_x3f_2144_);
lean_inc(v_stx_2143_);
v___x_2327_ = l_Lean_Doc_BlockView_of(v_stx_2143_);
if (lean_obj_tag(v___x_2327_) == 1)
{
lean_object* v_val_2328_; 
v_val_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_val_2328_);
lean_dec_ref_known(v___x_2327_, 1);
switch(lean_obj_tag(v_val_2328_))
{
case 0:
{
lean_object* v_view_2329_; lean_object* v_content_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
lean_dec(v_stx_2143_);
v_view_2329_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2329_);
lean_dec_ref_known(v_val_2328_, 1);
v_content_2330_ = lean_ctor_get(v_view_2329_, 1);
lean_inc_ref(v_content_2330_);
lean_dec_ref(v_view_2329_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_array_get_size(v_content_2330_);
v___x_2333_ = lean_nat_dec_lt(v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v_content_2330_);
goto v___jp_2177_;
}
else
{
if (v___x_2333_ == 0)
{
lean_dec_ref(v_content_2330_);
goto v___jp_2177_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; uint8_t v___x_2336_; lean_object* v___y_2338_; lean_object* v___y_2339_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2332_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2182_, v_content_2330_, v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v_content_2330_);
goto v___jp_2177_;
}
else
{
if (v___x_2182_ == 0)
{
lean_object* v___x_2345_; lean_object* v_snd_2346_; 
v___x_2345_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2346_ = lean_ctor_get(v___x_2345_, 1);
lean_inc(v_snd_2346_);
lean_dec_ref(v___x_2345_);
if (v___x_2333_ == 0)
{
goto v___jp_2347_;
}
else
{
if (v___x_2333_ == 0)
{
goto v___jp_2347_;
}
else
{
uint8_t v___x_2351_; 
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2336_, v___x_2182_, v_content_2330_, v___x_2334_, v___x_2335_);
if (v___x_2351_ == 0)
{
goto v___jp_2347_;
}
else
{
v___y_2338_ = v_a_2147_;
v___y_2339_ = v_snd_2346_;
goto v___jp_2337_;
}
}
}
v___jp_2347_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v_snd_2350_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2348_, v_snd_2346_);
v_snd_2350_ = lean_ctor_get(v___x_2349_, 1);
lean_inc(v_snd_2350_);
lean_dec_ref(v___x_2349_);
v___y_2338_ = v_a_2147_;
v___y_2339_ = v_snd_2350_;
goto v___jp_2337_;
}
}
else
{
lean_dec_ref(v_content_2330_);
goto v___jp_2177_;
}
}
v___jp_2337_:
{
size_t v_sz_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_snd_2343_; lean_object* v___x_2344_; 
v_sz_2340_ = lean_array_size(v_content_2330_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2340_, v___x_2334_, v_content_2330_);
v___x_2342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2341_, v___x_2336_, v___y_2338_, v___y_2339_);
lean_dec_ref(v___x_2341_);
v_snd_2343_ = lean_ctor_get(v___x_2342_, 1);
lean_inc(v_snd_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2343_);
return v___x_2344_;
}
}
}
}
case 1:
{
lean_object* v_view_2352_; lean_object* v___y_2354_; 
lean_dec(v_stx_2143_);
v_view_2352_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2352_);
lean_dec_ref_known(v_val_2328_, 1);
if (v_alternate_2146_ == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___y_2354_ = v___x_2362_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2363_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___y_2354_ = v___x_2363_;
goto v___jp_2353_;
}
v___jp_2353_:
{
lean_object* v_items_2355_; lean_object* v___x_2356_; size_t v_sz_2357_; size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v_snd_2360_; lean_object* v___x_2361_; 
v_items_2355_ = lean_ctor_get(v_view_2352_, 1);
lean_inc_ref(v_items_2355_);
lean_dec_ref(v_view_2352_);
v___x_2356_ = lean_box(0);
v_sz_2357_ = lean_array_size(v_items_2355_);
v___x_2358_ = ((size_t)0ULL);
lean_inc_ref(v___y_2354_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2354_, v___x_2182_, v_items_2355_, v_sz_2357_, v___x_2358_, v___x_2356_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_items_2355_);
v_snd_2360_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_snd_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2360_);
return v___x_2361_;
}
}
case 2:
{
lean_object* v_view_2364_; lean_object* v_start_2365_; lean_object* v_items_2366_; size_t v_sz_2367_; size_t v___x_2368_; lean_object* v___x_2369_; lean_object* v_snd_2370_; lean_object* v___x_2371_; 
lean_dec(v_stx_2143_);
v_view_2364_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2364_);
lean_dec_ref_known(v_val_2328_, 1);
v_start_2365_ = lean_ctor_get(v_view_2364_, 1);
lean_inc(v_start_2365_);
v_items_2366_ = lean_ctor_get(v_view_2364_, 2);
lean_inc_ref(v_items_2366_);
lean_dec_ref(v_view_2364_);
v_sz_2367_ = lean_array_size(v_items_2366_);
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2182_, v_alternate_2146_, v_items_2366_, v_sz_2367_, v___x_2368_, v_start_2365_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_items_2366_);
v_snd_2370_ = lean_ctor_get(v___x_2369_, 1);
lean_inc(v_snd_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2370_);
return v___x_2371_;
}
case 3:
{
lean_object* v_view_2372_; lean_object* v_items_2373_; lean_object* v___x_2374_; size_t v_sz_2375_; size_t v___x_2376_; lean_object* v___x_2377_; lean_object* v_snd_2378_; lean_object* v___x_2379_; 
lean_dec(v_stx_2143_);
v_view_2372_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2372_);
lean_dec_ref_known(v_val_2328_, 1);
v_items_2373_ = lean_ctor_get(v_view_2372_, 1);
lean_inc_ref(v_items_2373_);
lean_dec_ref(v_view_2372_);
v___x_2374_ = lean_box(0);
v_sz_2375_ = lean_array_size(v_items_2373_);
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2182_, v_items_2373_, v_sz_2375_, v___x_2376_, v___x_2374_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_items_2373_);
v_snd_2378_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_snd_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2378_);
return v___x_2379_;
}
case 4:
{
lean_object* v_view_2380_; lean_object* v___x_2381_; lean_object* v_snd_2382_; lean_object* v_content_2383_; lean_object* v___y_2385_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
lean_dec(v_stx_2143_);
v_view_2380_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2380_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2381_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2382_ = lean_ctor_get(v___x_2381_, 1);
lean_inc(v_snd_2382_);
lean_dec_ref(v___x_2381_);
v_content_2383_ = lean_ctor_get(v_view_2380_, 2);
lean_inc_ref(v_content_2383_);
lean_dec_ref(v_view_2380_);
v___x_2396_ = lean_array_get_size(v_content_2383_);
v___x_2397_ = lean_unsigned_to_nat(0u);
v___x_2398_ = lean_nat_dec_eq(v___x_2396_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2385_ = v___x_2399_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___y_2385_ = v___x_2400_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v_snd_2387_; size_t v_sz_2388_; size_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; 
v___x_2386_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2385_, v_snd_2382_);
v_snd_2387_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_snd_2387_);
lean_dec_ref(v___x_2386_);
v_sz_2388_ = lean_array_size(v_content_2383_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2388_, v___x_2389_, v_content_2383_);
v___x_2391_ = lean_unsigned_to_nat(2u);
v___x_2392_ = lean_nat_add(v_a_2147_, v___x_2391_);
v___x_2393_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2390_, v___x_2182_, v___x_2392_, v_snd_2387_);
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2390_);
v_snd_2394_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2394_);
return v___x_2395_;
}
}
case 5:
{
lean_object* v_view_2401_; lean_object* v___x_2402_; lean_object* v_snd_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2428_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
lean_dec(v_stx_2143_);
v_view_2401_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2401_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2402_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2403_ = lean_ctor_get(v___x_2402_, 1);
lean_inc(v_snd_2403_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2405_ = lean_unsigned_to_nat(3u);
v___x_2406_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2401_);
lean_inc_ref(v___x_2406_);
v___x_2444_ = l_Lean_Doc_longestBacktickRun(v___x_2406_);
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_nat_add(v___x_2444_, v___x_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_nat_dec_le(v___x_2405_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_dec(v___x_2446_);
v___y_2428_ = v___x_2405_;
goto v___jp_2427_;
}
else
{
v___y_2428_ = v___x_2446_;
goto v___jp_2427_;
}
v___jp_2407_:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_string_append(v___x_2406_, v___y_2410_);
v___y_2159_ = v___y_2408_;
v___y_2160_ = v___y_2409_;
v___y_2161_ = v___y_2410_;
v___y_2162_ = v___y_2411_;
v___y_2163_ = v___x_2412_;
goto v___jp_2158_;
}
v___jp_2413_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_snd_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2418_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2417_, v___y_2416_);
v_snd_2419_ = lean_ctor_get(v___x_2418_, 1);
lean_inc(v_snd_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = lean_string_utf8_byte_size(v___x_2406_);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_nat_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_2424_ = lean_nat_dec_le(v___x_2423_, v___x_2420_);
if (v___x_2424_ == 0)
{
v___y_2408_ = v___y_2414_;
v___y_2409_ = v_snd_2419_;
v___y_2410_ = v___x_2417_;
v___y_2411_ = v___y_2415_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_nat_sub(v___x_2420_, v___x_2423_);
v___x_2426_ = lean_string_memcmp(v___x_2406_, v___x_2417_, v___x_2425_, v___x_2421_, v___x_2423_);
lean_dec(v___x_2425_);
if (v___x_2426_ == 0)
{
v___y_2408_ = v___y_2414_;
v___y_2409_ = v_snd_2419_;
v___y_2410_ = v___x_2417_;
v___y_2411_ = v___y_2415_;
goto v___jp_2407_;
}
else
{
v___y_2159_ = v___y_2414_;
v___y_2160_ = v_snd_2419_;
v___y_2161_ = v___x_2417_;
v___y_2162_ = v___y_2415_;
v___y_2163_ = v___x_2406_;
goto v___jp_2158_;
}
}
}
else
{
v___y_2159_ = v___y_2414_;
v___y_2160_ = v_snd_2419_;
v___y_2161_ = v___x_2417_;
v___y_2162_ = v___y_2415_;
v___y_2163_ = v___x_2406_;
goto v___jp_2158_;
}
}
v___jp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_name_x3f_2431_; 
v___x_2429_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2428_, v___x_2404_);
v___x_2430_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2429_, v_snd_2403_);
v_name_x3f_2431_ = lean_ctor_get(v_view_2401_, 2);
lean_inc(v_name_x3f_2431_);
if (lean_obj_tag(v_name_x3f_2431_) == 1)
{
lean_object* v_snd_2432_; lean_object* v_args_2433_; lean_object* v_val_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_snd_2437_; lean_object* v___x_2438_; size_t v_sz_2439_; size_t v___x_2440_; lean_object* v___x_2441_; lean_object* v_snd_2442_; 
v_snd_2432_ = lean_ctor_get(v___x_2430_, 1);
lean_inc(v_snd_2432_);
lean_dec_ref(v___x_2430_);
v_args_2433_ = lean_ctor_get(v_view_2401_, 3);
lean_inc_ref(v_args_2433_);
lean_dec_ref(v_view_2401_);
v_val_2434_ = lean_ctor_get(v_name_x3f_2431_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v_name_x3f_2431_, 1);
v___x_2435_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2434_);
v___x_2436_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2435_, v_snd_2432_);
lean_dec_ref(v___x_2435_);
v_snd_2437_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_snd_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = lean_box(0);
v_sz_2439_ = lean_array_size(v_args_2433_);
v___x_2440_ = ((size_t)0ULL);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2182_, v_args_2433_, v_sz_2439_, v___x_2440_, v___x_2438_, v_a_2147_, v_snd_2437_);
lean_dec_ref(v_args_2433_);
v_snd_2442_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_snd_2442_);
lean_dec_ref(v___x_2441_);
v___y_2414_ = v___x_2429_;
v___y_2415_ = v_a_2147_;
v___y_2416_ = v_snd_2442_;
goto v___jp_2413_;
}
else
{
lean_object* v_snd_2443_; 
lean_dec(v_name_x3f_2431_);
lean_dec_ref(v_view_2401_);
v_snd_2443_ = lean_ctor_get(v___x_2430_, 1);
lean_inc(v_snd_2443_);
lean_dec_ref(v___x_2430_);
v___y_2414_ = v___x_2429_;
v___y_2415_ = v_a_2147_;
v___y_2416_ = v_snd_2443_;
goto v___jp_2413_;
}
}
}
case 6:
{
lean_object* v_view_2448_; lean_object* v___x_2449_; lean_object* v_snd_2450_; lean_object* v_name_2451_; lean_object* v_args_2452_; lean_object* v_content_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_snd_2461_; lean_object* v___x_2462_; size_t v_sz_2463_; size_t v___x_2464_; lean_object* v___x_2465_; lean_object* v_snd_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_snd_2469_; size_t v_sz_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_snd_2476_; lean_object* v___x_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; 
lean_dec(v_stx_2143_);
v_view_2448_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2448_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2449_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2450_ = lean_ctor_get(v___x_2449_, 1);
lean_inc(v_snd_2450_);
lean_dec_ref(v___x_2449_);
v_name_2451_ = lean_ctor_get(v_view_2448_, 2);
lean_inc(v_name_2451_);
v_args_2452_ = lean_ctor_get(v_view_2448_, 3);
lean_inc_ref(v_args_2452_);
v_content_2453_ = lean_ctor_get(v_view_2448_, 4);
lean_inc_ref(v_content_2453_);
lean_dec_ref(v_view_2448_);
v___x_2454_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2455_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2453_);
v___x_2456_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2455_, v___x_2454_);
v___x_2457_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2456_, v_snd_2450_);
v_snd_2458_ = lean_ctor_get(v___x_2457_, 1);
lean_inc(v_snd_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2451_);
v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2459_, v_snd_2458_);
lean_dec_ref(v___x_2459_);
v_snd_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_snd_2461_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = lean_box(0);
v_sz_2463_ = lean_array_size(v_args_2452_);
v___x_2464_ = ((size_t)0ULL);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2182_, v_args_2452_, v_sz_2463_, v___x_2464_, v___x_2462_, v_a_2147_, v_snd_2461_);
lean_dec_ref(v_args_2452_);
v_snd_2466_ = lean_ctor_get(v___x_2465_, 1);
lean_inc(v_snd_2466_);
lean_dec_ref(v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2468_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2467_, v_snd_2466_);
v_snd_2469_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v___x_2468_);
v_sz_2470_ = lean_array_size(v_content_2453_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2470_, v___x_2464_, v_content_2453_);
v___x_2472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2471_, v___x_2182_, v_a_2147_, v_snd_2469_);
lean_dec_ref(v___x_2471_);
v_snd_2473_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2472_);
lean_inc(v_a_2147_);
v___x_2474_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2147_, v___x_2454_);
v___x_2475_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2474_, v_snd_2473_);
lean_dec_ref(v___x_2474_);
v_snd_2476_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_snd_2476_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2456_, v_snd_2476_);
lean_dec_ref(v___x_2456_);
v_snd_2478_ = lean_ctor_get(v___x_2477_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2478_);
return v___x_2479_;
}
case 7:
{
lean_object* v_view_2480_; lean_object* v___x_2481_; lean_object* v_snd_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_snd_2485_; lean_object* v_name_2486_; lean_object* v_args_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v_snd_2490_; lean_object* v___x_2491_; size_t v_sz_2492_; size_t v___x_2493_; lean_object* v___x_2494_; lean_object* v_snd_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_snd_2498_; lean_object* v___x_2499_; 
lean_dec(v_stx_2143_);
v_view_2480_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2480_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2481_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2482_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_snd_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2484_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2483_, v_snd_2482_);
v_snd_2485_ = lean_ctor_get(v___x_2484_, 1);
lean_inc(v_snd_2485_);
lean_dec_ref(v___x_2484_);
v_name_2486_ = lean_ctor_get(v_view_2480_, 2);
lean_inc(v_name_2486_);
v_args_2487_ = lean_ctor_get(v_view_2480_, 3);
lean_inc_ref(v_args_2487_);
lean_dec_ref(v_view_2480_);
v___x_2488_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2486_);
v___x_2489_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2488_, v_snd_2485_);
lean_dec_ref(v___x_2488_);
v_snd_2490_ = lean_ctor_get(v___x_2489_, 1);
lean_inc(v_snd_2490_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = lean_box(0);
v_sz_2492_ = lean_array_size(v_args_2487_);
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2182_, v_args_2487_, v_sz_2492_, v___x_2493_, v___x_2491_, v_a_2147_, v_snd_2490_);
lean_dec_ref(v_args_2487_);
v_snd_2495_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2497_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2496_, v_snd_2495_);
v_snd_2498_ = lean_ctor_get(v___x_2497_, 1);
lean_inc(v_snd_2498_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2498_);
return v___x_2499_;
}
case 8:
{
lean_object* v_view_2500_; lean_object* v___x_2501_; lean_object* v_snd_2502_; lean_object* v_level_2503_; lean_object* v_content_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v_snd_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_snd_2515_; lean_object* v___x_2516_; 
lean_dec(v_stx_2143_);
v_view_2500_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2500_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2502_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_snd_2502_);
lean_dec_ref(v___x_2501_);
v_level_2503_ = lean_ctor_get(v_view_2500_, 2);
lean_inc(v_level_2503_);
v_content_2504_ = lean_ctor_get(v_view_2500_, 3);
lean_inc_ref(v_content_2504_);
lean_dec_ref(v_view_2500_);
v___x_2505_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_2506_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2503_, v___x_2505_);
v___x_2507_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2508_ = lean_string_append(v___x_2506_, v___x_2507_);
v___x_2509_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2508_, v_snd_2502_);
lean_dec_ref(v___x_2508_);
v_snd_2510_ = lean_ctor_get(v___x_2509_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2509_);
v_sz_2511_ = lean_array_size(v_content_2504_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2511_, v___x_2512_, v_content_2504_);
v___x_2514_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2513_, v___x_2182_, v_a_2147_, v_snd_2510_);
lean_dec_ref(v___x_2513_);
v_snd_2515_ = lean_ctor_get(v___x_2514_, 1);
lean_inc(v_snd_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2515_);
return v___x_2516_;
}
case 9:
{
lean_object* v_view_2517_; lean_object* v___x_2518_; lean_object* v_snd_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_snd_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v_snd_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_snd_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_snd_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_snd_2534_; lean_object* v___x_2535_; 
lean_dec(v_stx_2143_);
v_view_2517_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2517_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2518_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2519_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2521_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2520_, v_snd_2519_);
v_snd_2522_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2522_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = l_Lean_Doc_LinkRefView_getName(v_view_2517_);
v___x_2524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2523_, v_snd_2522_);
lean_dec_ref(v___x_2523_);
v_snd_2525_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_snd_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___x_2527_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2526_, v_snd_2525_);
v_snd_2528_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2530_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2529_, v_snd_2528_);
v_snd_2531_ = lean_ctor_get(v___x_2530_, 1);
lean_inc(v_snd_2531_);
lean_dec_ref(v___x_2530_);
v___x_2532_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2517_);
lean_dec_ref(v_view_2517_);
v___x_2533_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2532_, v_snd_2531_);
lean_dec_ref(v___x_2532_);
v_snd_2534_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_snd_2534_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2534_);
return v___x_2535_;
}
case 10:
{
lean_object* v_view_2536_; lean_object* v___x_2537_; lean_object* v_snd_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_snd_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_snd_2550_; lean_object* v_content_2551_; size_t v_sz_2552_; size_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v_snd_2556_; lean_object* v___x_2557_; 
lean_dec(v_stx_2143_);
v_view_2536_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2536_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2537_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2538_ = lean_ctor_get(v___x_2537_, 1);
lean_inc(v_snd_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2540_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2539_, v_snd_2538_);
v_snd_2541_ = lean_ctor_get(v___x_2540_, 1);
lean_inc(v_snd_2541_);
lean_dec_ref(v___x_2540_);
v___x_2542_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2536_);
v___x_2543_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2542_, v_snd_2541_);
lean_dec_ref(v___x_2542_);
v_snd_2544_ = lean_ctor_get(v___x_2543_, 1);
lean_inc(v_snd_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___x_2546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2545_, v_snd_2544_);
v_snd_2547_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_snd_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2549_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2548_, v_snd_2547_);
v_snd_2550_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_snd_2550_);
lean_dec_ref(v___x_2549_);
v_content_2551_ = lean_ctor_get(v_view_2536_, 4);
lean_inc_ref(v_content_2551_);
lean_dec_ref(v_view_2536_);
v_sz_2552_ = lean_array_size(v_content_2551_);
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2552_, v___x_2553_, v_content_2551_);
v___x_2555_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2554_, v___x_2182_, v_a_2147_, v_snd_2550_);
lean_dec_ref(v___x_2554_);
v_snd_2556_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_snd_2556_);
lean_dec_ref(v___x_2555_);
v___x_2557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2556_);
return v___x_2557_;
}
default: 
{
lean_object* v_view_2558_; lean_object* v___x_2559_; lean_object* v_snd_2560_; lean_object* v___y_2562_; lean_object* v___x_2575_; 
v_view_2558_ = lean_ctor_get(v_val_2328_, 0);
lean_inc_ref(v_view_2558_);
lean_dec_ref_known(v_val_2328_, 1);
v___x_2559_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2147_, v_a_2148_);
v_snd_2560_ = lean_ctor_get(v___x_2559_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2559_);
v___x_2575_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2143_, v___x_2182_, v___x_2182_);
lean_dec(v_stx_2143_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_contents_2576_; lean_object* v___x_2577_; 
v_contents_2576_ = lean_ctor_get(v_view_2558_, 2);
lean_inc(v_contents_2576_);
lean_dec_ref(v_view_2558_);
v___x_2577_ = l_Lean_Syntax_reprint(v_contents_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___y_2562_ = v___x_2578_;
goto v___jp_2561_;
}
else
{
lean_object* v_val_2579_; 
v_val_2579_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v___x_2577_, 1);
v___y_2562_ = v_val_2579_;
goto v___jp_2561_;
}
}
else
{
lean_object* v_val_2580_; lean_object* v_str_2581_; lean_object* v_startPos_2582_; lean_object* v_stopPos_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v_snd_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v_view_2558_);
v_val_2580_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v___x_2575_, 1);
v_str_2581_ = lean_ctor_get(v_val_2580_, 0);
lean_inc_ref(v_str_2581_);
v_startPos_2582_ = lean_ctor_get(v_val_2580_, 1);
lean_inc(v_startPos_2582_);
v_stopPos_2583_ = lean_ctor_get(v_val_2580_, 2);
lean_inc(v_stopPos_2583_);
lean_dec(v_val_2580_);
v___x_2584_ = lean_string_utf8_extract(v_str_2581_, v_startPos_2582_, v_stopPos_2583_);
lean_dec(v_stopPos_2583_);
lean_dec(v_startPos_2582_);
lean_dec_ref(v_str_2581_);
lean_inc(v_a_2147_);
v___x_2585_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2147_, v___x_2584_);
v___x_2586_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2585_, v_snd_2560_);
lean_dec_ref(v___x_2585_);
v_snd_2587_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_snd_2587_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2587_);
return v___x_2588_;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_snd_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2564_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2563_, v_snd_2560_);
v_snd_2565_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_snd_2565_);
lean_dec_ref(v___x_2564_);
lean_inc(v_a_2147_);
v___x_2566_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2147_, v___y_2562_);
v___x_2567_ = lean_string_utf8_byte_size(v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = lean_nat_dec_eq(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v_snd_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_snd_2574_; 
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2566_, v_snd_2565_);
lean_dec_ref(v___x_2566_);
v_snd_2571_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2573_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2572_, v_snd_2571_);
v_snd_2574_ = lean_ctor_get(v___x_2573_, 1);
lean_inc(v_snd_2574_);
lean_dec_ref(v___x_2573_);
v___y_2150_ = v_snd_2574_;
goto v___jp_2149_;
}
else
{
lean_dec_ref(v___x_2566_);
v___y_2150_ = v_snd_2565_;
goto v___jp_2149_;
}
}
}
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v___x_2327_);
v___x_2589_ = lean_box(0);
v___x_2590_ = l_Lean_Syntax_formatStx(v_stx_2143_, v___x_2589_, v___x_2182_);
v___x_2591_ = l_Std_Format_defWidth;
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = l_Std_Format_pretty(v___x_2590_, v___x_2591_, v___x_2592_, v___x_2592_);
v___x_2594_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2593_, v_a_2148_);
lean_dec_ref(v___x_2593_);
return v___x_2594_;
}
}
}
}
}
}
else
{
lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; 
lean_dec(v_next_x3f_2144_);
v___x_2595_ = l_Lean_Syntax_getArgs(v_stx_2143_);
lean_dec(v_stx_2143_);
v___x_2596_ = 0;
v___x_2597_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2595_, v___x_2596_, v_a_2147_, v_a_2148_);
lean_dec_ref(v___x_2595_);
return v___x_2597_;
}
v___jp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_snd_2156_; lean_object* v___x_2157_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
lean_inc(v_a_2147_);
v___x_2152_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2147_, v___x_2151_);
v___x_2153_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2154_ = lean_string_append(v___x_2152_, v___x_2153_);
v___x_2155_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2154_, v___y_2150_);
lean_dec_ref(v___x_2154_);
v_snd_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2156_);
return v___x_2157_;
}
v___jp_2158_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; lean_object* v_snd_2175_; lean_object* v___x_2176_; 
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_string_utf8_byte_size(v___y_2163_);
lean_inc_ref(v___y_2163_);
v___x_2166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2163_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
lean_ctor_set(v___x_2166_, 2, v___x_2165_);
v___x_2167_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v___x_2166_);
v___x_2168_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0));
v___x_2169_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2162_, v___y_2163_, v___x_2166_, v___x_2165_, v___x_2167_, v___x_2168_);
lean_dec_ref_known(v___x_2166_, 3);
lean_dec_ref(v___y_2163_);
v___x_2170_ = lean_array_to_list(v___x_2169_);
v___x_2171_ = l_String_intercalate(v___y_2161_, v___x_2170_);
v___x_2172_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2171_, v___y_2160_);
lean_dec_ref(v___x_2171_);
v_snd_2173_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2159_, v_snd_2173_);
lean_dec_ref(v___y_2159_);
v_snd_2175_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_snd_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2175_);
return v___x_2176_;
}
v___jp_2177_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v_a_2148_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2598_, lean_object* v_as_2599_, size_t v_sz_2600_, size_t v_i_2601_, lean_object* v_b_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_usize_dec_lt(v_i_2601_, v_sz_2600_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_b_2602_);
lean_ctor_set(v___x_2606_, 1, v___y_2604_);
return v___x_2606_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v_snd_2609_; lean_object* v_a_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_snd_2613_; lean_object* v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2608_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2607_, v___y_2604_);
v_snd_2609_ = lean_ctor_get(v___x_2608_, 1);
lean_inc(v_snd_2609_);
lean_dec_ref(v___x_2608_);
v_a_2610_ = lean_array_uget_borrowed(v_as_2599_, v_i_2601_);
v___x_2611_ = lean_box(0);
lean_inc(v_a_2610_);
v___x_2612_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2610_, v___x_2611_, v___x_2598_, v___x_2598_, v___y_2603_, v_snd_2609_);
v_snd_2613_ = lean_ctor_get(v___x_2612_, 1);
lean_inc(v_snd_2613_);
lean_dec_ref(v___x_2612_);
v___x_2614_ = lean_box(0);
v___x_2615_ = ((size_t)1ULL);
v___x_2616_ = lean_usize_add(v_i_2601_, v___x_2615_);
v_i_2601_ = v___x_2616_;
v_b_2602_ = v___x_2614_;
v___y_2604_ = v_snd_2613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2618_, lean_object* v_as_2619_, lean_object* v_sz_2620_, lean_object* v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v___x_60375__boxed_2625_; size_t v_sz_boxed_2626_; size_t v_i_boxed_2627_; lean_object* v_res_2628_; 
v___x_60375__boxed_2625_ = lean_unbox(v___x_2618_);
v_sz_boxed_2626_ = lean_unbox_usize(v_sz_2620_);
lean_dec(v_sz_2620_);
v_i_boxed_2627_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_res_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_60375__boxed_2625_, v_as_2619_, v_sz_boxed_2626_, v_i_boxed_2627_, v_b_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v_as_2619_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2629_, lean_object* v___x_2630_, lean_object* v_as_2631_, lean_object* v_sz_2632_, lean_object* v_i_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v___x_60393__boxed_2637_; size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v___x_60393__boxed_2637_ = lean_unbox(v___x_2630_);
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2632_);
lean_dec(v_sz_2632_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2633_);
lean_dec(v_i_2633_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2629_, v___x_60393__boxed_2637_, v_as_2631_, v_sz_boxed_2638_, v_i_boxed_2639_, v_b_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v_as_2631_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2641_, lean_object* v_lineStart_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
uint8_t v_lineStart_boxed_2645_; lean_object* v_res_2646_; 
v_lineStart_boxed_2645_ = lean_unbox(v_lineStart_2642_);
v_res_2646_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2641_, v_lineStart_boxed_2645_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_stxs_2641_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2647_, lean_object* v_inls_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
uint32_t v_char_boxed_2651_; lean_object* v_res_2652_; 
v_char_boxed_2651_ = lean_unbox_uint32(v_char_2647_);
lean_dec(v_char_2647_);
v_res_2652_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2651_, v_inls_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2649_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2653_, lean_object* v_alternate_2654_, lean_object* v_as_2655_, lean_object* v_sz_2656_, lean_object* v_i_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v___x_60473__boxed_2661_; uint8_t v_alternate_boxed_2662_; size_t v_sz_boxed_2663_; size_t v_i_boxed_2664_; lean_object* v_res_2665_; 
v___x_60473__boxed_2661_ = lean_unbox(v___x_2653_);
v_alternate_boxed_2662_ = lean_unbox(v_alternate_2654_);
v_sz_boxed_2663_ = lean_unbox_usize(v_sz_2656_);
lean_dec(v_sz_2656_);
v_i_boxed_2664_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_60473__boxed_2661_, v_alternate_boxed_2662_, v_as_2655_, v_sz_boxed_2663_, v_i_boxed_2664_, v_b_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v_as_2655_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2666_, lean_object* v_as_2667_, lean_object* v_sz_2668_, lean_object* v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_60508__boxed_2673_; size_t v_sz_boxed_2674_; size_t v_i_boxed_2675_; lean_object* v_res_2676_; 
v___x_60508__boxed_2673_ = lean_unbox(v___x_2666_);
v_sz_boxed_2674_ = lean_unbox_usize(v_sz_2668_);
lean_dec(v_sz_2668_);
v_i_boxed_2675_ = lean_unbox_usize(v_i_2669_);
lean_dec(v_i_2669_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_60508__boxed_2673_, v_as_2667_, v_sz_boxed_2674_, v_i_boxed_2675_, v_b_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v_as_2667_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2677_, lean_object* v___y_2678_, lean_object* v_a_2679_, lean_object* v_b_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2677_, v___y_2678_, v_a_2679_, v_b_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2678_);
lean_dec(v_upperBound_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2684_, lean_object* v_next_x3f_2685_, lean_object* v_atLineStart_2686_, lean_object* v_alternate_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_atLineStart_boxed_2690_; uint8_t v_alternate_boxed_2691_; lean_object* v_res_2692_; 
v_atLineStart_boxed_2690_ = lean_unbox(v_atLineStart_2686_);
v_alternate_boxed_2691_ = lean_unbox(v_alternate_2687_);
v_res_2692_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2684_, v_next_x3f_2685_, v_atLineStart_boxed_2690_, v_alternate_boxed_2691_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2688_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2693_, lean_object* v___y_2694_, lean_object* v_inst_2695_, lean_object* v_R_2696_, lean_object* v_a_2697_, lean_object* v_b_2698_, lean_object* v_c_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2693_, v___y_2694_, v_a_2697_, v_b_2698_, v___y_2700_, v___y_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2703_, lean_object* v___y_2704_, lean_object* v_inst_2705_, lean_object* v_R_2706_, lean_object* v_a_2707_, lean_object* v_b_2708_, lean_object* v_c_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2703_, v___y_2704_, v_inst_2705_, v_R_2706_, v_a_2707_, v_b_2708_, v_c_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2704_);
lean_dec(v_upperBound_2703_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v_inst_2717_, lean_object* v_R_2718_, lean_object* v_a_2719_, lean_object* v_b_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2713_, v___y_2714_, v___x_2715_, v___x_2716_, v_a_2719_, v_b_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v_inst_2726_, lean_object* v_R_2727_, lean_object* v_a_2728_, lean_object* v_b_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2722_, v___y_2723_, v___x_2724_, v___x_2725_, v_inst_2726_, v_R_2727_, v_a_2728_, v_b_2729_);
lean_dec_ref(v___x_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2731_, lean_object* v_pos_2732_){
_start:
{
lean_object* v_str_2733_; lean_object* v_startInclusive_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v_decide_2738_; 
v_str_2733_ = lean_ctor_get(v_s_2731_, 0);
v_startInclusive_2734_ = lean_ctor_get(v_s_2731_, 1);
v___x_2735_ = lean_nat_add(v_startInclusive_2734_, v_pos_2732_);
v___x_2736_ = lean_nat_sub(v___x_2735_, v_startInclusive_2734_);
v___x_2737_ = lean_unsigned_to_nat(0u);
v_decide_2738_ = lean_nat_dec_eq(v___x_2736_, v___x_2737_);
if (v_decide_2738_ == 0)
{
uint32_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint32_t v___x_2745_; uint8_t v___x_2746_; 
v___x_2739_ = 10;
lean_inc(v_startInclusive_2734_);
lean_inc_ref(v_str_2733_);
v___x_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2740_, 0, v_str_2733_);
lean_ctor_set(v___x_2740_, 1, v_startInclusive_2734_);
lean_ctor_set(v___x_2740_, 2, v___x_2735_);
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_nat_sub(v___x_2736_, v___x_2741_);
lean_dec(v___x_2736_);
v___x_2743_ = l_String_Slice_posLE(v___x_2740_, v___x_2742_);
lean_dec_ref_known(v___x_2740_, 3);
v___x_2744_ = lean_nat_add(v_startInclusive_2734_, v___x_2743_);
v___x_2745_ = lean_string_utf8_get_fast(v_str_2733_, v___x_2744_);
lean_dec(v___x_2744_);
v___x_2746_ = lean_uint32_dec_eq(v___x_2745_, v___x_2739_);
if (v___x_2746_ == 0)
{
lean_dec(v___x_2743_);
return v_pos_2732_;
}
else
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = lean_nat_add(v___x_2743_, v___x_2741_);
v___x_2748_ = lean_nat_dec_le(v___x_2747_, v_pos_2732_);
lean_dec(v___x_2747_);
if (v___x_2748_ == 0)
{
lean_dec(v___x_2743_);
return v_pos_2732_;
}
else
{
lean_dec(v_pos_2732_);
v_pos_2732_ = v___x_2743_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2736_);
lean_dec(v___x_2735_);
return v_pos_2732_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2750_, lean_object* v_pos_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2750_, v_pos_2751_);
lean_dec_ref(v_s_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2755_ = lean_string_utf8_byte_size(v_s_2753_);
v___x_2756_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_2757_ = lean_nat_dec_le(v___x_2756_, v___x_2755_);
if (v___x_2757_ == 0)
{
return v_s_2753_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_nat_sub(v___x_2755_, v___x_2756_);
v___x_2760_ = lean_string_memcmp(v_s_2753_, v___x_2754_, v___x_2759_, v___x_2758_, v___x_2756_);
lean_dec(v___x_2759_);
if (v___x_2760_ == 0)
{
return v_s_2753_;
}
else
{
uint32_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2761_ = 10;
lean_inc_ref(v_s_2753_);
v___x_2762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2762_, 0, v_s_2753_);
lean_ctor_set(v___x_2762_, 1, v___x_2758_);
lean_ctor_set(v___x_2762_, 2, v___x_2755_);
v___x_2763_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2762_, v___x_2755_);
lean_dec_ref_known(v___x_2762_, 3);
v___x_2764_ = lean_string_utf8_extract_fast(v_s_2753_, v___x_2758_, v___x_2763_);
lean_dec(v___x_2763_);
lean_dec_ref(v_s_2753_);
v___x_2765_ = lean_string_push(v___x_2764_, v___x_2761_);
return v___x_2765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2766_, uint8_t v_alternate_2767_){
_start:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_snd_2773_; 
v___x_2768_ = lean_box(0);
v___x_2769_ = 0;
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2772_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2766_, v___x_2768_, v___x_2769_, v_alternate_2767_, v___x_2770_, v___x_2771_);
v_snd_2773_ = lean_ctor_get(v___x_2772_, 1);
lean_inc(v_snd_2773_);
lean_dec_ref(v___x_2772_);
return v_snd_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2774_, lean_object* v_alternate_2775_){
_start:
{
uint8_t v_alternate_boxed_2776_; lean_object* v_res_2777_; 
v_alternate_boxed_2776_ = lean_unbox(v_alternate_2775_);
v_res_2777_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2774_, v_alternate_boxed_2776_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2778_, uint8_t v_alternate_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2778_, v_alternate_2779_);
v___x_2781_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2782_, lean_object* v_alternate_2783_){
_start:
{
uint8_t v_alternate_boxed_2784_; lean_object* v_res_2785_; 
v_alternate_boxed_2784_ = lean_unbox(v_alternate_2783_);
v_res_2785_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2782_, v_alternate_boxed_2784_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v___x_2788_; 
lean_inc(v_b_2786_);
v___x_2788_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2786_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; uint8_t v___y_2791_; 
lean_inc(v_b_2786_);
v___x_2789_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2787_, v_b_2786_);
lean_dec(v___y_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
v___y_2791_ = v___x_2788_;
goto v___jp_2790_;
}
else
{
lean_object* v_val_2794_; uint8_t v_alternate_2795_; 
v_val_2794_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_val_2794_);
v_alternate_2795_ = lean_ctor_get_uint8(v_val_2794_, 1);
lean_dec(v_val_2794_);
v___y_2791_ = v_alternate_2795_;
goto v___jp_2790_;
}
v___jp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2786_, v___y_2791_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___x_2789_);
return v___x_2793_;
}
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec(v_b_2786_);
v___x_2796_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v___y_2787_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2798_, lean_object* v_f_2799_, lean_object* v_xs_2800_, lean_object* v_k_2801_, lean_object* v_acc_2802_, lean_object* v___y_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_nat_dec_lt(v_k_2801_, v_n_2798_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec(v_k_2801_);
lean_dec_ref(v_f_2799_);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v_acc_2802_);
lean_ctor_set(v___x_2805_, 1, v___y_2803_);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v_fst_2808_; lean_object* v_snd_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2806_ = lean_array_fget_borrowed(v_xs_2800_, v_k_2801_);
lean_inc_ref(v_f_2799_);
lean_inc(v___x_2806_);
v___x_2807_ = lean_apply_2(v_f_2799_, v___x_2806_, v___y_2803_);
v_fst_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_fst_2808_);
v_snd_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_snd_2809_);
lean_dec_ref(v___x_2807_);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = lean_nat_add(v_k_2801_, v___x_2810_);
lean_dec(v_k_2801_);
v___x_2812_ = lean_array_push(v_acc_2802_, v_fst_2808_);
v_k_2801_ = v___x_2811_;
v_acc_2802_ = v___x_2812_;
v___y_2803_ = v_snd_2809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2814_, lean_object* v_f_2815_, lean_object* v_xs_2816_, lean_object* v_k_2817_, lean_object* v_acc_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2814_, v_f_2815_, v_xs_2816_, v_k_2817_, v_acc_2818_, v___y_2819_);
lean_dec_ref(v_xs_2816_);
lean_dec(v_n_2814_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2822_){
_start:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_fst_2829_; 
v___f_2823_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2824_ = lean_array_get_size(v_blocks_2822_);
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0));
v___x_2827_ = lean_box(0);
v___x_2828_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2824_, v___f_2823_, v_blocks_2822_, v___x_2825_, v___x_2826_, v___x_2827_);
v_fst_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_fst_2829_);
lean_dec_ref(v___x_2828_);
return v_fst_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2830_);
lean_dec_ref(v_blocks_2830_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2832_, lean_object* v_00_u03b2_2833_, lean_object* v_n_2834_, lean_object* v_f_2835_, lean_object* v_xs_2836_, lean_object* v_k_2837_, lean_object* v_h_2838_, lean_object* v_acc_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2834_, v_f_2835_, v_xs_2836_, v_k_2837_, v_acc_2839_, v___y_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_n_2844_, lean_object* v_f_2845_, lean_object* v_xs_2846_, lean_object* v_k_2847_, lean_object* v_h_2848_, lean_object* v_acc_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2842_, v_00_u03b2_2843_, v_n_2844_, v_f_2845_, v_xs_2846_, v_k_2847_, v_h_2848_, v_acc_2849_, v___y_2850_);
lean_dec_ref(v_xs_2846_);
lean_dec(v_n_2844_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2852_, size_t v_i_2853_, size_t v_stop_2854_, lean_object* v_b_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_eq(v_i_2853_, v_stop_2854_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; 
v___x_2857_ = lean_array_uget_borrowed(v_as_2852_, v_i_2853_);
v___x_2858_ = lean_string_append(v_b_2855_, v___x_2857_);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_i_2853_, v___x_2859_);
v_i_2853_ = v___x_2860_;
v_b_2855_ = v___x_2858_;
goto _start;
}
else
{
return v_b_2855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2862_, lean_object* v_i_2863_, lean_object* v_stop_2864_, lean_object* v_b_2865_){
_start:
{
size_t v_i_boxed_2866_; size_t v_stop_boxed_2867_; lean_object* v_res_2868_; 
v_i_boxed_2866_ = lean_unbox_usize(v_i_2863_);
lean_dec(v_i_2863_);
v_stop_boxed_2867_ = lean_unbox_usize(v_stop_2864_);
lean_dec(v_stop_2864_);
v_res_2868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2862_, v_i_boxed_2866_, v_stop_boxed_2867_, v_b_2865_);
lean_dec_ref(v_as_2862_);
return v_res_2868_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2870_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2871_){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2873_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2871_);
v___x_2874_ = lean_unsigned_to_nat(0u);
v___x_2875_ = lean_array_get_size(v___x_2873_);
v___x_2876_ = lean_nat_dec_lt(v___x_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref(v___x_2873_);
v___x_2877_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2877_;
}
else
{
size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = lean_usize_of_nat(v___x_2875_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2873_, v___x_2878_, v___x_2879_, v___x_2872_);
lean_dec_ref(v___x_2873_);
v___x_2881_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2880_);
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2882_);
lean_dec_ref(v_blocks_2882_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; lean_object* v_stxTrav_2887_; lean_object* v_cur_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_st_ref_get(v___y_2884_);
v_stxTrav_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc_ref(v_stxTrav_2887_);
lean_dec(v___x_2886_);
v_cur_2888_ = lean_ctor_get(v_stxTrav_2887_, 0);
lean_inc(v_cur_2888_);
lean_dec_ref(v_stxTrav_2887_);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_cur_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2890_);
lean_dec(v___y_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2894_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; lean_object* v_stxTrav_2908_; lean_object* v_leadWord_2909_; uint8_t v_leadWordIdent_2910_; uint8_t v_isUngrouped_2911_; uint8_t v_mustBeGrouped_2912_; lean_object* v_stack_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2924_; 
v___x_2907_ = lean_st_ref_take(v___y_2905_);
v_stxTrav_2908_ = lean_ctor_get(v___x_2907_, 0);
v_leadWord_2909_ = lean_ctor_get(v___x_2907_, 1);
v_leadWordIdent_2910_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*3);
v_isUngrouped_2911_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2912_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*3 + 2);
v_stack_2913_ = lean_ctor_get(v___x_2907_, 2);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2915_ = v___x_2907_;
v_isShared_2916_ = v_isSharedCheck_2924_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_stack_2913_);
lean_inc(v_leadWord_2909_);
lean_inc(v_stxTrav_2908_);
lean_dec(v___x_2907_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2924_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2917_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2908_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2917_);
v___x_2919_ = v___x_2915_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_leadWord_2909_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_stack_2913_);
lean_ctor_set_uint8(v_reuseFailAlloc_2923_, sizeof(void*)*3, v_leadWordIdent_2910_);
lean_ctor_set_uint8(v_reuseFailAlloc_2923_, sizeof(void*)*3 + 1, v_isUngrouped_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2923_, sizeof(void*)*3 + 2, v_mustBeGrouped_2912_);
v___x_2919_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_st_ref_put(v___y_2905_, v___x_2919_);
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2925_);
lean_dec(v___y_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2929_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2940_, lean_object* v___x_2941_, lean_object* v_rendered_2942_, lean_object* v_a_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_nat_dec_lt(v_a_2943_, v_upperBound_2940_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_a_2943_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_b_2944_);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; lean_object* v___y_2954_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2952_ = lean_box(0);
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_sub(v___x_2941_, v___x_2961_);
v___x_2963_ = lean_nat_sub(v___x_2962_, v_a_2943_);
lean_dec(v___x_2962_);
v___x_2964_ = lean_array_fget_borrowed(v_rendered_2942_, v___x_2963_);
lean_dec(v___x_2963_);
v___x_2965_ = lean_nat_dec_eq(v_a_2943_, v___x_2960_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_inc(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
v___y_2954_ = v___x_2966_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_inc(v___x_2964_);
v___x_2967_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2964_);
v___x_2968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___y_2954_ = v___x_2968_;
goto v___jp_2953_;
}
v___jp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_2954_, v___y_2946_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; 
lean_dec_ref_known(v___x_2955_, 1);
v___x_2956_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2946_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec_ref_known(v___x_2956_, 1);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_add(v_a_2943_, v___x_2957_);
lean_dec(v_a_2943_);
v_a_2943_ = v___x_2958_;
v_b_2944_ = v___x_2952_;
goto _start;
}
else
{
lean_dec(v_a_2943_);
return v___x_2956_;
}
}
else
{
lean_dec(v_a_2943_);
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_2969_, lean_object* v___x_2970_, lean_object* v_rendered_2971_, lean_object* v_a_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2969_, v___x_2970_, v_rendered_2971_, v_a_2972_, v_b_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_rendered_2971_);
lean_dec(v___x_2970_);
lean_dec(v_upperBound_2969_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_2980_, lean_object* v_rendered_2981_, lean_object* v___x_2982_, lean_object* v___x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_2980_, v___x_2980_, v_rendered_2981_, v___x_2982_, v___x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2989_, 0);
lean_dec(v_unused_2997_);
v___x_2991_ = v___x_2989_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v___x_2989_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2983_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2983_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_2998_, lean_object* v_rendered_2999_, lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_2998_, v_rendered_2999_, v___x_3000_, v___x_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_rendered_2999_);
lean_dec(v___x_2998_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_a_3014_; lean_object* v_blocks_3015_; lean_object* v_rendered_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3013_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_3009_);
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v_blocks_3015_ = l_Lean_TSyntax_getVersoBlocks(v_a_3014_);
lean_dec(v_a_3014_);
v_rendered_3016_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_3015_);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = lean_array_get_size(v_blocks_3015_);
lean_dec_ref(v_blocks_3015_);
v___x_3019_ = lean_box(0);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3020_, 0, v___x_3018_);
lean_closure_set(v___f_3020_, 1, v_rendered_3016_);
lean_closure_set(v___f_3020_, 2, v___x_3017_);
lean_closure_set(v___f_3020_, 3, v___x_3019_);
v___x_3021_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_3021_, 0, v___f_3020_);
v___x_3022_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3021_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___f_3035_; lean_object* v___x_3036_; 
v___f_3035_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3036_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3035_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Doc_Parser_document_formatter(v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3043_, lean_object* v___x_3044_, lean_object* v_rendered_3045_, lean_object* v_inst_3046_, lean_object* v_R_3047_, lean_object* v_a_3048_, lean_object* v_b_3049_, lean_object* v_c_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3043_, v___x_3044_, v_rendered_3045_, v_a_3048_, v_b_3049_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3057_, lean_object* v___x_3058_, lean_object* v_rendered_3059_, lean_object* v_inst_3060_, lean_object* v_R_3061_, lean_object* v_a_3062_, lean_object* v_b_3063_, lean_object* v_c_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3057_, v___x_3058_, v_rendered_3059_, v_inst_3060_, v_R_3061_, v_a_3062_, v_b_3063_, v_c_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_rendered_3059_);
lean_dec(v___x_3058_);
lean_dec(v_upperBound_3057_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3088_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3089_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3090_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3091_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3092_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3094_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1);
res = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* initialize_Lean_DocString_View(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Formatter(builtin);
}
#ifdef __cplusplus
}
#endif

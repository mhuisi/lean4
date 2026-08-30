// Lean compiler output
// Module: Lean.Fmt.FmtM.Comments
// Imports: public import Lean.Syntax public import Lean.Fmt.FmtM.Error public import Lean.Fmt.Util.Basic import Lean.Fmt.Util.RangeTree import Init.Data.String.Search import Init.Control.Basic public import Lean.Fmt.FmtM.LineInfo
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_instOrdRaw__lean_ord(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Range_bsize(lean_object*);
uint64_t l_instHashableSubslice__lean_hash___redArg(lean_object*);
uint8_t l_instBEqSubslice__lean_beq___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_compareRanges(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
uint8_t l_instOrdPos__lean_ord___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_instHashablePos__lean_hash___redArg(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_String_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_instInhabitedSubslice(lean_object*);
lean_object* l_Lean_Fmt_binSearchLeftmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqSubslice__lean_beq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableSubslice__lean_hash___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_collectLineInfos(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashablePos__lean_hash___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_instInhabitedLineInfo_default(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object*);
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__8_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__String_indent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__String_indent___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__String_indent___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__String_indent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedWhitespace_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedWhitespace;
static const lean_string_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Fmt.Comment.Whitespace.leading"};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Fmt.Comment.Whitespace.trailing"};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4;
static lean_once_cell_t l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprWhitespace = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedPlacement_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedPlacement;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instBEqPlacement___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instBEqPlacement = (const lean_object*)&l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Fmt.Comment.Placement.afterToken"};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Fmt.Comment.Placement.onLineBeforeToken"};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprPlacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprPlacement_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprPlacement = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedKind;
static const lean_string_object l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Fmt.Comment.Kind.lineComment"};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Fmt.Comment.Kind.blockComment"};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprKind___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprKind = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/-"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___boxed(lean_object*);
static const lean_array_object l_Lean_Fmt_instInhabitedComment_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedComment_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedComment_default___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_instInhabitedComment_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedComment_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedComment_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedComment;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprComment_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "placement"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__10;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "originalTokenRange"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__13;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "originalWhitespaceRange"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__16;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "originalWhitespaceKind"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__19;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__22;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__24;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__25;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__23_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprComment_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprComment___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprComment___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprComment = (const lean_object*)&l_Lean_Fmt_instReprComment___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instInhabitedRendering_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Comment_instInhabitedRendering_default___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instInhabitedRendering_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instInhabitedRendering_default = (const lean_object*)&l_Lean_Fmt_Comment_instInhabitedRendering_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instInhabitedRendering = (const lean_object*)&l_Lean_Fmt_Comment_instInhabitedRendering_default___closed__0_value;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-- "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Comment_render___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/-\n"};
static const lean_object* l_Lean_Fmt_Comment_render___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_render___closed__0_value;
static const lean_string_object l_Lean_Fmt_Comment_render___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n-/"};
static const lean_object* l_Lean_Fmt_Comment_render___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_render___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_render___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/- "};
static const lean_object* l_Lean_Fmt_Comment_render___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_render___closed__2_value;
static const lean_string_object l_Lean_Fmt_Comment_render___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " -/"};
static const lean_object* l_Lean_Fmt_Comment_render___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_render___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_render(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements(lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedPendingComment_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedPendingComment_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPendingComment_default;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instInhabitedPendingComment;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toComment"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__4_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "startColumnOffset"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__7_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "startPos"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__13_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__14 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "endPos"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__15 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__15_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__16 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0 = (const lean_object*)&l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryNestComment(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_skip(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__0_value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__0_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_parseComments(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_parseComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "substring is invalid and cannot be converted to a slice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 141, .m_capacity = 141, .m_length = 140, .m_data = "Input syntax to the formatter is malformed: substring is invalid and cannot be converted to a slice. Offending portion of the input syntax: "};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_collectComments___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_collectComments___closed__0;
static lean_once_cell_t l_Lean_Fmt_collectComments___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_collectComments___closed__1;
static lean_once_cell_t l_Lean_Fmt_collectComments___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_collectComments___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_collectComments(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_collectComments___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__0_value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__6_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Fmt.FmtM.Comments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Fmt.FmtM.Comments.0.Lean.Fmt.determineCommentInsertions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: ! isFinalAlternative\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1;
LEAN_EXPORT uint32_t l_panic___at___00Lean_Fmt_insertComments_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_insertComments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_insertComments___closed__0 = (const lean_object*)&l_Lean_Fmt_insertComments___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_insertComments(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_insertComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1);
v___x_6_ = lean_nat_dec_eq(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3);
v___x_12_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__4);
v___x_15_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__3);
v___x_16_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__5);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(lean_object* v_s_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__2);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__6);
return v___x_27_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__8));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___boxed(lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(v_s_29_);
lean_dec_ref(v_s_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__0(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_zero_33_; uint8_t v_isZero_34_; 
v_zero_33_ = lean_unsigned_to_nat(0u);
v_isZero_34_ = lean_nat_dec_eq(v_x_31_, v_zero_33_);
if (v_isZero_34_ == 1)
{
lean_dec(v_x_31_);
return v_x_32_;
}
else
{
uint32_t v___x_35_; lean_object* v_one_36_; lean_object* v_n_37_; lean_object* v___x_38_; 
v___x_35_ = 32;
v_one_36_ = lean_unsigned_to_nat(1u);
v_n_37_ = lean_nat_sub(v_x_31_, v_one_36_);
lean_dec(v_x_31_);
v___x_38_ = lean_string_push(v_x_32_, v___x_35_);
v_x_31_ = v_n_37_;
v_x_32_ = v___x_38_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg(lean_object* v_numSpaces_41_, lean_object* v_s_42_, lean_object* v___x_43_, lean_object* v___x_44_, lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
lean_object* v_it_48_; lean_object* v_startInclusive_49_; lean_object* v_endExclusive_50_; 
if (lean_obj_tag(v_a_45_) == 0)
{
lean_object* v_currPos_58_; lean_object* v_searcher_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_163_; 
v_currPos_58_ = lean_ctor_get(v_a_45_, 0);
v_searcher_59_ = lean_ctor_get(v_a_45_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_45_);
if (v_isSharedCheck_163_ == 0)
{
v___x_61_ = v_a_45_;
v_isShared_62_ = v_isSharedCheck_163_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_searcher_59_);
lean_inc(v_currPos_58_);
lean_dec(v_a_45_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_163_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_it_64_; lean_object* v_it_70_; lean_object* v_startPos_71_; lean_object* v_endPos_72_; 
switch(lean_obj_tag(v_searcher_59_))
{
case 0:
{
lean_object* v_pos_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_97_; 
lean_del_object(v___x_61_);
v_pos_85_ = lean_ctor_get(v_searcher_59_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_searcher_59_);
if (v_isSharedCheck_97_ == 0)
{
v___x_87_ = v_searcher_59_;
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_pos_85_);
lean_dec(v_searcher_59_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_startInclusive_89_; lean_object* v_endExclusive_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_startInclusive_89_ = lean_ctor_get(v___x_43_, 1);
v_endExclusive_90_ = lean_ctor_get(v___x_43_, 2);
v___x_91_ = lean_nat_sub(v_endExclusive_90_, v_startInclusive_89_);
v___x_92_ = lean_nat_dec_eq(v_pos_85_, v___x_91_);
lean_dec(v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_94_; 
lean_inc(v_pos_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_pos_85_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_inc(v_pos_85_);
v_it_70_ = v___x_94_;
v_startPos_71_ = v_pos_85_;
v_endPos_72_ = v_pos_85_;
goto v___jp_69_;
}
}
else
{
lean_object* v___x_96_; 
lean_del_object(v___x_87_);
v___x_96_ = lean_box(3);
lean_inc(v_pos_85_);
v_it_70_ = v___x_96_;
v_startPos_71_ = v_pos_85_;
v_endPos_72_ = v_pos_85_;
goto v___jp_69_;
}
}
}
case 1:
{
lean_object* v_pos_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_pos_98_ = lean_ctor_get(v_searcher_59_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_searcher_59_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v_searcher_59_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_pos_98_);
lean_dec(v_searcher_59_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_string_utf8_next_fast(v_s_42_, v_pos_98_);
lean_dec(v_pos_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
v_it_64_ = v___x_104_;
goto v___jp_63_;
}
}
}
case 2:
{
lean_object* v_needle_107_; lean_object* v_table_108_; lean_object* v_stackPos_109_; lean_object* v_needlePos_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_162_; 
v_needle_107_ = lean_ctor_get(v_searcher_59_, 0);
v_table_108_ = lean_ctor_get(v_searcher_59_, 1);
v_stackPos_109_ = lean_ctor_get(v_searcher_59_, 2);
v_needlePos_110_ = lean_ctor_get(v_searcher_59_, 3);
v_isSharedCheck_162_ = !lean_is_exclusive(v_searcher_59_);
if (v_isSharedCheck_162_ == 0)
{
v___x_112_ = v_searcher_59_;
v_isShared_113_ = v_isSharedCheck_162_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_needlePos_110_);
lean_inc(v_stackPos_109_);
lean_inc(v_table_108_);
lean_inc(v_needle_107_);
lean_dec(v_searcher_59_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_162_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_str_114_; lean_object* v_startInclusive_115_; lean_object* v_endExclusive_116_; lean_object* v_basePos_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_str_114_ = lean_ctor_get(v_needle_107_, 0);
v_startInclusive_115_ = lean_ctor_get(v_needle_107_, 1);
v_endExclusive_116_ = lean_ctor_get(v_needle_107_, 2);
v_basePos_117_ = lean_nat_sub(v_stackPos_109_, v_needlePos_110_);
v___x_118_ = lean_nat_sub(v_endExclusive_116_, v_startInclusive_115_);
v___x_119_ = lean_nat_add(v_basePos_117_, v___x_118_);
v___x_120_ = lean_nat_dec_le(v___x_119_, v___x_44_);
lean_dec(v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
lean_dec(v___x_118_);
lean_del_object(v___x_112_);
lean_dec(v_needlePos_110_);
lean_dec(v_stackPos_109_);
lean_dec_ref(v_table_108_);
lean_dec_ref(v_needle_107_);
v___x_121_ = lean_nat_dec_lt(v_basePos_117_, v___x_44_);
lean_dec(v_basePos_117_);
if (v___x_121_ == 0)
{
lean_del_object(v___x_61_);
goto v___jp_83_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(3);
v_it_64_ = v___x_122_;
goto v___jp_63_;
}
}
else
{
uint8_t v_stackByte_123_; lean_object* v___x_124_; uint8_t v_patByte_125_; uint8_t v___x_126_; 
lean_dec(v_basePos_117_);
lean_inc(v_stackPos_109_);
v_stackByte_123_ = lean_string_get_byte_fast(v_s_42_, v_stackPos_109_);
v___x_124_ = lean_nat_add(v_startInclusive_115_, v_needlePos_110_);
v_patByte_125_ = lean_string_get_byte_fast(v_str_114_, v___x_124_);
v___x_126_ = lean_uint8_dec_eq(v_stackByte_123_, v_patByte_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
lean_dec(v___x_118_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_nat_dec_eq(v_needlePos_110_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_newNeedlePos_131_; uint8_t v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_sub(v_needlePos_110_, v___x_129_);
lean_dec(v_needlePos_110_);
v_newNeedlePos_131_ = lean_array_fget_borrowed(v_table_108_, v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_dec_eq(v_newNeedlePos_131_, v___x_127_);
if (v___x_132_ == 0)
{
lean_object* v___x_134_; 
lean_inc(v_newNeedlePos_131_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v_newNeedlePos_131_);
v___x_134_ = v___x_112_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_needle_107_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_table_108_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_stackPos_109_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_newNeedlePos_131_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v_it_64_ = v___x_134_;
goto v___jp_63_;
}
}
else
{
lean_object* v_nextStackPos_136_; lean_object* v___x_138_; 
v_nextStackPos_136_ = l_String_Slice_posGE___redArg(v___x_43_, v_stackPos_109_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v___x_127_);
lean_ctor_set(v___x_112_, 2, v_nextStackPos_136_);
v___x_138_ = v___x_112_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_needle_107_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_table_108_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_nextStackPos_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v___x_127_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v_it_64_ = v___x_138_;
goto v___jp_63_;
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_nextStackPos_142_; lean_object* v___x_144_; 
lean_dec(v_needlePos_110_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_stackPos_109_, v___x_140_);
lean_dec(v_stackPos_109_);
v_nextStackPos_142_ = l_String_Slice_posGE___redArg(v___x_43_, v___x_141_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v___x_127_);
lean_ctor_set(v___x_112_, 2, v_nextStackPos_142_);
v___x_144_ = v___x_112_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_needle_107_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_table_108_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_nextStackPos_142_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v___x_127_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v_it_64_ = v___x_144_;
goto v___jp_63_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v_nextStackPos_147_; lean_object* v_nextNeedlePos_148_; uint8_t v___x_149_; 
lean_del_object(v___x_61_);
v___x_146_ = lean_unsigned_to_nat(1u);
v_nextStackPos_147_ = lean_nat_add(v_stackPos_109_, v___x_146_);
lean_dec(v_stackPos_109_);
v_nextNeedlePos_148_ = lean_nat_add(v_needlePos_110_, v___x_146_);
lean_dec(v_needlePos_110_);
v___x_149_ = lean_nat_dec_eq(v_nextNeedlePos_148_, v___x_118_);
lean_dec(v___x_118_);
if (v___x_149_ == 0)
{
lean_object* v___x_151_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v_nextNeedlePos_148_);
lean_ctor_set(v___x_112_, 2, v_nextStackPos_147_);
v___x_151_ = v___x_112_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_needle_107_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_table_108_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_nextStackPos_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_nextNeedlePos_148_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_currPos_58_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v_a_45_ = v___x_152_;
goto _start;
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_155_ = lean_nat_sub(v_nextStackPos_147_, v_nextNeedlePos_148_);
lean_dec(v_nextNeedlePos_148_);
v___x_156_ = l_String_Slice_pos_x21(v___x_43_, v___x_155_);
lean_dec(v___x_155_);
v___x_157_ = l_String_Slice_pos_x21(v___x_43_, v_nextStackPos_147_);
v___x_158_ = lean_unsigned_to_nat(0u);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v___x_158_);
lean_ctor_set(v___x_112_, 2, v_nextStackPos_147_);
v___x_160_ = v___x_112_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_needle_107_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_table_108_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_nextStackPos_147_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_it_70_ = v___x_160_;
v_startPos_71_ = v___x_156_;
v_endPos_72_ = v___x_157_;
goto v___jp_69_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_61_);
goto v___jp_83_;
}
}
v___jp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_it_64_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_currPos_58_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_it_64_);
v___x_66_ = v_reuseFailAlloc_68_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
v_a_45_ = v___x_66_;
goto _start;
}
}
v___jp_69_:
{
lean_object* v_slice_73_; lean_object* v_startInclusive_74_; lean_object* v_endExclusive_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_slice_73_ = l_String_Slice_subslice_x21(v___x_43_, v_currPos_58_, v_startPos_71_);
v_startInclusive_74_ = lean_ctor_get(v_slice_73_, 0);
v_endExclusive_75_ = lean_ctor_get(v_slice_73_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_slice_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v_slice_73_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_endExclusive_75_);
lean_inc(v_startInclusive_74_);
lean_dec(v_slice_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_nextIt_80_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v_it_70_);
lean_ctor_set(v___x_77_, 0, v_endPos_72_);
v_nextIt_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_endPos_72_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_it_70_);
v_nextIt_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v_it_48_ = v_nextIt_80_;
v_startInclusive_49_ = v_startInclusive_74_;
v_endExclusive_50_ = v_endExclusive_75_;
goto v___jp_47_;
}
}
}
v___jp_83_:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(1);
lean_inc(v___x_44_);
v_it_48_ = v___x_84_;
v_startInclusive_49_ = v_currPos_58_;
v_endExclusive_50_ = v___x_44_;
goto v___jp_47_;
}
}
}
else
{
lean_dec(v___x_44_);
lean_dec_ref(v_s_42_);
lean_dec(v_numSpaces_41_);
return v_b_46_;
}
v___jp_47_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_inc_ref(v_s_42_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_s_42_);
lean_ctor_set(v___x_51_, 1, v_startInclusive_49_);
lean_ctor_set(v___x_51_, 2, v_endExclusive_50_);
v___x_52_ = ((lean_object*)(l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0));
lean_inc(v_numSpaces_41_);
v___x_53_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__0(v_numSpaces_41_, v___x_52_);
v___x_54_ = l_String_Slice_toString(v___x_51_);
lean_dec_ref_known(v___x_51_, 3);
v___x_55_ = lean_string_append(v___x_53_, v___x_54_);
lean_dec_ref(v___x_54_);
v___x_56_ = lean_array_push(v_b_46_, v___x_55_);
v_a_45_ = v_it_48_;
v_b_46_ = v___x_56_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___boxed(lean_object* v_numSpaces_164_, lean_object* v_s_165_, lean_object* v___x_166_, lean_object* v___x_167_, lean_object* v_a_168_, lean_object* v_b_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg(v_numSpaces_164_, v_s_165_, v___x_166_, v___x_167_, v_a_168_, v_b_169_);
lean_dec_ref(v___x_166_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__String_indent(lean_object* v_s_173_, lean_object* v_numSpaces_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_175_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_string_utf8_byte_size(v_s_173_);
lean_inc_ref(v_s_173_);
v___x_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_178_, 0, v_s_173_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
v___x_179_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__String_indent___closed__0));
v___x_181_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg(v_numSpaces_174_, v_s_173_, v___x_178_, v___x_177_, v___x_179_, v___x_180_);
lean_dec_ref_known(v___x_178_, 3);
v___x_182_ = lean_array_to_list(v___x_181_);
v___x_183_ = l_String_intercalate(v___x_175_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2(lean_object* v_numSpaces_184_, lean_object* v_s_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_inst_188_, lean_object* v_R_189_, lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg(v_numSpaces_184_, v_s_185_, v___x_186_, v___x_187_, v_a_190_, v_b_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___boxed(lean_object* v_numSpaces_193_, lean_object* v_s_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v_inst_197_, lean_object* v_R_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2(v_numSpaces_193_, v_s_194_, v___x_195_, v___x_196_, v_inst_197_, v_R_198_, v_a_199_, v_b_200_);
lean_dec_ref(v___x_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx(uint8_t v_x_202_){
_start:
{
if (v_x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_unsigned_to_nat(0u);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(1u);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___boxed(lean_object* v_x_205_){
_start:
{
uint8_t v_x_boxed_206_; lean_object* v_res_207_; 
v_x_boxed_206_ = lean_unbox(v_x_205_);
v_res_207_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx(v_x_boxed_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object* v_k_208_){
_start:
{
lean_inc(v_k_208_);
return v_k_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(v_k_209_);
lean_dec(v_k_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, uint8_t v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
lean_inc(v_k_215_);
return v_k_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object* v_motive_216_, lean_object* v_ctorIdx_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_k_220_){
_start:
{
uint8_t v_t_boxed_221_; lean_object* v_res_222_; 
v_t_boxed_221_ = lean_unbox(v_t_218_);
v_res_222_ = l_Lean_Fmt_Comment_Whitespace_ctorElim(v_motive_216_, v_ctorIdx_217_, v_t_boxed_221_, v_h_219_, v_k_220_);
lean_dec(v_k_220_);
lean_dec(v_ctorIdx_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object* v_leading_223_){
_start:
{
lean_inc(v_leading_223_);
return v_leading_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object* v_leading_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(v_leading_224_);
lean_dec(v_leading_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object* v_motive_226_, uint8_t v_t_227_, lean_object* v_h_228_, lean_object* v_leading_229_){
_start:
{
lean_inc(v_leading_229_);
return v_leading_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_leading_233_){
_start:
{
uint8_t v_t_boxed_234_; lean_object* v_res_235_; 
v_t_boxed_234_ = lean_unbox(v_t_231_);
v_res_235_ = l_Lean_Fmt_Comment_Whitespace_leading_elim(v_motive_230_, v_t_boxed_234_, v_h_232_, v_leading_233_);
lean_dec(v_leading_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object* v_trailing_236_){
_start:
{
lean_inc(v_trailing_236_);
return v_trailing_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object* v_trailing_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(v_trailing_237_);
lean_dec(v_trailing_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object* v_motive_239_, uint8_t v_t_240_, lean_object* v_h_241_, lean_object* v_trailing_242_){
_start:
{
lean_inc(v_trailing_242_);
return v_trailing_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_trailing_246_){
_start:
{
uint8_t v_t_boxed_247_; lean_object* v_res_248_; 
v_t_boxed_247_ = lean_unbox(v_t_244_);
v_res_248_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim(v_motive_243_, v_t_boxed_247_, v_h_245_, v_trailing_246_);
lean_dec(v_trailing_246_);
return v_res_248_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default(void){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace(void){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(2u);
v___x_258_ = lean_nat_to_int(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_to_int(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t v_x_261_, lean_object* v_prec_262_){
_start:
{
lean_object* v___y_264_; lean_object* v___y_271_; 
if (v_x_261_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = lean_nat_dec_le(v___x_277_, v_prec_262_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_264_ = v___x_279_;
goto v___jp_263_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_264_ = v___x_280_;
goto v___jp_263_;
}
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1024u);
v___x_282_ = lean_nat_dec_le(v___x_281_, v_prec_262_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_271_ = v___x_283_;
goto v___jp_270_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_271_ = v___x_284_;
goto v___jp_270_;
}
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_265_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1));
lean_inc(v___y_264_);
v___x_266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_266_, 0, v___y_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = 0;
v___x_268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_267_);
v___x_269_ = l_Repr_addAppParen(v___x_268_, v_prec_262_);
return v___x_269_;
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3));
lean_inc(v___y_271_);
v___x_273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = 0;
v___x_275_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___x_274_);
v___x_276_ = l_Repr_addAppParen(v___x_275_, v_prec_262_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object* v_x_285_, lean_object* v_prec_286_){
_start:
{
uint8_t v_x_121__boxed_287_; lean_object* v_res_288_; 
v_x_121__boxed_287_ = lean_unbox(v_x_285_);
v_res_288_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_x_121__boxed_287_, v_prec_286_);
lean_dec(v_prec_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx(uint8_t v_x_291_){
_start:
{
if (v_x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
return v___x_292_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(1u);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___boxed(lean_object* v_x_294_){
_start:
{
uint8_t v_x_boxed_295_; lean_object* v_res_296_; 
v_x_boxed_295_ = lean_unbox(v_x_294_);
v_res_296_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_x_boxed_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object* v_k_297_){
_start:
{
lean_inc(v_k_297_);
return v_k_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Fmt_Comment_Placement_ctorElim___redArg(v_k_298_);
lean_dec(v_k_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object* v_motive_300_, lean_object* v_ctorIdx_301_, uint8_t v_t_302_, lean_object* v_h_303_, lean_object* v_k_304_){
_start:
{
lean_inc(v_k_304_);
return v_k_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object* v_motive_305_, lean_object* v_ctorIdx_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
uint8_t v_t_boxed_310_; lean_object* v_res_311_; 
v_t_boxed_310_ = lean_unbox(v_t_307_);
v_res_311_ = l_Lean_Fmt_Comment_Placement_ctorElim(v_motive_305_, v_ctorIdx_306_, v_t_boxed_310_, v_h_308_, v_k_309_);
lean_dec(v_k_309_);
lean_dec(v_ctorIdx_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object* v_afterToken_312_){
_start:
{
lean_inc(v_afterToken_312_);
return v_afterToken_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object* v_afterToken_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(v_afterToken_313_);
lean_dec(v_afterToken_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object* v_motive_315_, uint8_t v_t_316_, lean_object* v_h_317_, lean_object* v_afterToken_318_){
_start:
{
lean_inc(v_afterToken_318_);
return v_afterToken_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object* v_motive_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_afterToken_322_){
_start:
{
uint8_t v_t_boxed_323_; lean_object* v_res_324_; 
v_t_boxed_323_ = lean_unbox(v_t_320_);
v_res_324_ = l_Lean_Fmt_Comment_Placement_afterToken_elim(v_motive_319_, v_t_boxed_323_, v_h_321_, v_afterToken_322_);
lean_dec(v_afterToken_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object* v_onLineBeforeToken_325_){
_start:
{
lean_inc(v_onLineBeforeToken_325_);
return v_onLineBeforeToken_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object* v_onLineBeforeToken_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(v_onLineBeforeToken_326_);
lean_dec(v_onLineBeforeToken_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object* v_motive_328_, uint8_t v_t_329_, lean_object* v_h_330_, lean_object* v_onLineBeforeToken_331_){
_start:
{
lean_inc(v_onLineBeforeToken_331_);
return v_onLineBeforeToken_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_onLineBeforeToken_335_){
_start:
{
uint8_t v_t_boxed_336_; lean_object* v_res_337_; 
v_t_boxed_336_ = lean_unbox(v_t_333_);
v_res_337_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(v_motive_332_, v_t_boxed_336_, v_h_334_, v_onLineBeforeToken_335_);
lean_dec(v_onLineBeforeToken_335_);
return v_res_337_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default(void){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement(void){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t v_x_340_, uint8_t v_y_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_x_340_);
v___x_343_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_y_341_);
v___x_344_ = lean_nat_dec_eq(v___x_342_, v___x_343_);
lean_dec(v___x_343_);
lean_dec(v___x_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object* v_x_345_, lean_object* v_y_346_){
_start:
{
uint8_t v_x_17__boxed_347_; uint8_t v_y_18__boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v_x_17__boxed_347_ = lean_unbox(v_x_345_);
v_y_18__boxed_348_ = lean_unbox(v_y_346_);
v_res_349_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_x_17__boxed_347_, v_y_18__boxed_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t v_x_359_, lean_object* v_prec_360_){
_start:
{
lean_object* v___y_362_; lean_object* v___y_369_; 
if (v_x_359_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1024u);
v___x_376_ = lean_nat_dec_le(v___x_375_, v_prec_360_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_362_ = v___x_377_;
goto v___jp_361_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_362_ = v___x_378_;
goto v___jp_361_;
}
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(1024u);
v___x_380_ = lean_nat_dec_le(v___x_379_, v_prec_360_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_369_ = v___x_381_;
goto v___jp_368_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_369_ = v___x_382_;
goto v___jp_368_;
}
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_363_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1));
lean_inc(v___y_362_);
v___x_364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_364_, 0, v___y_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = 0;
v___x_366_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_365_);
v___x_367_ = l_Repr_addAppParen(v___x_366_, v_prec_360_);
return v___x_367_;
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3));
lean_inc(v___y_369_);
v___x_371_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_371_, 0, v___y_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_372_);
v___x_374_ = l_Repr_addAppParen(v___x_373_, v_prec_360_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
uint8_t v_x_117__boxed_385_; lean_object* v_res_386_; 
v_x_117__boxed_385_ = lean_unbox(v_x_383_);
v_res_386_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_x_117__boxed_385_, v_prec_384_);
lean_dec(v_prec_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx(uint8_t v_x_389_){
_start:
{
if (v_x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_unsigned_to_nat(0u);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(1u);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___boxed(lean_object* v_x_392_){
_start:
{
uint8_t v_x_boxed_393_; lean_object* v_res_394_; 
v_x_boxed_393_ = lean_unbox(v_x_392_);
v_res_394_ = l_Lean_Fmt_Comment_Kind_ctorIdx(v_x_boxed_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object* v_k_395_){
_start:
{
lean_inc(v_k_395_);
return v_k_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Fmt_Comment_Kind_ctorElim___redArg(v_k_396_);
lean_dec(v_k_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object* v_motive_398_, lean_object* v_ctorIdx_399_, uint8_t v_t_400_, lean_object* v_h_401_, lean_object* v_k_402_){
_start:
{
lean_inc(v_k_402_);
return v_k_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object* v_motive_403_, lean_object* v_ctorIdx_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_k_407_){
_start:
{
uint8_t v_t_boxed_408_; lean_object* v_res_409_; 
v_t_boxed_408_ = lean_unbox(v_t_405_);
v_res_409_ = l_Lean_Fmt_Comment_Kind_ctorElim(v_motive_403_, v_ctorIdx_404_, v_t_boxed_408_, v_h_406_, v_k_407_);
lean_dec(v_k_407_);
lean_dec(v_ctorIdx_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object* v_lineComment_410_){
_start:
{
lean_inc(v_lineComment_410_);
return v_lineComment_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object* v_lineComment_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(v_lineComment_411_);
lean_dec(v_lineComment_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object* v_motive_413_, uint8_t v_t_414_, lean_object* v_h_415_, lean_object* v_lineComment_416_){
_start:
{
lean_inc(v_lineComment_416_);
return v_lineComment_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_lineComment_420_){
_start:
{
uint8_t v_t_boxed_421_; lean_object* v_res_422_; 
v_t_boxed_421_ = lean_unbox(v_t_418_);
v_res_422_ = l_Lean_Fmt_Comment_Kind_lineComment_elim(v_motive_417_, v_t_boxed_421_, v_h_419_, v_lineComment_420_);
lean_dec(v_lineComment_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object* v_blockComment_423_){
_start:
{
lean_inc(v_blockComment_423_);
return v_blockComment_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object* v_blockComment_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(v_blockComment_424_);
lean_dec(v_blockComment_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object* v_motive_426_, uint8_t v_t_427_, lean_object* v_h_428_, lean_object* v_blockComment_429_){
_start:
{
lean_inc(v_blockComment_429_);
return v_blockComment_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_blockComment_433_){
_start:
{
uint8_t v_t_boxed_434_; lean_object* v_res_435_; 
v_t_boxed_434_ = lean_unbox(v_t_431_);
v_res_435_ = l_Lean_Fmt_Comment_Kind_blockComment_elim(v_motive_430_, v_t_boxed_434_, v_h_432_, v_blockComment_433_);
lean_dec(v_blockComment_433_);
return v_res_435_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind(void){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t v_x_444_, lean_object* v_prec_445_){
_start:
{
lean_object* v___y_447_; lean_object* v___y_454_; 
if (v_x_444_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(1024u);
v___x_461_ = lean_nat_dec_le(v___x_460_, v_prec_445_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_447_ = v___x_462_;
goto v___jp_446_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_447_ = v___x_463_;
goto v___jp_446_;
}
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1024u);
v___x_465_ = lean_nat_dec_le(v___x_464_, v_prec_445_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_454_ = v___x_466_;
goto v___jp_453_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_454_ = v___x_467_;
goto v___jp_453_;
}
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__1));
lean_inc(v___y_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_445_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__3));
lean_inc(v___y_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_445_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object* v_x_468_, lean_object* v_prec_469_){
_start:
{
uint8_t v_x_117__boxed_470_; lean_object* v_res_471_; 
v_x_117__boxed_470_ = lean_unbox(v_x_468_);
v_res_471_ = l_Lean_Fmt_Comment_instReprKind_repr(v_x_117__boxed_470_, v_prec_469_);
lean_dec(v_prec_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(uint8_t v_kind_476_){
_start:
{
if (v_kind_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0));
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__1));
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___boxed(lean_object* v_kind_479_){
_start:
{
uint8_t v_kind_boxed_480_; lean_object* v_res_481_; 
v_kind_boxed_480_ = lean_unbox(v_kind_479_);
v_res_481_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(v_kind_boxed_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(uint8_t v_kind_483_){
_start:
{
if (v_kind_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___closed__0));
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___boxed(lean_object* v_kind_486_){
_start:
{
uint8_t v_kind_boxed_487_; lean_object* v_res_488_; 
v_kind_boxed_487_ = lean_unbox(v_kind_486_);
v_res_488_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(v_kind_boxed_487_);
return v_res_488_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting(uint8_t v_kind_489_){
_start:
{
if (v_kind_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 1;
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting___boxed(lean_object* v_kind_492_){
_start:
{
uint8_t v_kind_boxed_493_; uint8_t v_res_494_; lean_object* v_r_495_; 
v_kind_boxed_493_ = lean_unbox(v_kind_492_);
v_res_494_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting(v_kind_boxed_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f(uint8_t v_kind_498_){
_start:
{
if (v_kind_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___closed__0));
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_box(0);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f___boxed(lean_object* v_kind_501_){
_start:
{
uint8_t v_kind_boxed_502_; lean_object* v_res_503_; 
v_kind_boxed_502_ = lean_unbox(v_kind_501_);
v_res_503_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f(v_kind_boxed_502_);
return v_res_503_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default___closed__1(void){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; 
v___x_506_ = ((lean_object*)(l_Lean_Fmt_instInhabitedComment_default___closed__0));
v___x_507_ = 0;
v___x_508_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_509_ = 0;
v___x_510_ = 0;
v___x_511_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_511_, 0, v___x_508_);
lean_ctor_set(v___x_511_, 1, v___x_508_);
lean_ctor_set(v___x_511_, 2, v___x_506_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*3, v___x_510_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*3 + 1, v___x_509_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*3 + 2, v___x_507_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default(void){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Fmt_instInhabitedComment_default___closed__1, &l_Lean_Fmt_instInhabitedComment_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedComment_default___closed__1);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment(void){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Fmt_instInhabitedComment_default;
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprComment_repr_spec__1(lean_object* v_a_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_nat_to_int(v_a_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_dec(v_x_516_);
return v_x_517_;
}
else
{
lean_object* v_head_519_; lean_object* v_tail_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_531_; 
v_head_519_ = lean_ctor_get(v_x_518_, 0);
v_tail_520_ = lean_ctor_get(v_x_518_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_531_ == 0)
{
v___x_522_ = v_x_518_;
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_tail_520_);
lean_inc(v_head_519_);
lean_dec(v_x_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
lean_inc(v_x_516_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 5);
lean_ctor_set(v___x_522_, 1, v_x_516_);
lean_ctor_set(v___x_522_, 0, v_x_517_);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_x_517_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_x_516_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = l_String_quote(v_head_519_);
v___x_527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v_x_517_ = v___x_528_;
v_x_518_ = v_tail_520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2(lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_dec(v_x_532_);
return v_x_533_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
v_head_535_ = lean_ctor_get(v_x_534_, 0);
v_tail_536_ = lean_ctor_get(v_x_534_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_547_ == 0)
{
v___x_538_ = v_x_534_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_tail_536_);
lean_inc(v_head_535_);
lean_dec(v_x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
lean_inc(v_x_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 5);
lean_ctor_set(v___x_538_, 1, v_x_532_);
lean_ctor_set(v___x_538_, 0, v_x_533_);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_x_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_x_532_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = l_String_quote(v_head_535_);
v___x_543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2_spec__3(v_x_532_, v___x_544_, v_tail_536_);
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object* v___y_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = l_String_quote(v___y_548_);
v___x_550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v___x_553_; 
lean_dec(v_x_552_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v_tail_554_; 
v_tail_554_ = lean_ctor_get(v_x_551_, 1);
if (lean_obj_tag(v_tail_554_) == 0)
{
lean_object* v_head_555_; lean_object* v___x_556_; 
lean_dec(v_x_552_);
v_head_555_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_head_555_);
lean_dec_ref_known(v_x_551_, 2);
v___x_556_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_555_);
return v___x_556_;
}
else
{
lean_object* v_head_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc(v_tail_554_);
v_head_557_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_head_557_);
lean_dec_ref_known(v_x_551_, 2);
v___x_558_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_557_);
v___x_559_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__2(v_x_552_, v___x_558_, v_tail_554_);
return v___x_559_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__0));
v___x_569_ = lean_string_length(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__5);
v___x_571_ = lean_nat_to_int(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object* v_xs_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_array_get_size(v_xs_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_583_ = lean_array_to_list(v_xs_579_);
v___x_584_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__3));
v___x_585_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(v___x_583_, v___x_584_);
v___x_586_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__6);
v___x_587_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__7));
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_585_);
v___x_589_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__8));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_586_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Std_Format_fill(v___x_591_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v_xs_579_);
v___x_593_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__10));
return v___x_593_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(8u);
v___x_608_ = lean_nat_to_int(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(13u);
v___x_613_ = lean_nat_to_int(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(22u);
v___x_618_ = lean_nat_to_int(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(27u);
v___x_623_ = lean_nat_to_int(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(26u);
v___x_628_ = lean_nat_to_int(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(11u);
v___x_633_ = lean_nat_to_int(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__0));
v___x_636_ = lean_string_length(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__24, &l_Lean_Fmt_instReprComment_repr___redArg___closed__24_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__24);
v___x_638_ = lean_nat_to_int(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object* v_x_643_){
_start:
{
uint8_t v_kind_644_; uint8_t v_placement_645_; lean_object* v_originalTokenRange_646_; lean_object* v_originalWhitespaceRange_647_; uint8_t v_originalWhitespaceKind_648_; lean_object* v_content_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_kind_644_ = lean_ctor_get_uint8(v_x_643_, sizeof(void*)*3);
v_placement_645_ = lean_ctor_get_uint8(v_x_643_, sizeof(void*)*3 + 1);
v_originalTokenRange_646_ = lean_ctor_get(v_x_643_, 0);
lean_inc_ref(v_originalTokenRange_646_);
v_originalWhitespaceRange_647_ = lean_ctor_get(v_x_643_, 1);
lean_inc_ref(v_originalWhitespaceRange_647_);
v_originalWhitespaceKind_648_ = lean_ctor_get_uint8(v_x_643_, sizeof(void*)*3 + 2);
v_content_649_ = lean_ctor_get(v_x_643_, 2);
lean_inc_ref(v_content_649_);
lean_dec_ref(v_x_643_);
v___x_650_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__5));
v___x_651_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__6));
v___x_652_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__7, &l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_Fmt_Comment_instReprKind_repr(v_kind_644_, v___x_653_);
v___x_655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_652_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = 0;
v___x_657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*1, v___x_656_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_651_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2));
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_box(1);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__9));
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_650_);
v___x_666_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_667_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_placement_645_, v___x_653_);
v___x_668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_656_);
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_665_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_659_);
v___x_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_661_);
v___x_673_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__12));
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_650_);
v___x_676_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__13, &l_Lean_Fmt_instReprComment_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__13);
v___x_677_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalTokenRange_646_);
v___x_678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v___x_656_);
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_675_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_659_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_661_);
v___x_683_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__15));
v___x_684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_650_);
v___x_686_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__16, &l_Lean_Fmt_instReprComment_repr___redArg___closed__16_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__16);
v___x_687_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalWhitespaceRange_647_);
v___x_688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*1, v___x_656_);
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_685_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_659_);
v___x_692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_661_);
v___x_693_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__18));
v___x_694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_650_);
v___x_696_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__19, &l_Lean_Fmt_instReprComment_repr___redArg___closed__19_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__19);
v___x_697_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_originalWhitespaceKind_648_, v___x_653_);
v___x_698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*1, v___x_656_);
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_695_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_659_);
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_661_);
v___x_703_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__21));
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_650_);
v___x_706_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__22, &l_Lean_Fmt_instReprComment_repr___redArg___closed__22_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__22);
v___x_707_ = l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(v_content_649_);
v___x_708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*1, v___x_656_);
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_705_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__25, &l_Lean_Fmt_instReprComment_repr___redArg___closed__25_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__25);
v___x_712_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__26));
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_710_);
v___x_714_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__27));
v___x_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_711_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*1, v___x_656_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object* v_x_718_, lean_object* v_prec_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Fmt_instReprComment_repr___redArg(v_x_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object* v_x_721_, lean_object* v_prec_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Fmt_instReprComment_repr(v_x_721_, v_prec_722_);
lean_dec(v_prec_722_);
return v_res_723_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(lean_object* v___x_731_, lean_object* v_x_732_, lean_object* v_a_733_, uint8_t v_b_734_){
_start:
{
lean_object* v_startInclusive_735_; lean_object* v_endExclusive_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_startInclusive_735_ = lean_ctor_get(v___x_731_, 1);
v_endExclusive_736_ = lean_ctor_get(v___x_731_, 2);
v___x_737_ = lean_nat_sub(v_endExclusive_736_, v_startInclusive_735_);
v___x_738_ = lean_nat_dec_eq(v_a_733_, v___x_737_);
lean_dec(v___x_737_);
if (v___x_738_ == 0)
{
uint32_t v___x_739_; uint32_t v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_string_utf8_get_fast(v_x_732_, v_a_733_);
v___x_740_ = 45;
v___x_741_ = lean_uint32_dec_eq(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v_a_733_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = lean_string_utf8_next_fast(v_x_732_, v_a_733_);
lean_dec(v_a_733_);
v_a_733_ = v___x_742_;
v_b_734_ = v___x_741_;
goto _start;
}
}
else
{
lean_dec(v_a_733_);
return v_b_734_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg___boxed(lean_object* v___x_744_, lean_object* v_x_745_, lean_object* v_a_746_, lean_object* v_b_747_){
_start:
{
uint8_t v_b_boxed_748_; uint8_t v_res_749_; lean_object* v_r_750_; 
v_b_boxed_748_ = lean_unbox(v_b_747_);
v_res_749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(v___x_744_, v_x_745_, v_a_746_, v_b_boxed_748_);
lean_dec_ref(v_x_745_);
lean_dec_ref(v___x_744_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1(size_t v_sz_752_, size_t v_i_753_, lean_object* v_bs_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_755_ == 0)
{
return v_bs_754_;
}
else
{
lean_object* v_v_756_; lean_object* v___x_757_; lean_object* v_bs_x27_758_; lean_object* v___y_760_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_v_756_ = lean_array_uget(v_bs_754_, v_i_753_);
v___x_757_ = lean_unsigned_to_nat(0u);
v_bs_x27_758_ = lean_array_uset(v_bs_754_, v_i_753_, v___x_757_);
v___x_765_ = lean_string_utf8_byte_size(v_v_756_);
lean_inc(v_v_756_);
v___x_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_766_, 0, v_v_756_);
lean_ctor_set(v___x_766_, 1, v___x_757_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
v___x_767_ = l_String_Slice_positions(v___x_766_);
v___x_768_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(v___x_766_, v_v_756_, v___x_767_, v___x_755_);
lean_dec_ref_known(v___x_766_, 3);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___closed__0));
v___x_770_ = lean_string_append(v___x_769_, v_v_756_);
lean_dec(v_v_756_);
v___y_760_ = v___x_770_;
goto v___jp_759_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__0));
v___x_772_ = lean_string_append(v___x_771_, v_v_756_);
lean_dec(v_v_756_);
v___y_760_ = v___x_772_;
goto v___jp_759_;
}
v___jp_759_:
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_753_, v___x_761_);
v___x_763_ = lean_array_uset(v_bs_x27_758_, v_i_753_, v___y_760_);
v_i_753_ = v___x_762_;
v_bs_754_ = v___x_763_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1___boxed(lean_object* v_sz_773_, lean_object* v_i_774_, lean_object* v_bs_775_){
_start:
{
size_t v_sz_boxed_776_; size_t v_i_boxed_777_; lean_object* v_res_778_; 
v_sz_boxed_776_ = lean_unbox_usize(v_sz_773_);
lean_dec(v_sz_773_);
v_i_boxed_777_ = lean_unbox_usize(v_i_774_);
lean_dec(v_i_774_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1(v_sz_boxed_776_, v_i_boxed_777_, v_bs_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_render(lean_object* v_c_783_){
_start:
{
uint8_t v_kind_784_; 
v_kind_784_ = lean_ctor_get_uint8(v_c_783_, sizeof(void*)*3);
if (v_kind_784_ == 0)
{
lean_object* v_content_785_; size_t v_sz_786_; size_t v___x_787_; lean_object* v_lines_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_content_785_ = lean_ctor_get(v_c_783_, 2);
lean_inc_ref(v_content_785_);
lean_dec_ref(v_c_783_);
v_sz_786_ = lean_array_size(v_content_785_);
v___x_787_ = ((size_t)0ULL);
v_lines_788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Comment_render_spec__1(v_sz_786_, v___x_787_, v_content_785_);
v___x_789_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
lean_inc_ref(v_lines_788_);
v___x_790_ = lean_array_to_list(v_lines_788_);
v___x_791_ = l_String_intercalate(v___x_789_, v___x_790_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_array_get_size(v_lines_788_);
lean_dec_ref(v_lines_788_);
v___x_794_ = lean_nat_dec_lt(v___x_792_, v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_795_, 0, v___x_791_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*1, v___x_794_);
v___x_796_ = lean_mk_empty_array_with_capacity(v___x_792_);
v___x_797_ = lean_array_push(v___x_796_, v___x_795_);
return v___x_797_;
}
else
{
lean_object* v_content_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___y_807_; uint8_t v___x_828_; 
v_content_798_ = lean_ctor_get(v_c_783_, 2);
lean_inc_ref(v_content_798_);
lean_dec_ref(v_c_783_);
v___x_799_ = ((lean_object*)(l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0));
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_borrowed(v___x_799_, v_content_798_, v___x_800_);
v___x_802_ = lean_string_utf8_byte_size(v___x_801_);
lean_inc(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_800_);
lean_ctor_set(v___x_803_, 2, v___x_802_);
v___x_804_ = l_String_Slice_positions(v___x_803_);
v___x_805_ = 1;
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(v___x_803_, v___x_801_, v___x_804_, v___x_805_);
lean_dec_ref_known(v___x_803_, 3);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = ((lean_object*)(l_Lean_Fmt_Comment_render___closed__2));
v___x_830_ = lean_string_append(v___x_829_, v___x_801_);
v___x_831_ = ((lean_object*)(l_Lean_Fmt_Comment_render___closed__3));
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
v___y_807_ = v___x_832_;
goto v___jp_806_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol___closed__1));
v___x_834_ = lean_string_append(v___x_833_, v___x_801_);
v___x_835_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol___closed__0));
v___x_836_ = lean_string_append(v___x_834_, v___x_835_);
v___y_807_ = v___x_836_;
goto v___jp_806_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_multiLineRendering_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_808_ = ((lean_object*)(l_Lean_Fmt_Comment_render___closed__0));
v___x_809_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
lean_inc_ref(v_content_798_);
v___x_810_ = lean_array_to_list(v_content_798_);
v___x_811_ = l_String_intercalate(v___x_809_, v___x_810_);
v___x_812_ = lean_string_append(v___x_808_, v___x_811_);
lean_dec_ref(v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_Fmt_Comment_render___closed__1));
v_multiLineRendering_814_ = lean_string_append(v___x_812_, v___x_813_);
v___x_815_ = lean_array_get_size(v_content_798_);
lean_dec_ref(v_content_798_);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_dec_eq(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v___y_807_);
v___x_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_818_, 0, v_multiLineRendering_814_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_805_);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_816_);
v___x_820_ = lean_array_push(v___x_819_, v___x_818_);
return v___x_820_;
}
else
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = 0;
v___x_822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_822_, 0, v___y_807_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_823_, 0, v_multiLineRendering_814_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_805_);
v___x_824_ = lean_unsigned_to_nat(2u);
v___x_825_ = lean_mk_empty_array_with_capacity(v___x_824_);
v___x_826_ = lean_array_push(v___x_825_, v___x_822_);
v___x_827_ = lean_array_push(v___x_826_, v___x_823_);
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0(lean_object* v___x_837_, lean_object* v_x_838_, lean_object* v_inst_839_, lean_object* v_R_840_, lean_object* v_a_841_, uint8_t v_b_842_, lean_object* v_c_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___redArg(v___x_837_, v_x_838_, v_a_841_, v_b_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0___boxed(lean_object* v___x_845_, lean_object* v_x_846_, lean_object* v_inst_847_, lean_object* v_R_848_, lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v_c_851_){
_start:
{
uint8_t v_b_boxed_852_; uint8_t v_res_853_; lean_object* v_r_854_; 
v_b_boxed_852_ = lean_unbox(v_b_850_);
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Comment_render_spec__0(v___x_845_, v_x_846_, v_inst_847_, v_R_848_, v_a_849_, v_b_boxed_852_, v_c_851_);
lean_dec_ref(v_x_846_);
lean_dec_ref(v___x_845_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorIdx(uint8_t v_x_855_){
_start:
{
switch(v_x_855_)
{
case 0:
{
lean_object* v___x_856_; 
v___x_856_ = lean_unsigned_to_nat(0u);
return v___x_856_;
}
case 1:
{
lean_object* v___x_857_; 
v___x_857_ = lean_unsigned_to_nat(1u);
return v___x_857_;
}
default: 
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(2u);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorIdx___boxed(lean_object* v_x_859_){
_start:
{
uint8_t v_x_boxed_860_; lean_object* v_res_861_; 
v_x_boxed_860_ = lean_unbox(v_x_859_);
v_res_861_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorIdx(v_x_boxed_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___redArg(lean_object* v_k_862_){
_start:
{
lean_inc(v_k_862_);
return v_k_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___redArg___boxed(lean_object* v_k_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___redArg(v_k_863_);
lean_dec(v_k_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim(lean_object* v_motive_865_, lean_object* v_ctorIdx_866_, uint8_t v_t_867_, lean_object* v_h_868_, lean_object* v_k_869_){
_start:
{
lean_inc(v_k_869_);
return v_k_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim___boxed(lean_object* v_motive_870_, lean_object* v_ctorIdx_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_k_874_){
_start:
{
uint8_t v_t_boxed_875_; lean_object* v_res_876_; 
v_t_boxed_875_ = lean_unbox(v_t_872_);
v_res_876_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_ctorElim(v_motive_870_, v_ctorIdx_871_, v_t_boxed_875_, v_h_873_, v_k_874_);
lean_dec(v_k_874_);
lean_dec(v_ctorIdx_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___redArg(lean_object* v_afterClosestPreviousNewline_877_){
_start:
{
lean_inc(v_afterClosestPreviousNewline_877_);
return v_afterClosestPreviousNewline_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___redArg___boxed(lean_object* v_afterClosestPreviousNewline_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___redArg(v_afterClosestPreviousNewline_878_);
lean_dec(v_afterClosestPreviousNewline_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim(lean_object* v_motive_880_, uint8_t v_t_881_, lean_object* v_h_882_, lean_object* v_afterClosestPreviousNewline_883_){
_start:
{
lean_inc(v_afterClosestPreviousNewline_883_);
return v_afterClosestPreviousNewline_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim___boxed(lean_object* v_motive_884_, lean_object* v_t_885_, lean_object* v_h_886_, lean_object* v_afterClosestPreviousNewline_887_){
_start:
{
uint8_t v_t_boxed_888_; lean_object* v_res_889_; 
v_t_boxed_888_ = lean_unbox(v_t_885_);
v_res_889_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterClosestPreviousNewline_elim(v_motive_884_, v_t_boxed_888_, v_h_886_, v_afterClosestPreviousNewline_887_);
lean_dec(v_afterClosestPreviousNewline_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___redArg(lean_object* v_beforeClosestNextNewline_890_){
_start:
{
lean_inc(v_beforeClosestNextNewline_890_);
return v_beforeClosestNextNewline_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___redArg___boxed(lean_object* v_beforeClosestNextNewline_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___redArg(v_beforeClosestNextNewline_891_);
lean_dec(v_beforeClosestNextNewline_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim(lean_object* v_motive_893_, uint8_t v_t_894_, lean_object* v_h_895_, lean_object* v_beforeClosestNextNewline_896_){
_start:
{
lean_inc(v_beforeClosestNextNewline_896_);
return v_beforeClosestNextNewline_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim___boxed(lean_object* v_motive_897_, lean_object* v_t_898_, lean_object* v_h_899_, lean_object* v_beforeClosestNextNewline_900_){
_start:
{
uint8_t v_t_boxed_901_; lean_object* v_res_902_; 
v_t_boxed_901_ = lean_unbox(v_t_898_);
v_res_902_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_beforeClosestNextNewline_elim(v_motive_897_, v_t_boxed_901_, v_h_899_, v_beforeClosestNextNewline_900_);
lean_dec(v_beforeClosestNextNewline_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___redArg(lean_object* v_afterToken_903_){
_start:
{
lean_inc(v_afterToken_903_);
return v_afterToken_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___redArg___boxed(lean_object* v_afterToken_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___redArg(v_afterToken_904_);
lean_dec(v_afterToken_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim(lean_object* v_motive_906_, uint8_t v_t_907_, lean_object* v_h_908_, lean_object* v_afterToken_909_){
_start:
{
lean_inc(v_afterToken_909_);
return v_afterToken_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim___boxed(lean_object* v_motive_910_, lean_object* v_t_911_, lean_object* v_h_912_, lean_object* v_afterToken_913_){
_start:
{
uint8_t v_t_boxed_914_; lean_object* v_res_915_; 
v_t_boxed_914_ = lean_unbox(v_t_911_);
v_res_915_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_RenderedPlacementKind_afterToken_elim(v_motive_910_, v_t_boxed_914_, v_h_912_, v_afterToken_913_);
lean_dec(v_afterToken_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0(lean_object* v_00___921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0(lean_object* v_x2_923_, size_t v_sz_924_, size_t v_i_925_, lean_object* v_bs_926_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_lt(v_i_925_, v_sz_924_);
if (v___x_927_ == 0)
{
lean_dec_ref(v_x2_923_);
return v_bs_926_;
}
else
{
lean_object* v_v_928_; lean_object* v___x_929_; lean_object* v_bs_x27_930_; lean_object* v___x_931_; uint8_t v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v___x_935_; 
v_v_928_ = lean_array_uget(v_bs_926_, v_i_925_);
v___x_929_ = lean_unsigned_to_nat(0u);
v_bs_x27_930_ = lean_array_uset(v_bs_926_, v_i_925_, v___x_929_);
lean_inc_ref(v_x2_923_);
v___x_931_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_931_, 0, v_x2_923_);
v___x_932_ = lean_unbox(v_v_928_);
lean_dec(v_v_928_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_932_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_925_, v___x_933_);
v___x_935_ = lean_array_uset(v_bs_x27_930_, v_i_925_, v___x_931_);
v_i_925_ = v___x_934_;
v_bs_926_ = v___x_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0___boxed(lean_object* v_x2_937_, lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_bs_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_942_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0(v_x2_937_, v_sz_boxed_941_, v_i_boxed_942_, v_bs_940_);
return v_res_943_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_box(0);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1(lean_object* v_c_962_, lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_, lean_object* v_b_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_967_ == 0)
{
uint8_t v_kind_968_; uint8_t v_placement_969_; lean_object* v___x_970_; lean_object* v___y_972_; 
v_kind_968_ = lean_ctor_get_uint8(v_c_962_, sizeof(void*)*3);
v_placement_969_ = lean_ctor_get_uint8(v_c_962_, sizeof(void*)*3 + 1);
v___x_970_ = lean_array_uget_borrowed(v_as_963_, v_i_964_);
if (v_kind_968_ == 0)
{
if (v_placement_969_ == 0)
{
uint8_t v_isMultiLine_980_; 
v_isMultiLine_980_ = lean_ctor_get_uint8(v___x_970_, sizeof(void*)*1);
if (v_isMultiLine_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__0));
v___y_972_ = v___x_981_;
goto v___jp_971_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0));
v___y_972_ = v___x_982_;
goto v___jp_971_;
}
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1);
v___y_972_ = v___x_983_;
goto v___jp_971_;
}
}
else
{
if (v_placement_969_ == 0)
{
uint8_t v_isMultiLine_984_; 
v_isMultiLine_984_ = lean_ctor_get_uint8(v___x_970_, sizeof(void*)*1);
if (v_isMultiLine_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__2));
v___y_972_ = v___x_985_;
goto v___jp_971_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___lam__0___closed__0));
v___y_972_ = v___x_986_;
goto v___jp_971_;
}
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___closed__1);
v___y_972_ = v___x_987_;
goto v___jp_971_;
}
}
v___jp_971_:
{
size_t v_sz_973_; size_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; size_t v___x_977_; size_t v___x_978_; 
v_sz_973_ = lean_array_size(v___y_972_);
v___x_974_ = ((size_t)0ULL);
lean_inc_ref(v___y_972_);
lean_inc(v___x_970_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__0(v___x_970_, v_sz_973_, v___x_974_, v___y_972_);
v___x_976_ = l_Array_append___redArg(v_b_966_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_964_, v___x_977_);
v_i_964_ = v___x_978_;
v_b_966_ = v___x_976_;
goto _start;
}
}
else
{
return v_b_966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1___boxed(lean_object* v_c_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_){
_start:
{
size_t v_i_boxed_993_; size_t v_stop_boxed_994_; lean_object* v_res_995_; 
v_i_boxed_993_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_994_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1(v_c_988_, v_as_989_, v_i_boxed_993_, v_stop_boxed_994_, v_b_992_);
lean_dec_ref(v_as_989_);
lean_dec_ref(v_c_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements(lean_object* v_c_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
lean_inc_ref(v_c_998_);
v___x_999_ = l_Lean_Fmt_Comment_render(v_c_998_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements___closed__0));
v___x_1002_ = lean_array_get_size(v___x_999_);
v___x_1003_ = lean_nat_dec_lt(v___x_1000_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v___x_999_);
lean_dec_ref(v_c_998_);
return v___x_1001_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_le(v___x_1002_, v___x_1002_);
if (v___x_1004_ == 0)
{
if (v___x_1003_ == 0)
{
lean_dec_ref(v___x_999_);
lean_dec_ref(v_c_998_);
return v___x_1001_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = lean_usize_of_nat(v___x_1002_);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1(v_c_998_, v___x_999_, v___x_1005_, v___x_1006_, v___x_1001_);
lean_dec_ref(v___x_999_);
lean_dec_ref(v_c_998_);
return v___x_1007_;
}
}
else
{
size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = lean_usize_of_nat(v___x_1002_);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements_spec__1(v_c_998_, v___x_999_, v___x_1008_, v___x_1009_, v___x_1001_);
lean_dec_ref(v___x_999_);
lean_dec_ref(v_c_998_);
return v___x_1010_;
}
}
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedPendingComment_default___closed__0(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = ((lean_object*)(l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0));
v___x_1013_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
lean_ctor_set(v___x_1014_, 2, v___x_1011_);
lean_ctor_set(v___x_1014_, 3, v___x_1011_);
lean_ctor_set(v___x_1014_, 4, v___x_1011_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedPendingComment_default(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_obj_once(&l_Lean_Fmt_instInhabitedPendingComment_default___closed__0, &l_Lean_Fmt_instInhabitedPendingComment_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedPendingComment_default___closed__0);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instInhabitedPendingComment(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Fmt_instInhabitedPendingComment_default;
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(7u);
v___x_1030_ = lean_nat_to_int(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(21u);
v___x_1035_ = lean_nat_to_int(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(12u);
v___x_1040_ = lean_nat_to_int(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(10u);
v___x_1048_ = lean_nat_to_int(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg(lean_object* v_x_1049_){
_start:
{
lean_object* v_toComment_1050_; lean_object* v_raw_1051_; lean_object* v_startColumnOffset_1052_; lean_object* v_startPos_1053_; lean_object* v_endPos_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_toComment_1050_ = lean_ctor_get(v_x_1049_, 0);
lean_inc_ref(v_toComment_1050_);
v_raw_1051_ = lean_ctor_get(v_x_1049_, 1);
lean_inc_ref(v_raw_1051_);
v_startColumnOffset_1052_ = lean_ctor_get(v_x_1049_, 2);
lean_inc(v_startColumnOffset_1052_);
v_startPos_1053_ = lean_ctor_get(v_x_1049_, 3);
lean_inc(v_startPos_1053_);
v_endPos_1054_ = lean_ctor_get(v_x_1049_, 4);
lean_inc(v_endPos_1054_);
lean_dec_ref(v_x_1049_);
v___x_1055_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__5));
v___x_1056_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__3));
v___x_1057_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_1058_ = l_Lean_Fmt_instReprComment_repr___redArg(v_toComment_1050_);
v___x_1059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = 0;
v___x_1061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1056_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0___closed__2));
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_box(1);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__5));
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1055_);
v___x_1070_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__6);
v___x_1071_ = l_String_quote(v_raw_1051_);
v___x_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1060_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1063_);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1065_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__8));
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1055_);
v___x_1081_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__9);
v___x_1082_ = l_Nat_reprFast(v_startColumnOffset_1052_);
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v___x_1060_);
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1080_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1063_);
v___x_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1065_);
v___x_1089_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__11));
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1055_);
v___x_1092_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__12);
v___x_1093_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__14));
v___x_1094_ = l_Nat_reprFast(v_startPos_1053_);
v___x_1095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__27));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1092_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*1, v___x_1060_);
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1091_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1063_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1065_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__16));
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1055_);
v___x_1107_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg___closed__17);
v___x_1108_ = l_Nat_reprFast(v_endPos_1054_);
v___x_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1093_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1097_);
v___x_1112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1107_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*1, v___x_1060_);
v___x_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1106_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__25, &l_Lean_Fmt_instReprComment_repr___redArg___closed__25_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__25);
v___x_1116_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__26));
v___x_1117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1114_);
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1097_);
v___x_1119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1115_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1060_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr(lean_object* v_x_1121_, lean_object* v_prec_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___redArg(v_x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr___boxed(lean_object* v_x_1124_, lean_object* v_prec_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instReprPendingComment_repr(v_x_1124_, v_prec_1125_);
lean_dec(v_prec_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v_a_1131_, lean_object* v_b_1132_){
_start:
{
lean_object* v_startInclusive_1133_; lean_object* v_endExclusive_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_startInclusive_1133_ = lean_ctor_get(v___x_1129_, 1);
v_endExclusive_1134_ = lean_ctor_get(v___x_1129_, 2);
v___x_1135_ = lean_nat_sub(v_endExclusive_1134_, v_startInclusive_1133_);
v___x_1136_ = lean_nat_dec_eq(v_a_1131_, v___x_1135_);
lean_dec(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_string_utf8_next_fast(v___x_1130_, v_a_1131_);
lean_dec(v_a_1131_);
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_b_1132_, v___x_1138_);
lean_dec(v_b_1132_);
v_a_1131_ = v___x_1137_;
v_b_1132_ = v___x_1139_;
goto _start;
}
else
{
lean_dec(v_a_1131_);
return v_b_1132_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg___boxed(lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_1141_, v___x_1142_, v_a_1143_, v_b_1144_);
lean_dec_ref(v___x_1142_);
lean_dec_ref(v___x_1141_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0(lean_object* v_s_1146_, lean_object* v_pos_1147_){
_start:
{
lean_object* v_str_1148_; lean_object* v_startInclusive_1149_; lean_object* v_endExclusive_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_str_1148_ = lean_ctor_get(v_s_1146_, 0);
v_startInclusive_1149_ = lean_ctor_get(v_s_1146_, 1);
v_endExclusive_1150_ = lean_ctor_get(v_s_1146_, 2);
v___x_1151_ = lean_nat_add(v_startInclusive_1149_, v_pos_1147_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_nat_sub(v_endExclusive_1150_, v___x_1151_);
v___x_1154_ = lean_nat_dec_eq(v___x_1152_, v___x_1153_);
lean_dec(v___x_1153_);
if (v___x_1154_ == 0)
{
uint32_t v___x_1155_; uint32_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_string_utf8_get_fast(v_str_1148_, v___x_1151_);
v___x_1156_ = 32;
v___x_1157_ = lean_uint32_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v___x_1151_);
return v_pos_1147_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1158_ = lean_string_utf8_next_fast(v_str_1148_, v___x_1151_);
v___x_1159_ = lean_nat_sub(v___x_1158_, v___x_1151_);
lean_dec(v___x_1151_);
v___x_1160_ = lean_nat_add(v_pos_1147_, v___x_1159_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_nat_dec_lt(v_pos_1147_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec(v___x_1160_);
return v_pos_1147_;
}
else
{
lean_dec(v_pos_1147_);
v_pos_1147_ = v___x_1160_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1151_);
return v_pos_1147_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0___boxed(lean_object* v_s_1163_, lean_object* v_pos_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0(v_s_1163_, v_pos_1164_);
lean_dec_ref(v_s_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(lean_object* v_fst_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_str_1169_; lean_object* v_startInclusive_1170_; lean_object* v_endExclusive_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_str_1169_ = lean_ctor_get(v_fst_1166_, 0);
v_startInclusive_1170_ = lean_ctor_get(v_fst_1166_, 1);
v_endExclusive_1171_ = lean_ctor_get(v_fst_1166_, 2);
v___x_1172_ = lean_nat_sub(v_endExclusive_1171_, v_startInclusive_1170_);
v___x_1173_ = lean_nat_dec_eq(v_a_1167_, v___x_1172_);
lean_dec(v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1174_ = lean_nat_add(v_startInclusive_1170_, v_a_1167_);
lean_dec(v_a_1167_);
v___x_1175_ = lean_string_utf8_next_fast(v_str_1169_, v___x_1174_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_nat_sub(v___x_1175_, v_startInclusive_1170_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_b_1168_, v___x_1177_);
lean_dec(v_b_1168_);
v_a_1167_ = v___x_1176_;
v_b_1168_ = v___x_1178_;
goto _start;
}
else
{
lean_dec(v_a_1167_);
return v_b_1168_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg___boxed(lean_object* v_fst_1180_, lean_object* v_a_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(v_fst_1180_, v_a_1181_, v_b_1182_);
lean_dec_ref(v_fst_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg(lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_a_1187_, lean_object* v_b_1188_){
_start:
{
lean_object* v_startInclusive_1189_; lean_object* v_endExclusive_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_startInclusive_1189_ = lean_ctor_get(v___x_1184_, 1);
v_endExclusive_1190_ = lean_ctor_get(v___x_1184_, 2);
v___x_1191_ = lean_nat_sub(v_endExclusive_1190_, v_startInclusive_1189_);
v___x_1192_ = lean_nat_dec_eq(v_a_1187_, v___x_1191_);
lean_dec(v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1193_ = lean_nat_add(v___x_1185_, v_a_1187_);
lean_dec(v_a_1187_);
v___x_1194_ = lean_string_utf8_next_fast(v___x_1186_, v___x_1193_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_nat_sub(v___x_1194_, v___x_1185_);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_add(v_b_1188_, v___x_1196_);
lean_dec(v_b_1188_);
v_a_1187_ = v___x_1195_;
v_b_1188_ = v___x_1197_;
goto _start;
}
else
{
lean_dec(v_a_1187_);
return v_b_1188_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg___boxed(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg(v___x_1199_, v___x_1200_, v___x_1201_, v_a_1202_, v_b_1203_);
lean_dec_ref(v___x_1201_);
lean_dec(v___x_1200_);
lean_dec_ref(v___x_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4(lean_object* v_p_1205_, lean_object* v_as_1206_, size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_b_1209_){
_start:
{
lean_object* v_a_1211_; lean_object* v___y_1216_; uint8_t v___x_1218_; 
v___x_1218_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1218_ == 0)
{
return v_b_1209_;
}
else
{
lean_object* v_a_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v_str_1222_; lean_object* v_startInclusive_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___y_1231_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1253_; 
v_a_1219_ = lean_array_uget_borrowed(v_as_1206_, v_i_1208_);
v_fst_1220_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_fst_1220_);
v_snd_1221_ = lean_ctor_get(v_a_1219_, 1);
v_str_1222_ = lean_ctor_get(v_fst_1220_, 0);
v_startInclusive_1223_ = lean_ctor_get(v_fst_1220_, 1);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__0(v_fst_1220_, v___x_1224_);
v___x_1226_ = lean_nat_add(v_startInclusive_1223_, v___x_1225_);
lean_dec(v___x_1225_);
lean_inc(v_startInclusive_1223_);
lean_inc_ref(v_str_1222_);
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v_str_1222_);
lean_ctor_set(v___x_1227_, 1, v_startInclusive_1223_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
v___x_1228_ = l_String_Slice_positions(v___x_1227_);
v___x_1229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg(v___x_1227_, v_startInclusive_1223_, v_str_1222_, v___x_1228_, v___x_1224_);
lean_dec_ref_known(v___x_1227_, 3);
v___x_1235_ = l_String_Slice_positions(v_fst_1220_);
v___x_1236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(v_fst_1220_, v___x_1235_, v___x_1224_);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_fst_1220_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1254_ = lean_ctor_get(v_fst_1220_, 2);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_fst_1220_, 1);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_fst_1220_, 0);
lean_dec(v_unused_1256_);
v___x_1238_ = v_fst_1220_;
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v_fst_1220_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_nat_add(v___y_1231_, v___x_1229_);
lean_dec(v___x_1229_);
lean_dec(v___y_1231_);
if (lean_obj_tag(v_b_1209_) == 0)
{
v___y_1216_ = v___x_1232_;
goto v___jp_1215_;
}
else
{
lean_object* v_val_1233_; uint8_t v___x_1234_; 
v_val_1233_ = lean_ctor_get(v_b_1209_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_b_1209_, 1);
v___x_1234_ = lean_nat_dec_le(v_val_1233_, v___x_1232_);
if (v___x_1234_ == 0)
{
lean_dec(v_val_1233_);
v___y_1216_ = v___x_1232_;
goto v___jp_1215_;
}
else
{
lean_dec(v___x_1232_);
v___y_1216_ = v_val_1233_;
goto v___jp_1215_;
}
}
}
v_resetjp_1237_:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_nat_dec_eq(v___x_1229_, v___x_1236_);
lean_dec(v___x_1236_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_nat_dec_eq(v_snd_1221_, v___x_1224_);
if (v___x_1241_ == 0)
{
lean_del_object(v___x_1238_);
v___y_1231_ = v___x_1224_;
goto v___jp_1230_;
}
else
{
lean_object* v_toComment_1242_; lean_object* v_startColumnOffset_1243_; uint8_t v_kind_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_toComment_1242_ = lean_ctor_get(v_p_1205_, 0);
v_startColumnOffset_1243_ = lean_ctor_get(v_p_1205_, 2);
v_kind_1244_ = lean_ctor_get_uint8(v_toComment_1242_, sizeof(void*)*3);
v___x_1245_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(v_kind_1244_);
v___x_1246_ = lean_string_utf8_byte_size(v___x_1245_);
lean_inc_ref(v___x_1245_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 2, v___x_1246_);
lean_ctor_set(v___x_1238_, 1, v___x_1224_);
lean_ctor_set(v___x_1238_, 0, v___x_1245_);
v___x_1248_ = v___x_1238_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = l_String_Slice_positions(v___x_1248_);
v___x_1250_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_1248_, v___x_1245_, v___x_1249_, v___x_1224_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1248_);
v___x_1251_ = lean_nat_add(v_startColumnOffset_1243_, v___x_1250_);
lean_dec(v___x_1250_);
v___y_1231_ = v___x_1251_;
goto v___jp_1230_;
}
}
}
else
{
lean_del_object(v___x_1238_);
lean_dec(v___x_1229_);
v_a_1211_ = v_b_1209_;
goto v___jp_1210_;
}
}
}
v___jp_1210_:
{
size_t v___x_1212_; size_t v___x_1213_; 
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1208_, v___x_1212_);
v_i_1208_ = v___x_1213_;
v_b_1209_ = v_a_1211_;
goto _start;
}
v___jp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1216_);
v_a_1211_ = v___x_1217_;
goto v___jp_1210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4___boxed(lean_object* v_p_1257_, lean_object* v_as_1258_, lean_object* v_sz_1259_, lean_object* v_i_1260_, lean_object* v_b_1261_){
_start:
{
size_t v_sz_boxed_1262_; size_t v_i_boxed_1263_; lean_object* v_res_1264_; 
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1259_);
lean_dec(v_sz_1259_);
v_i_boxed_1263_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4(v_p_1257_, v_as_1258_, v_sz_boxed_1262_, v_i_boxed_1263_, v_b_1261_);
lean_dec_ref(v_as_1258_);
lean_dec_ref(v_p_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset(lean_object* v_p_1265_, lean_object* v_lines_1266_){
_start:
{
lean_object* v_offset_x3f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; size_t v_sz_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_offset_x3f_1267_ = lean_box(0);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = l_Array_zipIdx___redArg(v_lines_1266_, v___x_1268_);
v_sz_1270_ = lean_array_size(v___x_1269_);
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__4(v_p_1265_, v___x_1269_, v_sz_1270_, v___x_1271_, v_offset_x3f_1267_);
lean_dec_ref(v___x_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_startColumnOffset_1273_; 
v_startColumnOffset_1273_ = lean_ctor_get(v_p_1265_, 2);
lean_inc(v_startColumnOffset_1273_);
return v_startColumnOffset_1273_;
}
else
{
lean_object* v_val_1274_; 
v_val_1274_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1272_, 1);
return v_val_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset___boxed(lean_object* v_p_1275_, lean_object* v_lines_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset(v_p_1275_, v_lines_1276_);
lean_dec_ref(v_p_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1(lean_object* v___x_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_inst_1281_, lean_object* v_R_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___redArg(v___x_1278_, v___x_1279_, v___x_1280_, v_a_1283_, v_b_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1___boxed(lean_object* v___x_1287_, lean_object* v___x_1288_, lean_object* v___x_1289_, lean_object* v_inst_1290_, lean_object* v_R_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_, lean_object* v_c_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__1(v___x_1287_, v___x_1288_, v___x_1289_, v_inst_1290_, v_R_1291_, v_a_1292_, v_b_1293_, v_c_1294_);
lean_dec_ref(v___x_1289_);
lean_dec(v___x_1288_);
lean_dec_ref(v___x_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2(lean_object* v_fst_1296_, lean_object* v_inst_1297_, lean_object* v_R_1298_, lean_object* v_a_1299_, lean_object* v_b_1300_, lean_object* v_c_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(v_fst_1296_, v_a_1299_, v_b_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___boxed(lean_object* v_fst_1303_, lean_object* v_inst_1304_, lean_object* v_R_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_, lean_object* v_c_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2(v_fst_1303_, v_inst_1304_, v_R_1305_, v_a_1306_, v_b_1307_, v_c_1308_);
lean_dec_ref(v_fst_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3(lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v_inst_1312_, lean_object* v_R_1313_, lean_object* v_a_1314_, lean_object* v_b_1315_, lean_object* v_c_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_1310_, v___x_1311_, v_a_1314_, v_b_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___boxed(lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_inst_1320_, lean_object* v_R_1321_, lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_c_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3(v___x_1318_, v___x_1319_, v_inst_1320_, v_R_1321_, v_a_1322_, v_b_1323_, v_c_1324_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v___x_1318_);
return v_res_1325_;
}
}
static lean_object* _init_l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0));
v___x_1328_ = lean_string_utf8_byte_size(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0(lean_object* v_s_1329_){
_start:
{
lean_object* v_str_1330_; lean_object* v_startInclusive_1331_; lean_object* v_endExclusive_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_str_1330_ = lean_ctor_get(v_s_1329_, 0);
v_startInclusive_1331_ = lean_ctor_get(v_s_1329_, 1);
v_endExclusive_1332_ = lean_ctor_get(v_s_1329_, 2);
v___x_1333_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0));
v___x_1334_ = lean_obj_once(&l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1, &l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1_once, _init_l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__1);
v___x_1335_ = lean_nat_sub(v_endExclusive_1332_, v_startInclusive_1331_);
v___x_1336_ = lean_nat_dec_le(v___x_1334_, v___x_1335_);
lean_dec(v___x_1335_);
if (v___x_1336_ == 0)
{
return v_s_1329_;
}
else
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_string_memcmp(v_str_1330_, v___x_1333_, v_startInclusive_1331_, v___x_1337_, v___x_1334_);
if (v___x_1338_ == 0)
{
return v_s_1329_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
lean_inc(v_endExclusive_1332_);
lean_inc(v_startInclusive_1331_);
lean_inc_ref(v_str_1330_);
v___x_1339_ = l_String_Slice_pos_x21(v_s_1329_, v___x_1334_);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_s_1329_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1348_ = lean_ctor_get(v_s_1329_, 2);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_s_1329_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_s_1329_, 0);
lean_dec(v_unused_1350_);
v___x_1341_ = v_s_1329_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_s_1329_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_nat_add(v_startInclusive_1331_, v___x_1339_);
lean_dec(v___x_1339_);
lean_dec(v_startInclusive_1331_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_str_1330_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_endExclusive_1332_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__1(lean_object* v_s_1351_){
_start:
{
lean_object* v_str_1352_; lean_object* v_startInclusive_1353_; lean_object* v_endExclusive_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_str_1352_ = lean_ctor_get(v_s_1351_, 0);
v_startInclusive_1353_ = lean_ctor_get(v_s_1351_, 1);
v_endExclusive_1354_ = lean_ctor_get(v_s_1351_, 2);
v___x_1355_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_1356_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__1);
v___x_1357_ = lean_nat_sub(v_endExclusive_1354_, v_startInclusive_1353_);
v___x_1358_ = lean_nat_dec_le(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec(v___x_1357_);
return v_s_1351_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_nat_sub(v___x_1357_, v___x_1356_);
lean_dec(v___x_1357_);
v___x_1361_ = lean_nat_add(v_startInclusive_1353_, v___x_1360_);
v___x_1362_ = lean_string_memcmp(v_str_1352_, v___x_1355_, v___x_1361_, v___x_1359_, v___x_1356_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v___x_1360_);
return v_s_1351_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
lean_inc(v_startInclusive_1353_);
lean_inc_ref(v_str_1352_);
v___x_1363_ = l_String_Slice_pos_x21(v_s_1351_, v___x_1360_);
lean_dec(v___x_1360_);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_s_1351_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1372_ = lean_ctor_get(v_s_1351_, 2);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_s_1351_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_s_1351_, 0);
lean_dec(v_unused_1374_);
v___x_1365_ = v_s_1351_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v_s_1351_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_nat_add(v_startInclusive_1353_, v___x_1363_);
lean_dec(v___x_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_str_1352_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_startInclusive_1353_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2(lean_object* v_s_1375_, lean_object* v_pos_1376_){
_start:
{
lean_object* v_str_1377_; lean_object* v_startInclusive_1378_; lean_object* v_endExclusive_1379_; lean_object* v___x_1380_; uint8_t v___y_1382_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_str_1377_ = lean_ctor_get(v_s_1375_, 0);
v_startInclusive_1378_ = lean_ctor_get(v_s_1375_, 1);
v_endExclusive_1379_ = lean_ctor_get(v_s_1375_, 2);
v___x_1380_ = lean_nat_add(v_startInclusive_1378_, v_pos_1376_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_nat_sub(v_endExclusive_1379_, v___x_1380_);
v___x_1390_ = lean_nat_dec_eq(v___x_1388_, v___x_1389_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
uint32_t v___x_1391_; uint32_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_string_utf8_get_fast(v_str_1377_, v___x_1380_);
v___x_1392_ = 32;
v___x_1393_ = lean_uint32_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
uint32_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = 10;
v___x_1395_ = lean_uint32_dec_eq(v___x_1391_, v___x_1394_);
v___y_1382_ = v___x_1395_;
goto v___jp_1381_;
}
else
{
v___y_1382_ = v___x_1393_;
goto v___jp_1381_;
}
}
else
{
lean_dec(v___x_1380_);
return v_pos_1376_;
}
v___jp_1381_:
{
if (v___y_1382_ == 0)
{
lean_dec(v___x_1380_);
return v_pos_1376_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1383_ = lean_string_utf8_next_fast(v_str_1377_, v___x_1380_);
v___x_1384_ = lean_nat_sub(v___x_1383_, v___x_1380_);
lean_dec(v___x_1380_);
v___x_1385_ = lean_nat_add(v_pos_1376_, v___x_1384_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_nat_dec_lt(v_pos_1376_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v___x_1385_);
return v_pos_1376_;
}
else
{
lean_dec(v_pos_1376_);
v_pos_1376_ = v___x_1385_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2___boxed(lean_object* v_s_1396_, lean_object* v_pos_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2(v_s_1396_, v_pos_1397_);
lean_dec_ref(v_s_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3(lean_object* v_s_1399_, lean_object* v_pos_1400_){
_start:
{
lean_object* v_str_1401_; lean_object* v_startInclusive_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_str_1401_ = lean_ctor_get(v_s_1399_, 0);
v_startInclusive_1402_ = lean_ctor_get(v_s_1399_, 1);
v___x_1403_ = lean_nat_add(v_startInclusive_1402_, v_pos_1400_);
v___x_1404_ = lean_nat_sub(v___x_1403_, v_startInclusive_1402_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_nat_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___y_1412_; lean_object* v___x_1415_; uint32_t v___x_1416_; uint32_t v___x_1417_; uint8_t v___x_1418_; 
lean_inc(v_startInclusive_1402_);
lean_inc_ref(v_str_1401_);
v___x_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1407_, 0, v_str_1401_);
lean_ctor_set(v___x_1407_, 1, v_startInclusive_1402_);
lean_ctor_set(v___x_1407_, 2, v___x_1403_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_sub(v___x_1404_, v___x_1408_);
lean_dec(v___x_1404_);
v___x_1410_ = l_String_Slice_posLE(v___x_1407_, v___x_1409_);
lean_dec_ref_known(v___x_1407_, 3);
v___x_1415_ = lean_nat_add(v_startInclusive_1402_, v___x_1410_);
v___x_1416_ = lean_string_utf8_get_fast(v_str_1401_, v___x_1415_);
lean_dec(v___x_1415_);
v___x_1417_ = 32;
v___x_1418_ = lean_uint32_dec_eq(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
uint32_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = 10;
v___x_1420_ = lean_uint32_dec_eq(v___x_1416_, v___x_1419_);
v___y_1412_ = v___x_1420_;
goto v___jp_1411_;
}
else
{
v___y_1412_ = v___x_1418_;
goto v___jp_1411_;
}
v___jp_1411_:
{
if (v___y_1412_ == 0)
{
lean_dec(v___x_1410_);
return v_pos_1400_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_lt(v___x_1410_, v_pos_1400_);
if (v___x_1413_ == 0)
{
lean_dec(v___x_1410_);
return v_pos_1400_;
}
else
{
lean_dec(v_pos_1400_);
v_pos_1400_ = v___x_1410_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1404_);
lean_dec(v___x_1403_);
return v_pos_1400_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3___boxed(lean_object* v_s_1421_, lean_object* v_pos_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3(v_s_1421_, v_pos_1422_);
lean_dec_ref(v_s_1421_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent(uint8_t v_kind_1424_, lean_object* v_s_1425_){
_start:
{
if (v_kind_1424_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0(v_s_1425_);
v___x_1427_ = l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__1(v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v_str_1428_; lean_object* v_startInclusive_1429_; lean_object* v_endExclusive_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1444_; 
v_str_1428_ = lean_ctor_get(v_s_1425_, 0);
lean_inc_ref(v_str_1428_);
v_startInclusive_1429_ = lean_ctor_get(v_s_1425_, 1);
lean_inc(v_startInclusive_1429_);
v_endExclusive_1430_ = lean_ctor_get(v_s_1425_, 2);
lean_inc(v_endExclusive_1430_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__2(v_s_1425_, v___x_1431_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_s_1425_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1445_ = lean_ctor_get(v_s_1425_, 2);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_s_1425_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_s_1425_, 0);
lean_dec(v_unused_1447_);
v___x_1434_ = v_s_1425_;
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v_s_1425_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_nat_add(v_startInclusive_1429_, v___x_1432_);
lean_dec(v___x_1432_);
lean_dec(v_startInclusive_1429_);
lean_inc(v_endExclusive_1430_);
lean_inc(v___x_1436_);
lean_inc_ref(v_str_1428_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_str_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_endExclusive_1430_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_nat_sub(v_endExclusive_1430_, v___x_1436_);
lean_dec(v_endExclusive_1430_);
v___x_1440_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__3(v___x_1438_, v___x_1439_);
lean_dec_ref(v___x_1438_);
v___x_1441_ = lean_nat_add(v___x_1436_, v___x_1440_);
lean_dec(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1442_, 0, v_str_1428_);
lean_ctor_set(v___x_1442_, 1, v___x_1436_);
lean_ctor_set(v___x_1442_, 2, v___x_1441_);
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent___boxed(lean_object* v_kind_1448_, lean_object* v_s_1449_){
_start:
{
uint8_t v_kind_boxed_1450_; lean_object* v_res_1451_; 
v_kind_boxed_1450_ = lean_unbox(v_kind_1448_);
v_res_1451_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent(v_kind_boxed_1450_, v_s_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0___redArg(lean_object* v_a_1452_){
_start:
{
lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1497_; 
v_fst_1453_ = lean_ctor_get(v_a_1452_, 0);
v_snd_1454_ = lean_ctor_get(v_a_1452_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1452_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1456_ = v_a_1452_;
v_isShared_1457_ = v_isSharedCheck_1497_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_snd_1454_);
lean_inc(v_fst_1453_);
lean_dec(v_a_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1497_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_str_1458_; lean_object* v_startInclusive_1459_; lean_object* v_endExclusive_1460_; uint32_t v___y_1462_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_str_1458_ = lean_ctor_get(v_fst_1453_, 0);
v_startInclusive_1459_ = lean_ctor_get(v_fst_1453_, 1);
v_endExclusive_1460_ = lean_ctor_get(v_fst_1453_, 2);
v___x_1487_ = lean_nat_sub(v_endExclusive_1460_, v_startInclusive_1459_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_nat_dec_eq(v___x_1487_, v___x_1488_);
lean_dec(v___x_1487_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_lt(v___x_1488_, v_snd_1454_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_del_object(v___x_1456_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_fst_1453_);
lean_ctor_set(v___x_1491_, 1, v_snd_1454_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
v___x_1492_ = l_String_Slice_Pos_get_x3f(v_fst_1453_, v___x_1488_);
if (lean_obj_tag(v___x_1492_) == 0)
{
uint32_t v___x_1493_; 
v___x_1493_ = 65;
v___y_1462_ = v___x_1493_;
goto v___jp_1461_;
}
else
{
lean_object* v_val_1494_; uint32_t v___x_1495_; 
v_val_1494_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1495_ = lean_unbox_uint32(v_val_1494_);
lean_dec(v_val_1494_);
v___y_1462_ = v___x_1495_;
goto v___jp_1461_;
}
}
}
else
{
lean_object* v___x_1496_; 
lean_del_object(v___x_1456_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_fst_1453_);
lean_ctor_set(v___x_1496_, 1, v_snd_1454_);
return v___x_1496_;
}
v___jp_1461_:
{
uint32_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = 32;
v___x_1464_ = lean_uint32_dec_eq(v___y_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1466_; 
if (v_isShared_1457_ == 0)
{
v___x_1466_ = v___x_1456_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_fst_1453_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_snd_1454_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_endExclusive_1460_);
lean_inc(v_startInclusive_1459_);
lean_inc_ref(v_str_1458_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l_String_Slice_Pos_nextn(v_fst_1453_, v___x_1469_, v___x_1468_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_fst_1453_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1484_ = lean_ctor_get(v_fst_1453_, 2);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_fst_1453_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_fst_1453_, 0);
lean_dec(v_unused_1486_);
v___x_1472_ = v_fst_1453_;
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v_fst_1453_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_nat_add(v_startInclusive_1459_, v___x_1470_);
lean_dec(v___x_1470_);
lean_dec(v_startInclusive_1459_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_str_1458_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_endExclusive_1460_);
v___x_1476_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = lean_nat_sub(v_snd_1454_, v___x_1468_);
lean_dec(v_snd_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 1, v___x_1477_);
lean_ctor_set(v___x_1456_, 0, v___x_1476_);
v___x_1479_ = v___x_1456_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_a_1452_ = v___x_1479_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation(lean_object* v_line_1498_, lean_object* v_amount_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_fst_1502_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_line_1498_);
lean_ctor_set(v___x_1500_, 1, v_amount_1499_);
v___x_1501_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0___redArg(v___x_1500_);
v_fst_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_fst_1502_);
lean_dec_ref(v___x_1501_);
return v_fst_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0(lean_object* v_inst_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation_spec__0___redArg(v_a_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix(lean_object* v_p_1506_, lean_object* v_line_1507_){
_start:
{
lean_object* v_toComment_1508_; uint8_t v_kind_1509_; lean_object* v___x_1510_; 
v_toComment_1508_ = lean_ctor_get(v_p_1506_, 0);
v_kind_1509_ = lean_ctor_get_uint8(v_toComment_1508_, sizeof(void*)*3);
v___x_1510_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_linePrefix_x3f(v_kind_1509_);
if (lean_obj_tag(v___x_1510_) == 1)
{
lean_object* v_val_1511_; lean_object* v_str_1512_; lean_object* v_startInclusive_1513_; lean_object* v_endExclusive_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_str_1512_ = lean_ctor_get(v_line_1507_, 0);
v_startInclusive_1513_ = lean_ctor_get(v_line_1507_, 1);
v_endExclusive_1514_ = lean_ctor_get(v_line_1507_, 2);
v___x_1515_ = lean_string_utf8_byte_size(v_val_1511_);
v___x_1516_ = lean_nat_sub(v_endExclusive_1514_, v_startInclusive_1513_);
v___x_1517_ = lean_nat_dec_le(v___x_1515_, v___x_1516_);
lean_dec(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v_val_1511_);
return v_line_1507_;
}
else
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_string_memcmp(v_str_1512_, v_val_1511_, v_startInclusive_1513_, v___x_1518_, v___x_1515_);
lean_dec(v_val_1511_);
if (v___x_1519_ == 0)
{
return v_line_1507_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
lean_inc(v_endExclusive_1514_);
lean_inc(v_startInclusive_1513_);
lean_inc_ref(v_str_1512_);
v___x_1520_ = l_String_Slice_pos_x21(v_line_1507_, v___x_1515_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_line_1507_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; 
v_unused_1530_ = lean_ctor_get(v_line_1507_, 2);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_line_1507_, 1);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_line_1507_, 0);
lean_dec(v_unused_1532_);
v___x_1522_ = v_line_1507_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v_line_1507_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_nat_add(v_startInclusive_1513_, v___x_1520_);
lean_dec(v___x_1520_);
lean_dec(v_startInclusive_1513_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_str_1512_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_endExclusive_1514_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0(v___x_1526_);
return v___x_1527_;
}
}
}
}
}
else
{
lean_dec(v___x_1510_);
return v_line_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix___boxed(lean_object* v_p_1533_, lean_object* v_line_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix(v_p_1533_, v_line_1534_);
lean_dec_ref(v_p_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0(lean_object* v___x_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_str_1538_; lean_object* v_startInclusive_1539_; lean_object* v_endExclusive_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_str_1538_ = lean_ctor_get(v_s_1537_, 0);
v_startInclusive_1539_ = lean_ctor_get(v_s_1537_, 1);
v_endExclusive_1540_ = lean_ctor_get(v_s_1537_, 2);
v___x_1541_ = lean_string_utf8_byte_size(v___x_1536_);
v___x_1542_ = lean_nat_sub(v_endExclusive_1540_, v_startInclusive_1539_);
v___x_1543_ = lean_nat_dec_le(v___x_1541_, v___x_1542_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
return v_s_1537_;
}
else
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_string_memcmp(v_str_1538_, v___x_1536_, v_startInclusive_1539_, v___x_1544_, v___x_1541_);
if (v___x_1545_ == 0)
{
return v_s_1537_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
lean_inc(v_endExclusive_1540_);
lean_inc(v_startInclusive_1539_);
lean_inc_ref(v_str_1538_);
v___x_1546_ = l_String_Slice_pos_x21(v_s_1537_, v___x_1541_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_s_1537_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1555_ = lean_ctor_get(v_s_1537_, 2);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_s_1537_, 1);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_s_1537_, 0);
lean_dec(v_unused_1557_);
v___x_1548_ = v_s_1537_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v_s_1537_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_nat_add(v_startInclusive_1539_, v___x_1546_);
lean_dec(v___x_1546_);
lean_dec(v_startInclusive_1539_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_str_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_endExclusive_1540_);
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
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0___boxed(lean_object* v___x_1558_, lean_object* v_s_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0(v___x_1558_, v_s_1559_);
lean_dec_ref(v___x_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1(lean_object* v___x_1561_, lean_object* v_s_1562_){
_start:
{
lean_object* v_str_1563_; lean_object* v_startInclusive_1564_; lean_object* v_endExclusive_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_str_1563_ = lean_ctor_get(v_s_1562_, 0);
v_startInclusive_1564_ = lean_ctor_get(v_s_1562_, 1);
v_endExclusive_1565_ = lean_ctor_get(v_s_1562_, 2);
v___x_1566_ = lean_string_utf8_byte_size(v___x_1561_);
v___x_1567_ = lean_nat_sub(v_endExclusive_1565_, v_startInclusive_1564_);
v___x_1568_ = lean_nat_dec_le(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec(v___x_1567_);
return v_s_1562_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_nat_sub(v___x_1567_, v___x_1566_);
lean_dec(v___x_1567_);
v___x_1571_ = lean_nat_add(v_startInclusive_1564_, v___x_1570_);
v___x_1572_ = lean_string_memcmp(v_str_1563_, v___x_1561_, v___x_1571_, v___x_1569_, v___x_1566_);
lean_dec(v___x_1571_);
if (v___x_1572_ == 0)
{
lean_dec(v___x_1570_);
return v_s_1562_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
lean_inc(v_startInclusive_1564_);
lean_inc_ref(v_str_1563_);
v___x_1573_ = l_String_Slice_pos_x21(v_s_1562_, v___x_1570_);
lean_dec(v___x_1570_);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_s_1562_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1582_ = lean_ctor_get(v_s_1562_, 2);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_s_1562_, 1);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_s_1562_, 0);
lean_dec(v_unused_1584_);
v___x_1575_ = v_s_1562_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v_s_1562_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_nat_add(v_startInclusive_1564_, v___x_1573_);
lean_dec(v___x_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 2, v___x_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_str_1563_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_startInclusive_1564_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1___boxed(lean_object* v___x_1585_, lean_object* v_s_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1(v___x_1585_, v_s_1586_);
lean_dec_ref(v___x_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg(lean_object* v_content_1588_, lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v_a_1591_, lean_object* v_b_1592_){
_start:
{
lean_object* v_it_1594_; lean_object* v_startInclusive_1595_; lean_object* v_endExclusive_1596_; 
if (lean_obj_tag(v_a_1591_) == 0)
{
lean_object* v_currPos_1600_; lean_object* v_searcher_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1705_; 
v_currPos_1600_ = lean_ctor_get(v_a_1591_, 0);
v_searcher_1601_ = lean_ctor_get(v_a_1591_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1591_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1603_ = v_a_1591_;
v_isShared_1604_ = v_isSharedCheck_1705_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_searcher_1601_);
lean_inc(v_currPos_1600_);
lean_dec(v_a_1591_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1705_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_it_1606_; lean_object* v_it_1612_; lean_object* v_startPos_1613_; lean_object* v_endPos_1614_; 
switch(lean_obj_tag(v_searcher_1601_))
{
case 0:
{
lean_object* v_pos_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1639_; 
lean_del_object(v___x_1603_);
v_pos_1627_ = lean_ctor_get(v_searcher_1601_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_searcher_1601_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1629_ = v_searcher_1601_;
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_pos_1627_);
lean_dec(v_searcher_1601_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_startInclusive_1631_; lean_object* v_endExclusive_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_startInclusive_1631_ = lean_ctor_get(v___x_1589_, 1);
v_endExclusive_1632_ = lean_ctor_get(v___x_1589_, 2);
v___x_1633_ = lean_nat_sub(v_endExclusive_1632_, v_startInclusive_1631_);
v___x_1634_ = lean_nat_dec_eq(v_pos_1627_, v___x_1633_);
lean_dec(v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1636_; 
lean_inc(v_pos_1627_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 1);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_pos_1627_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_inc(v_pos_1627_);
v_it_1612_ = v___x_1636_;
v_startPos_1613_ = v_pos_1627_;
v_endPos_1614_ = v_pos_1627_;
goto v___jp_1611_;
}
}
else
{
lean_object* v___x_1638_; 
lean_del_object(v___x_1629_);
v___x_1638_ = lean_box(3);
lean_inc(v_pos_1627_);
v_it_1612_ = v___x_1638_;
v_startPos_1613_ = v_pos_1627_;
v_endPos_1614_ = v_pos_1627_;
goto v___jp_1611_;
}
}
}
case 1:
{
lean_object* v_pos_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_pos_1640_ = lean_ctor_get(v_searcher_1601_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_searcher_1601_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v_searcher_1601_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_pos_1640_);
lean_dec(v_searcher_1601_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_string_utf8_next_fast(v_content_1588_, v_pos_1640_);
lean_dec(v_pos_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v_it_1606_ = v___x_1646_;
goto v___jp_1605_;
}
}
}
case 2:
{
lean_object* v_needle_1649_; lean_object* v_table_1650_; lean_object* v_stackPos_1651_; lean_object* v_needlePos_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1704_; 
v_needle_1649_ = lean_ctor_get(v_searcher_1601_, 0);
v_table_1650_ = lean_ctor_get(v_searcher_1601_, 1);
v_stackPos_1651_ = lean_ctor_get(v_searcher_1601_, 2);
v_needlePos_1652_ = lean_ctor_get(v_searcher_1601_, 3);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_searcher_1601_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1654_ = v_searcher_1601_;
v_isShared_1655_ = v_isSharedCheck_1704_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_needlePos_1652_);
lean_inc(v_stackPos_1651_);
lean_inc(v_table_1650_);
lean_inc(v_needle_1649_);
lean_dec(v_searcher_1601_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1704_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_str_1656_; lean_object* v_startInclusive_1657_; lean_object* v_endExclusive_1658_; lean_object* v_basePos_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_str_1656_ = lean_ctor_get(v_needle_1649_, 0);
v_startInclusive_1657_ = lean_ctor_get(v_needle_1649_, 1);
v_endExclusive_1658_ = lean_ctor_get(v_needle_1649_, 2);
v_basePos_1659_ = lean_nat_sub(v_stackPos_1651_, v_needlePos_1652_);
v___x_1660_ = lean_nat_sub(v_endExclusive_1658_, v_startInclusive_1657_);
v___x_1661_ = lean_nat_add(v_basePos_1659_, v___x_1660_);
v___x_1662_ = lean_nat_dec_le(v___x_1661_, v___x_1590_);
lean_dec(v___x_1661_);
if (v___x_1662_ == 0)
{
uint8_t v___x_1663_; 
lean_dec(v___x_1660_);
lean_del_object(v___x_1654_);
lean_dec(v_needlePos_1652_);
lean_dec(v_stackPos_1651_);
lean_dec_ref(v_table_1650_);
lean_dec_ref(v_needle_1649_);
v___x_1663_ = lean_nat_dec_lt(v_basePos_1659_, v___x_1590_);
lean_dec(v_basePos_1659_);
if (v___x_1663_ == 0)
{
lean_del_object(v___x_1603_);
goto v___jp_1625_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_box(3);
v_it_1606_ = v___x_1664_;
goto v___jp_1605_;
}
}
else
{
uint8_t v_stackByte_1665_; lean_object* v___x_1666_; uint8_t v_patByte_1667_; uint8_t v___x_1668_; 
lean_dec(v_basePos_1659_);
lean_inc(v_stackPos_1651_);
v_stackByte_1665_ = lean_string_get_byte_fast(v_content_1588_, v_stackPos_1651_);
v___x_1666_ = lean_nat_add(v_startInclusive_1657_, v_needlePos_1652_);
v_patByte_1667_ = lean_string_get_byte_fast(v_str_1656_, v___x_1666_);
v___x_1668_ = lean_uint8_dec_eq(v_stackByte_1665_, v_patByte_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
lean_dec(v___x_1660_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_nat_dec_eq(v_needlePos_1652_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_newNeedlePos_1673_; uint8_t v___x_1674_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_sub(v_needlePos_1652_, v___x_1671_);
lean_dec(v_needlePos_1652_);
v_newNeedlePos_1673_ = lean_array_fget_borrowed(v_table_1650_, v___x_1672_);
lean_dec(v___x_1672_);
v___x_1674_ = lean_nat_dec_eq(v_newNeedlePos_1673_, v___x_1669_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; 
lean_inc(v_newNeedlePos_1673_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v_newNeedlePos_1673_);
v___x_1676_ = v___x_1654_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_needle_1649_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_table_1650_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_stackPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_newNeedlePos_1673_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
v_it_1606_ = v___x_1676_;
goto v___jp_1605_;
}
}
else
{
lean_object* v_nextStackPos_1678_; lean_object* v___x_1680_; 
v_nextStackPos_1678_ = l_String_Slice_posGE___redArg(v___x_1589_, v_stackPos_1651_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v___x_1669_);
lean_ctor_set(v___x_1654_, 2, v_nextStackPos_1678_);
v___x_1680_ = v___x_1654_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_needle_1649_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_table_1650_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_nextStackPos_1678_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v___x_1669_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v_it_1606_ = v___x_1680_;
goto v___jp_1605_;
}
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_nextStackPos_1684_; lean_object* v___x_1686_; 
lean_dec(v_needlePos_1652_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v_stackPos_1651_, v___x_1682_);
lean_dec(v_stackPos_1651_);
v_nextStackPos_1684_ = l_String_Slice_posGE___redArg(v___x_1589_, v___x_1683_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v___x_1669_);
lean_ctor_set(v___x_1654_, 2, v_nextStackPos_1684_);
v___x_1686_ = v___x_1654_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_needle_1649_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_table_1650_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_nextStackPos_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v___x_1669_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_it_1606_ = v___x_1686_;
goto v___jp_1605_;
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v_nextStackPos_1689_; lean_object* v_nextNeedlePos_1690_; uint8_t v___x_1691_; 
lean_del_object(v___x_1603_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1689_ = lean_nat_add(v_stackPos_1651_, v___x_1688_);
lean_dec(v_stackPos_1651_);
v_nextNeedlePos_1690_ = lean_nat_add(v_needlePos_1652_, v___x_1688_);
lean_dec(v_needlePos_1652_);
v___x_1691_ = lean_nat_dec_eq(v_nextNeedlePos_1690_, v___x_1660_);
lean_dec(v___x_1660_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1693_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v_nextNeedlePos_1690_);
lean_ctor_set(v___x_1654_, 2, v_nextStackPos_1689_);
v___x_1693_ = v___x_1654_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_needle_1649_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_table_1650_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_nextStackPos_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_nextNeedlePos_1690_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_currPos_1600_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v_a_1591_ = v___x_1694_;
goto _start;
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1697_ = lean_nat_sub(v_nextStackPos_1689_, v_nextNeedlePos_1690_);
lean_dec(v_nextNeedlePos_1690_);
v___x_1698_ = l_String_Slice_pos_x21(v___x_1589_, v___x_1697_);
lean_dec(v___x_1697_);
v___x_1699_ = l_String_Slice_pos_x21(v___x_1589_, v_nextStackPos_1689_);
v___x_1700_ = lean_unsigned_to_nat(0u);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v___x_1700_);
lean_ctor_set(v___x_1654_, 2, v_nextStackPos_1689_);
v___x_1702_ = v___x_1654_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_needle_1649_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_table_1650_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_nextStackPos_1689_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
v_it_1612_ = v___x_1702_;
v_startPos_1613_ = v___x_1698_;
v_endPos_1614_ = v___x_1699_;
goto v___jp_1611_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1603_);
goto v___jp_1625_;
}
}
v___jp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v_it_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_currPos_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_it_1606_);
v___x_1608_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
v_a_1591_ = v___x_1608_;
goto _start;
}
}
v___jp_1611_:
{
lean_object* v_slice_1615_; lean_object* v_startInclusive_1616_; lean_object* v_endExclusive_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_slice_1615_ = l_String_Slice_subslice_x21(v___x_1589_, v_currPos_1600_, v_startPos_1613_);
v_startInclusive_1616_ = lean_ctor_get(v_slice_1615_, 0);
v_endExclusive_1617_ = lean_ctor_get(v_slice_1615_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_slice_1615_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v_slice_1615_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_endExclusive_1617_);
lean_inc(v_startInclusive_1616_);
lean_dec(v_slice_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_nextIt_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v_it_1612_);
lean_ctor_set(v___x_1619_, 0, v_endPos_1614_);
v_nextIt_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_endPos_1614_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_it_1612_);
v_nextIt_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
v_it_1594_ = v_nextIt_1622_;
v_startInclusive_1595_ = v_startInclusive_1616_;
v_endExclusive_1596_ = v_endExclusive_1617_;
goto v___jp_1593_;
}
}
}
v___jp_1625_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_box(1);
lean_inc(v___x_1590_);
v_it_1594_ = v___x_1626_;
v_startInclusive_1595_ = v_currPos_1600_;
v_endExclusive_1596_ = v___x_1590_;
goto v___jp_1593_;
}
}
}
else
{
lean_dec(v___x_1590_);
lean_dec_ref(v_content_1588_);
return v_b_1592_;
}
v___jp_1593_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_inc_ref(v_content_1588_);
v___x_1597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1597_, 0, v_content_1588_);
lean_ctor_set(v___x_1597_, 1, v_startInclusive_1595_);
lean_ctor_set(v___x_1597_, 2, v_endExclusive_1596_);
v___x_1598_ = lean_array_push(v_b_1592_, v___x_1597_);
v_a_1591_ = v_it_1594_;
v_b_1592_ = v___x_1598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg___boxed(lean_object* v_content_1706_, lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v_a_1709_, lean_object* v_b_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg(v_content_1706_, v___x_1707_, v___x_1708_, v_a_1709_, v_b_1710_);
lean_dec_ref(v___x_1707_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__6(lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
if (lean_obj_tag(v_a_1712_) == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = l_List_reverse___redArg(v_a_1713_);
return v___x_1714_;
}
else
{
lean_object* v_head_1715_; lean_object* v_tail_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1725_; 
v_head_1715_ = lean_ctor_get(v_a_1712_, 0);
v_tail_1716_ = lean_ctor_get(v_a_1712_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_a_1712_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1718_ = v_a_1712_;
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_tail_1716_);
lean_inc(v_head_1715_);
lean_dec(v_a_1712_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = l_String_Slice_toString(v_head_1715_);
lean_dec(v_head_1715_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v_a_1713_);
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1713_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
v_a_1712_ = v_tail_1716_;
v_a_1713_ = v___x_1722_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3___redArg(lean_object* v_a_1726_, lean_object* v_b_1727_){
_start:
{
lean_object* v_array_1728_; lean_object* v_start_1729_; lean_object* v_stop_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1743_; 
v_array_1728_ = lean_ctor_get(v_a_1726_, 0);
v_start_1729_ = lean_ctor_get(v_a_1726_, 1);
v_stop_1730_ = lean_ctor_get(v_a_1726_, 2);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1732_ = v_a_1726_;
v_isShared_1733_ = v_isSharedCheck_1743_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_stop_1730_);
lean_inc(v_start_1729_);
lean_inc(v_array_1728_);
lean_dec(v_a_1726_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1743_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_nat_dec_lt(v_start_1729_, v_stop_1730_);
if (v___x_1734_ == 0)
{
lean_del_object(v___x_1732_);
lean_dec(v_stop_1730_);
lean_dec(v_start_1729_);
lean_dec_ref(v_array_1728_);
return v_b_1727_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_nat_add(v_start_1729_, v___x_1735_);
lean_inc_ref(v_array_1728_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1736_);
v___x_1738_ = v___x_1732_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_array_1728_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_stop_1730_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_array_fget(v_array_1728_, v_start_1729_);
lean_dec(v_start_1729_);
lean_dec_ref(v_array_1728_);
v___x_1740_ = lean_array_push(v_b_1727_, v___x_1739_);
v_a_1726_ = v___x_1738_;
v_b_1727_ = v___x_1740_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg(lean_object* v_s_1744_, lean_object* v_a_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v_it_1748_; lean_object* v_startInclusive_1749_; lean_object* v_endExclusive_1750_; 
if (lean_obj_tag(v_a_1745_) == 0)
{
lean_object* v_currPos_1758_; lean_object* v_searcher_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1875_; 
v_currPos_1758_ = lean_ctor_get(v_a_1745_, 0);
v_searcher_1759_ = lean_ctor_get(v_a_1745_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_a_1745_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1761_ = v_a_1745_;
v_isShared_1762_ = v_isSharedCheck_1875_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_searcher_1759_);
lean_inc(v_currPos_1758_);
lean_dec(v_a_1745_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1875_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_it_1764_; lean_object* v_it_1770_; lean_object* v_startPos_1771_; lean_object* v_endPos_1772_; 
switch(lean_obj_tag(v_searcher_1759_))
{
case 0:
{
lean_object* v_pos_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1800_; 
lean_del_object(v___x_1761_);
v_pos_1788_ = lean_ctor_get(v_searcher_1759_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_searcher_1759_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1790_ = v_searcher_1759_;
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_pos_1788_);
lean_dec(v_searcher_1759_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_startInclusive_1792_; lean_object* v_endExclusive_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_startInclusive_1792_ = lean_ctor_get(v_s_1744_, 1);
v_endExclusive_1793_ = lean_ctor_get(v_s_1744_, 2);
v___x_1794_ = lean_nat_sub(v_endExclusive_1793_, v_startInclusive_1792_);
v___x_1795_ = lean_nat_dec_eq(v_pos_1788_, v___x_1794_);
lean_dec(v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1797_; 
lean_inc(v_pos_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set_tag(v___x_1790_, 1);
v___x_1797_ = v___x_1790_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_pos_1788_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_inc(v_pos_1788_);
v_it_1770_ = v___x_1797_;
v_startPos_1771_ = v_pos_1788_;
v_endPos_1772_ = v_pos_1788_;
goto v___jp_1769_;
}
}
else
{
lean_object* v___x_1799_; 
lean_del_object(v___x_1790_);
v___x_1799_ = lean_box(3);
lean_inc(v_pos_1788_);
v_it_1770_ = v___x_1799_;
v_startPos_1771_ = v_pos_1788_;
v_endPos_1772_ = v_pos_1788_;
goto v___jp_1769_;
}
}
}
case 1:
{
lean_object* v_pos_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1813_; 
v_pos_1801_ = lean_ctor_get(v_searcher_1759_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_searcher_1759_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1803_ = v_searcher_1759_;
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_pos_1801_);
lean_dec(v_searcher_1759_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_str_1805_; lean_object* v_startInclusive_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v_str_1805_ = lean_ctor_get(v_s_1744_, 0);
v_startInclusive_1806_ = lean_ctor_get(v_s_1744_, 1);
v___x_1807_ = lean_nat_add(v_startInclusive_1806_, v_pos_1801_);
lean_dec(v_pos_1801_);
v___x_1808_ = lean_string_utf8_next_fast(v_str_1805_, v___x_1807_);
lean_dec(v___x_1807_);
v___x_1809_ = lean_nat_sub(v___x_1808_, v_startInclusive_1806_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v_it_1764_ = v___x_1811_;
goto v___jp_1763_;
}
}
}
case 2:
{
lean_object* v_needle_1814_; lean_object* v_table_1815_; lean_object* v_stackPos_1816_; lean_object* v_needlePos_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1874_; 
v_needle_1814_ = lean_ctor_get(v_searcher_1759_, 0);
v_table_1815_ = lean_ctor_get(v_searcher_1759_, 1);
v_stackPos_1816_ = lean_ctor_get(v_searcher_1759_, 2);
v_needlePos_1817_ = lean_ctor_get(v_searcher_1759_, 3);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_searcher_1759_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1819_ = v_searcher_1759_;
v_isShared_1820_ = v_isSharedCheck_1874_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_needlePos_1817_);
lean_inc(v_stackPos_1816_);
lean_inc(v_table_1815_);
lean_inc(v_needle_1814_);
lean_dec(v_searcher_1759_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1874_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_str_1821_; lean_object* v_startInclusive_1822_; lean_object* v_endExclusive_1823_; lean_object* v_str_1824_; lean_object* v_startInclusive_1825_; lean_object* v_endExclusive_1826_; lean_object* v_basePos_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_str_1821_ = lean_ctor_get(v_needle_1814_, 0);
v_startInclusive_1822_ = lean_ctor_get(v_needle_1814_, 1);
v_endExclusive_1823_ = lean_ctor_get(v_needle_1814_, 2);
v_str_1824_ = lean_ctor_get(v_s_1744_, 0);
v_startInclusive_1825_ = lean_ctor_get(v_s_1744_, 1);
v_endExclusive_1826_ = lean_ctor_get(v_s_1744_, 2);
v_basePos_1827_ = lean_nat_sub(v_stackPos_1816_, v_needlePos_1817_);
v___x_1828_ = lean_nat_sub(v_endExclusive_1823_, v_startInclusive_1822_);
v___x_1829_ = lean_nat_add(v_basePos_1827_, v___x_1828_);
v___x_1830_ = lean_nat_sub(v_endExclusive_1826_, v_startInclusive_1825_);
v___x_1831_ = lean_nat_dec_le(v___x_1829_, v___x_1830_);
lean_dec(v___x_1829_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
lean_dec(v___x_1828_);
lean_del_object(v___x_1819_);
lean_dec(v_needlePos_1817_);
lean_dec(v_stackPos_1816_);
lean_dec_ref(v_table_1815_);
lean_dec_ref(v_needle_1814_);
v___x_1832_ = lean_nat_dec_lt(v_basePos_1827_, v___x_1830_);
lean_dec(v___x_1830_);
lean_dec(v_basePos_1827_);
if (v___x_1832_ == 0)
{
lean_del_object(v___x_1761_);
goto v___jp_1783_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_box(3);
v_it_1764_ = v___x_1833_;
goto v___jp_1763_;
}
}
else
{
lean_object* v___x_1834_; uint8_t v_stackByte_1835_; lean_object* v___x_1836_; uint8_t v_patByte_1837_; uint8_t v___x_1838_; 
lean_dec(v___x_1830_);
lean_dec(v_basePos_1827_);
v___x_1834_ = lean_nat_add(v_startInclusive_1825_, v_stackPos_1816_);
v_stackByte_1835_ = lean_string_get_byte_fast(v_str_1824_, v___x_1834_);
v___x_1836_ = lean_nat_add(v_startInclusive_1822_, v_needlePos_1817_);
v_patByte_1837_ = lean_string_get_byte_fast(v_str_1821_, v___x_1836_);
v___x_1838_ = lean_uint8_dec_eq(v_stackByte_1835_, v_patByte_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_dec(v___x_1828_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_needlePos_1817_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_newNeedlePos_1843_; uint8_t v___x_1844_; 
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_sub(v_needlePos_1817_, v___x_1841_);
lean_dec(v_needlePos_1817_);
v_newNeedlePos_1843_ = lean_array_fget_borrowed(v_table_1815_, v___x_1842_);
lean_dec(v___x_1842_);
v___x_1844_ = lean_nat_dec_eq(v_newNeedlePos_1843_, v___x_1839_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; 
lean_inc(v_newNeedlePos_1843_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v_newNeedlePos_1843_);
v___x_1846_ = v___x_1819_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_needle_1814_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_table_1815_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_stackPos_1816_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_newNeedlePos_1843_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
v_it_1764_ = v___x_1846_;
goto v___jp_1763_;
}
}
else
{
lean_object* v_nextStackPos_1848_; lean_object* v___x_1850_; 
v_nextStackPos_1848_ = l_String_Slice_posGE___redArg(v_s_1744_, v_stackPos_1816_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v___x_1839_);
lean_ctor_set(v___x_1819_, 2, v_nextStackPos_1848_);
v___x_1850_ = v___x_1819_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_needle_1814_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_table_1815_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_nextStackPos_1848_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v___x_1839_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
v_it_1764_ = v___x_1850_;
goto v___jp_1763_;
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_nextStackPos_1854_; lean_object* v___x_1856_; 
lean_dec(v_needlePos_1817_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_stackPos_1816_, v___x_1852_);
lean_dec(v_stackPos_1816_);
v_nextStackPos_1854_ = l_String_Slice_posGE___redArg(v_s_1744_, v___x_1853_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v___x_1839_);
lean_ctor_set(v___x_1819_, 2, v_nextStackPos_1854_);
v___x_1856_ = v___x_1819_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_needle_1814_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_table_1815_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_nextStackPos_1854_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v___x_1839_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v_it_1764_ = v___x_1856_;
goto v___jp_1763_;
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v_nextStackPos_1859_; lean_object* v_nextNeedlePos_1860_; uint8_t v___x_1861_; 
lean_del_object(v___x_1761_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1859_ = lean_nat_add(v_stackPos_1816_, v___x_1858_);
lean_dec(v_stackPos_1816_);
v_nextNeedlePos_1860_ = lean_nat_add(v_needlePos_1817_, v___x_1858_);
lean_dec(v_needlePos_1817_);
v___x_1861_ = lean_nat_dec_eq(v_nextNeedlePos_1860_, v___x_1828_);
lean_dec(v___x_1828_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1863_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v_nextNeedlePos_1860_);
lean_ctor_set(v___x_1819_, 2, v_nextStackPos_1859_);
v___x_1863_ = v___x_1819_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_needle_1814_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_table_1815_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_nextStackPos_1859_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_nextNeedlePos_1860_);
v___x_1863_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_currPos_1758_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v_a_1745_ = v___x_1864_;
goto _start;
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1867_ = lean_nat_sub(v_nextStackPos_1859_, v_nextNeedlePos_1860_);
lean_dec(v_nextNeedlePos_1860_);
v___x_1868_ = l_String_Slice_pos_x21(v_s_1744_, v___x_1867_);
lean_dec(v___x_1867_);
v___x_1869_ = l_String_Slice_pos_x21(v_s_1744_, v_nextStackPos_1859_);
v___x_1870_ = lean_unsigned_to_nat(0u);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v___x_1870_);
lean_ctor_set(v___x_1819_, 2, v_nextStackPos_1859_);
v___x_1872_ = v___x_1819_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_needle_1814_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_table_1815_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_nextStackPos_1859_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v_it_1770_ = v___x_1872_;
v_startPos_1771_ = v___x_1868_;
v_endPos_1772_ = v___x_1869_;
goto v___jp_1769_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1761_);
goto v___jp_1783_;
}
}
v___jp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_it_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_currPos_1758_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_it_1764_);
v___x_1766_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v_a_1745_ = v___x_1766_;
goto _start;
}
}
v___jp_1769_:
{
lean_object* v_slice_1773_; lean_object* v_startInclusive_1774_; lean_object* v_endExclusive_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_slice_1773_ = l_String_Slice_subslice_x21(v_s_1744_, v_currPos_1758_, v_startPos_1771_);
v_startInclusive_1774_ = lean_ctor_get(v_slice_1773_, 0);
v_endExclusive_1775_ = lean_ctor_get(v_slice_1773_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_slice_1773_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v_slice_1773_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_endExclusive_1775_);
lean_inc(v_startInclusive_1774_);
lean_dec(v_slice_1773_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_nextIt_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_it_1770_);
lean_ctor_set(v___x_1777_, 0, v_endPos_1772_);
v_nextIt_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_endPos_1772_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_it_1770_);
v_nextIt_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
v_it_1748_ = v_nextIt_1780_;
v_startInclusive_1749_ = v_startInclusive_1774_;
v_endExclusive_1750_ = v_endExclusive_1775_;
goto v___jp_1747_;
}
}
}
v___jp_1783_:
{
lean_object* v_startInclusive_1784_; lean_object* v_endExclusive_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_startInclusive_1784_ = lean_ctor_get(v_s_1744_, 1);
v_endExclusive_1785_ = lean_ctor_get(v_s_1744_, 2);
v___x_1786_ = lean_nat_sub(v_endExclusive_1785_, v_startInclusive_1784_);
v___x_1787_ = lean_box(1);
v_it_1748_ = v___x_1787_;
v_startInclusive_1749_ = v_currPos_1758_;
v_endExclusive_1750_ = v___x_1786_;
goto v___jp_1747_;
}
}
}
else
{
return v_b_1746_;
}
v___jp_1747_:
{
lean_object* v_str_1751_; lean_object* v_startInclusive_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_str_1751_ = lean_ctor_get(v_s_1744_, 0);
v_startInclusive_1752_ = lean_ctor_get(v_s_1744_, 1);
v___x_1753_ = lean_nat_add(v_startInclusive_1752_, v_startInclusive_1749_);
lean_dec(v_startInclusive_1749_);
v___x_1754_ = lean_nat_add(v_startInclusive_1752_, v_endExclusive_1750_);
lean_dec(v_endExclusive_1750_);
lean_inc_ref(v_str_1751_);
v___x_1755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1755_, 0, v_str_1751_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
lean_ctor_set(v___x_1755_, 2, v___x_1754_);
v___x_1756_ = lean_array_push(v_b_1746_, v___x_1755_);
v_a_1745_ = v_it_1748_;
v_b_1746_ = v___x_1756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg___boxed(lean_object* v_s_1876_, lean_object* v_a_1877_, lean_object* v_b_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg(v_s_1876_, v_a_1877_, v_b_1878_);
lean_dec_ref(v_s_1876_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5(lean_object* v_p_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
if (lean_obj_tag(v_a_1881_) == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = l_List_reverse___redArg(v_a_1882_);
return v___x_1883_;
}
else
{
lean_object* v_head_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1894_; 
v_head_1884_ = lean_ctor_get(v_a_1881_, 0);
v_tail_1885_ = lean_ctor_get(v_a_1881_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_a_1881_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1887_ = v_a_1881_;
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_head_1884_);
lean_dec(v_a_1881_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropLinePrefix(v_p_1880_, v_head_1884_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_a_1882_);
lean_ctor_set(v___x_1887_, 0, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_a_1882_);
v___x_1891_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
v_a_1881_ = v_tail_1885_;
v_a_1882_ = v___x_1891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5___boxed(lean_object* v_p_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5(v_p_1895_, v_a_1896_, v_a_1897_);
lean_dec_ref(v_p_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8(size_t v_sz_1899_, size_t v_i_1900_, lean_object* v_bs_1901_){
_start:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_usize_dec_lt(v_i_1900_, v_sz_1899_);
if (v___x_1902_ == 0)
{
return v_bs_1901_;
}
else
{
lean_object* v_v_1903_; lean_object* v___x_1904_; lean_object* v_bs_x27_1905_; lean_object* v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v_v_1903_ = lean_array_uget(v_bs_1901_, v_i_1900_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v_bs_x27_1905_ = lean_array_uset(v_bs_1901_, v_i_1900_, v___x_1904_);
v___x_1906_ = l_String_Slice_toString(v_v_1903_);
lean_dec(v_v_1903_);
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1900_, v___x_1907_);
v___x_1909_ = lean_array_uset(v_bs_x27_1905_, v_i_1900_, v___x_1906_);
v_i_1900_ = v___x_1908_;
v_bs_1901_ = v___x_1909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8___boxed(lean_object* v_sz_1911_, lean_object* v_i_1912_, lean_object* v_bs_1913_){
_start:
{
size_t v_sz_boxed_1914_; size_t v_i_boxed_1915_; lean_object* v_res_1916_; 
v_sz_boxed_1914_ = lean_unbox_usize(v_sz_1911_);
lean_dec(v_sz_1911_);
v_i_boxed_1915_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8(v_sz_boxed_1914_, v_i_boxed_1915_, v_bs_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__4(lean_object* v_indentation_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
if (lean_obj_tag(v_a_1918_) == 0)
{
lean_object* v___x_1920_; 
lean_dec(v_indentation_1917_);
v___x_1920_ = l_List_reverse___redArg(v_a_1919_);
return v___x_1920_;
}
else
{
lean_object* v_head_1921_; lean_object* v_tail_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1931_; 
v_head_1921_ = lean_ctor_get(v_a_1918_, 0);
v_tail_1922_ = lean_ctor_get(v_a_1918_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_a_1918_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1924_ = v_a_1918_;
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_tail_1922_);
lean_inc(v_head_1921_);
lean_dec(v_a_1918_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_inc(v_indentation_1917_);
v___x_1926_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_dropIndentation(v_head_1921_, v_indentation_1917_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v_a_1919_);
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_a_1919_);
v___x_1928_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
v_a_1918_ = v_tail_1922_;
v_a_1919_ = v___x_1928_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize(lean_object* v_p_1934_){
_start:
{
lean_object* v_toComment_1935_; lean_object* v_raw_1936_; lean_object* v_startPos_1937_; lean_object* v_endPos_1938_; uint8_t v_kind_1939_; uint8_t v_placement_1940_; lean_object* v_originalTokenRange_1941_; uint8_t v_originalWhitespaceKind_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1986_; 
v_toComment_1935_ = lean_ctor_get(v_p_1934_, 0);
lean_inc_ref(v_toComment_1935_);
v_raw_1936_ = lean_ctor_get(v_p_1934_, 1);
v_startPos_1937_ = lean_ctor_get(v_p_1934_, 3);
lean_inc(v_startPos_1937_);
v_endPos_1938_ = lean_ctor_get(v_p_1934_, 4);
lean_inc(v_endPos_1938_);
v_kind_1939_ = lean_ctor_get_uint8(v_toComment_1935_, sizeof(void*)*3);
v_placement_1940_ = lean_ctor_get_uint8(v_toComment_1935_, sizeof(void*)*3 + 1);
v_originalTokenRange_1941_ = lean_ctor_get(v_toComment_1935_, 0);
v_originalWhitespaceKind_1942_ = lean_ctor_get_uint8(v_toComment_1935_, sizeof(void*)*3 + 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_toComment_1935_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_toComment_1935_, 2);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_toComment_1935_, 1);
lean_dec(v_unused_1988_);
v___x_1944_ = v_toComment_1935_;
v_isShared_1945_ = v_isSharedCheck_1986_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_originalTokenRange_1941_);
lean_dec(v_toComment_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1986_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_s_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v_indentation_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_deindentedLines_1968_; lean_object* v_deindentedLines_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_content_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; size_t v_sz_1980_; size_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1946_ = lean_string_utf8_byte_size(v_raw_1936_);
v___x_1947_ = l_String_instInhabitedSlice;
v___x_1948_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_raw_1936_);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_raw_1936_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
lean_ctor_set(v___x_1949_, 2, v___x_1946_);
v___x_1950_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(v_kind_1939_);
v___x_1951_ = l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0(v___x_1950_, v___x_1949_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(v_kind_1939_);
v_s_1953_ = l_String_Slice_dropSuffix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__1(v___x_1952_, v___x_1951_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_1955_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(v_s_1953_);
v___x_1956_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize___closed__0));
v_a_1957_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg(v_s_1953_, v___x_1955_, v___x_1956_);
lean_dec_ref(v_s_1953_);
lean_inc_ref(v_a_1957_);
v_indentation_1958_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset(v_p_1934_, v_a_1957_);
v___x_1959_ = lean_array_get(v___x_1947_, v_a_1957_, v___x_1948_);
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = lean_array_get_size(v_a_1957_);
v___x_1962_ = l_Array_toSubarray___redArg(v_a_1957_, v___x_1960_, v___x_1961_);
v___x_1963_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3___redArg(v___x_1962_, v___x_1956_);
v___x_1964_ = lean_array_to_list(v___x_1963_);
v___x_1965_ = lean_box(0);
v___x_1966_ = l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__4(v_indentation_1958_, v___x_1964_, v___x_1965_);
v___x_1967_ = l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__5(v_p_1934_, v___x_1966_, v___x_1965_);
lean_dec_ref(v_p_1934_);
v_deindentedLines_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_deindentedLines_1968_, 0, v___x_1959_);
lean_ctor_set(v_deindentedLines_1968_, 1, v___x_1967_);
v_deindentedLines_1969_ = l_List_mapTR_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__6(v_deindentedLines_1968_, v___x_1965_);
v___x_1970_ = l_String_intercalate(v___x_1954_, v_deindentedLines_1969_);
v___x_1971_ = lean_string_utf8_byte_size(v___x_1970_);
v___x_1972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set(v___x_1972_, 1, v___x_1948_);
lean_ctor_set(v___x_1972_, 2, v___x_1971_);
v___x_1973_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent(v_kind_1939_, v___x_1972_);
v_content_1974_ = l_String_Slice_toString(v___x_1973_);
lean_dec_ref(v___x_1973_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_startPos_1937_);
lean_ctor_set(v___x_1975_, 1, v_endPos_1938_);
v___x_1976_ = lean_string_utf8_byte_size(v_content_1974_);
lean_inc_ref(v_content_1974_);
v___x_1977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1977_, 0, v_content_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1948_);
lean_ctor_set(v___x_1977_, 2, v___x_1976_);
v___x_1978_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1(v___x_1977_);
v___x_1979_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg(v_content_1974_, v___x_1977_, v___x_1976_, v___x_1978_, v___x_1956_);
lean_dec_ref_known(v___x_1977_, 3);
v_sz_1980_ = lean_array_size(v___x_1979_);
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__8(v_sz_1980_, v___x_1981_, v___x_1979_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 2, v___x_1982_);
lean_ctor_set(v___x_1944_, 1, v___x_1975_);
v___x_1984_ = v___x_1944_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_originalTokenRange_1941_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v___x_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*3, v_kind_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*3 + 1, v_placement_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_1942_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2(lean_object* v_s_1989_, lean_object* v_inst_1990_, lean_object* v_R_1991_, lean_object* v_a_1992_, lean_object* v_b_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___redArg(v_s_1989_, v_a_1992_, v_b_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2___boxed(lean_object* v_s_1995_, lean_object* v_inst_1996_, lean_object* v_R_1997_, lean_object* v_a_1998_, lean_object* v_b_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__2(v_s_1995_, v_inst_1996_, v_R_1997_, v_a_1998_, v_b_1999_);
lean_dec_ref(v_s_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3(lean_object* v_inst_2001_, lean_object* v_R_2002_, lean_object* v_a_2003_, lean_object* v_b_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__3___redArg(v_a_2003_, v_b_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7(lean_object* v_content_2006_, lean_object* v___x_2007_, lean_object* v___x_2008_, lean_object* v_inst_2009_, lean_object* v_R_2010_, lean_object* v_a_2011_, lean_object* v_b_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___redArg(v_content_2006_, v___x_2007_, v___x_2008_, v_a_2011_, v_b_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7___boxed(lean_object* v_content_2014_, lean_object* v___x_2015_, lean_object* v___x_2016_, lean_object* v_inst_2017_, lean_object* v_R_2018_, lean_object* v_a_2019_, lean_object* v_b_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__7(v_content_2014_, v___x_2015_, v___x_2016_, v_inst_2017_, v_R_2018_, v_a_2019_, v_b_2020_);
lean_dec_ref(v___x_2015_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg(lean_object* v___x_2022_, lean_object* v___x_2023_, lean_object* v___x_2024_, lean_object* v_a_2025_, lean_object* v_b_2026_){
_start:
{
lean_object* v_startInclusive_2027_; lean_object* v_endExclusive_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_startInclusive_2027_ = lean_ctor_get(v___x_2022_, 1);
v_endExclusive_2028_ = lean_ctor_get(v___x_2022_, 2);
v___x_2029_ = lean_nat_sub(v_endExclusive_2028_, v_startInclusive_2027_);
v___x_2030_ = lean_nat_dec_eq(v_a_2025_, v___x_2029_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2031_ = lean_nat_add(v___x_2023_, v_a_2025_);
lean_dec(v_a_2025_);
v___x_2032_ = lean_string_utf8_next_fast(v___x_2024_, v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_nat_sub(v___x_2032_, v___x_2023_);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_b_2026_, v___x_2034_);
lean_dec(v_b_2026_);
v_a_2025_ = v___x_2033_;
v_b_2026_ = v___x_2035_;
goto _start;
}
else
{
lean_dec(v_a_2025_);
return v_b_2026_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg___boxed(lean_object* v___x_2037_, lean_object* v___x_2038_, lean_object* v___x_2039_, lean_object* v_a_2040_, lean_object* v_b_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg(v___x_2037_, v___x_2038_, v___x_2039_, v_a_2040_, v_b_2041_);
lean_dec_ref(v___x_2039_);
lean_dec(v___x_2038_);
lean_dec_ref(v___x_2037_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg(lean_object* v_s_2043_, lean_object* v_a_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_nat_dec_eq(v_a_2044_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v_str_2048_; lean_object* v_startInclusive_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint32_t v___x_2057_; uint32_t v___x_2058_; uint8_t v___x_2059_; 
v_str_2048_ = lean_ctor_get(v_s_2043_, 0);
v_startInclusive_2049_ = lean_ctor_get(v_s_2043_, 1);
v___x_2050_ = lean_nat_add(v_startInclusive_2049_, v_a_2044_);
lean_inc(v___x_2050_);
lean_inc(v_startInclusive_2049_);
lean_inc_ref(v_str_2048_);
v___x_2051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2051_, 0, v_str_2048_);
lean_ctor_set(v___x_2051_, 1, v_startInclusive_2049_);
lean_ctor_set(v___x_2051_, 2, v___x_2050_);
v___x_2052_ = lean_nat_sub(v___x_2050_, v_startInclusive_2049_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = lean_nat_sub(v___x_2052_, v___x_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = l_String_Slice_posLE(v___x_2051_, v___x_2054_);
lean_dec_ref_known(v___x_2051_, 3);
v___x_2056_ = lean_nat_add(v_startInclusive_2049_, v___x_2055_);
v___x_2057_ = lean_string_utf8_get_fast(v_str_2048_, v___x_2056_);
lean_dec(v___x_2056_);
v___x_2058_ = 10;
v___x_2059_ = lean_uint32_dec_eq(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v___x_2055_);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_nat_sub(v_a_2044_, v___x_2053_);
lean_dec(v_a_2044_);
v___x_2062_ = l_String_Slice_posLE(v_s_2043_, v___x_2061_);
v_a_2044_ = v___x_2062_;
v_b_2045_ = v___x_2060_;
goto _start;
}
else
{
lean_object* v___x_2064_; 
lean_dec(v_a_2044_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2055_);
return v___x_2064_;
}
}
else
{
lean_dec(v_a_2044_);
lean_inc(v_b_2045_);
return v_b_2045_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg___boxed(lean_object* v_s_2065_, lean_object* v_a_2066_, lean_object* v_b_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg(v_s_2065_, v_a_2066_, v_b_2067_);
lean_dec(v_b_2067_);
lean_dec_ref(v_s_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0(lean_object* v_s_2069_){
_start:
{
lean_object* v_startInclusive_2070_; lean_object* v_endExclusive_2071_; lean_object* v_searcher_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_startInclusive_2070_ = lean_ctor_get(v_s_2069_, 1);
v_endExclusive_2071_ = lean_ctor_get(v_s_2069_, 2);
v_searcher_2072_ = lean_nat_sub(v_endExclusive_2071_, v_startInclusive_2070_);
v___x_2073_ = lean_box(0);
v___x_2074_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg(v_s_2069_, v_searcher_2072_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0___boxed(lean_object* v_s_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0(v_s_2075_);
lean_dec_ref(v_s_2075_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg(lean_object* v_s_2077_, lean_object* v_a_2078_, lean_object* v_b_2079_){
_start:
{
lean_object* v_str_2080_; lean_object* v_startInclusive_2081_; lean_object* v_endExclusive_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_str_2080_ = lean_ctor_get(v_s_2077_, 0);
v_startInclusive_2081_ = lean_ctor_get(v_s_2077_, 1);
v_endExclusive_2082_ = lean_ctor_get(v_s_2077_, 2);
v___x_2083_ = lean_nat_sub(v_endExclusive_2082_, v_startInclusive_2081_);
v___x_2084_ = lean_nat_dec_eq(v_a_2078_, v___x_2083_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2085_ = lean_nat_add(v_startInclusive_2081_, v_a_2078_);
lean_dec(v_a_2078_);
v___x_2086_ = lean_string_utf8_next_fast(v_str_2080_, v___x_2085_);
lean_dec(v___x_2085_);
v___x_2087_ = lean_nat_sub(v___x_2086_, v_startInclusive_2081_);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_b_2079_, v___x_2088_);
lean_dec(v_b_2079_);
v_a_2078_ = v___x_2087_;
v_b_2079_ = v___x_2089_;
goto _start;
}
else
{
lean_dec(v_a_2078_);
return v_b_2079_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg___boxed(lean_object* v_s_2091_, lean_object* v_a_2092_, lean_object* v_b_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg(v_s_2091_, v_a_2092_, v_b_2093_);
lean_dec_ref(v_s_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset(lean_object* v_columnOffset_2095_, lean_object* v_s_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0(v_s_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = l_String_Slice_positions(v_s_2096_);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg(v_s_2096_, v___x_2098_, v___x_2099_);
lean_dec_ref(v_s_2096_);
v___x_2101_ = lean_nat_add(v_columnOffset_2095_, v___x_2100_);
lean_dec(v___x_2100_);
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; lean_object* v_str_2103_; lean_object* v_startInclusive_2104_; lean_object* v_endExclusive_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2117_; 
v_val_2102_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v___x_2097_, 1);
v_str_2103_ = lean_ctor_get(v_s_2096_, 0);
lean_inc_ref(v_str_2103_);
v_startInclusive_2104_ = lean_ctor_get(v_s_2096_, 1);
lean_inc(v_startInclusive_2104_);
v_endExclusive_2105_ = lean_ctor_get(v_s_2096_, 2);
lean_inc(v_endExclusive_2105_);
v___x_2106_ = l_String_Slice_Pos_next_x21(v_s_2096_, v_val_2102_);
lean_dec(v_val_2102_);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_s_2096_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; lean_object* v_unused_2119_; lean_object* v_unused_2120_; 
v_unused_2118_ = lean_ctor_get(v_s_2096_, 2);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_s_2096_, 1);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_s_2096_, 0);
lean_dec(v_unused_2120_);
v___x_2108_ = v_s_2096_;
v_isShared_2109_ = v_isSharedCheck_2117_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_s_2096_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2117_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_nat_add(v_startInclusive_2104_, v___x_2106_);
lean_dec(v___x_2106_);
lean_dec(v_startInclusive_2104_);
lean_inc(v___x_2110_);
lean_inc_ref(v_str_2103_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_str_2103_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_endExclusive_2105_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = l_String_Slice_positions(v___x_2112_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg(v___x_2112_, v___x_2110_, v_str_2103_, v___x_2113_, v___x_2114_);
lean_dec_ref(v_str_2103_);
lean_dec(v___x_2110_);
lean_dec_ref(v___x_2112_);
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset___boxed(lean_object* v_columnOffset_2121_, lean_object* v_s_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset(v_columnOffset_2121_, v_s_2122_);
lean_dec(v_columnOffset_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1(lean_object* v_s_2124_, lean_object* v_inst_2125_, lean_object* v_R_2126_, lean_object* v_a_2127_, lean_object* v_b_2128_, lean_object* v_c_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___redArg(v_s_2124_, v_a_2127_, v_b_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1___boxed(lean_object* v_s_2131_, lean_object* v_inst_2132_, lean_object* v_R_2133_, lean_object* v_a_2134_, lean_object* v_b_2135_, lean_object* v_c_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__1(v_s_2131_, v_inst_2132_, v_R_2133_, v_a_2134_, v_b_2135_, v_c_2136_);
lean_dec_ref(v_s_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2(lean_object* v___x_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v_inst_2141_, lean_object* v_R_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_, lean_object* v_c_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___redArg(v___x_2138_, v___x_2139_, v___x_2140_, v_a_2143_, v_b_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2___boxed(lean_object* v___x_2147_, lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v_inst_2150_, lean_object* v_R_2151_, lean_object* v_a_2152_, lean_object* v_b_2153_, lean_object* v_c_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__2(v___x_2147_, v___x_2148_, v___x_2149_, v_inst_2150_, v_R_2151_, v_a_2152_, v_b_2153_, v_c_2154_);
lean_dec_ref(v___x_2149_);
lean_dec(v___x_2148_);
lean_dec_ref(v___x_2147_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0(lean_object* v_s_2156_, lean_object* v_inst_2157_, lean_object* v_R_2158_, lean_object* v_a_2159_, lean_object* v_b_2160_, lean_object* v_c_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___redArg(v_s_2156_, v_a_2159_, v_b_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0___boxed(lean_object* v_s_2163_, lean_object* v_inst_2164_, lean_object* v_R_2165_, lean_object* v_a_2166_, lean_object* v_b_2167_, lean_object* v_c_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_advanceColumnOffset_spec__0_spec__0(v_s_2163_, v_inst_2164_, v_R_2165_, v_a_2166_, v_b_2167_, v_c_2168_);
lean_dec(v_b_2167_);
lean_dec_ref(v_s_2163_);
return v_res_2169_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg(lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_a_2172_, uint8_t v_b_2173_){
_start:
{
lean_object* v_startInclusive_2174_; lean_object* v_endExclusive_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_startInclusive_2174_ = lean_ctor_get(v___x_2170_, 1);
v_endExclusive_2175_ = lean_ctor_get(v___x_2170_, 2);
v___x_2176_ = lean_nat_sub(v_endExclusive_2175_, v_startInclusive_2174_);
v___x_2177_ = lean_nat_dec_eq(v_a_2172_, v___x_2176_);
lean_dec(v___x_2176_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; lean_object* v___x_2179_; uint8_t v___y_2181_; uint32_t v___x_2183_; uint8_t v___y_2185_; uint32_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2178_ = 1;
v___x_2179_ = lean_string_utf8_next_fast(v___x_2171_, v_a_2172_);
v___x_2183_ = lean_string_utf8_get_fast(v___x_2171_, v_a_2172_);
lean_dec(v_a_2172_);
v___x_2191_ = 32;
v___x_2192_ = lean_uint32_dec_eq(v___x_2183_, v___x_2191_);
if (v___x_2192_ == 0)
{
uint32_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = 9;
v___x_2194_ = lean_uint32_dec_eq(v___x_2183_, v___x_2193_);
v___y_2185_ = v___x_2194_;
goto v___jp_2184_;
}
else
{
v___y_2185_ = v___x_2192_;
goto v___jp_2184_;
}
v___jp_2180_:
{
if (v___y_2181_ == 0)
{
return v___y_2181_;
}
else
{
v_a_2172_ = v___x_2179_;
v_b_2173_ = v___x_2178_;
goto _start;
}
}
v___jp_2184_:
{
if (v___y_2185_ == 0)
{
uint32_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = 13;
v___x_2187_ = lean_uint32_dec_eq(v___x_2183_, v___x_2186_);
if (v___x_2187_ == 0)
{
uint32_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = 10;
v___x_2189_ = lean_uint32_dec_eq(v___x_2183_, v___x_2188_);
v___y_2181_ = v___x_2189_;
goto v___jp_2180_;
}
else
{
v___y_2181_ = v___x_2187_;
goto v___jp_2180_;
}
}
else
{
v_a_2172_ = v___x_2179_;
v_b_2173_ = v___x_2178_;
goto _start;
}
}
}
else
{
lean_dec(v_a_2172_);
return v_b_2173_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg___boxed(lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v_a_2197_, lean_object* v_b_2198_){
_start:
{
uint8_t v_b_boxed_2199_; uint8_t v_res_2200_; lean_object* v_r_2201_; 
v_b_boxed_2199_ = lean_unbox(v_b_2198_);
v_res_2200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg(v___x_2195_, v___x_2196_, v_a_2197_, v_b_boxed_2199_);
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2195_);
v_r_2201_ = lean_box(v_res_2200_);
return v_r_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment(lean_object* v_a_2202_){
_start:
{
lean_object* v_openComment_x3f_2203_; 
v_openComment_x3f_2203_ = lean_ctor_get(v_a_2202_, 3);
if (lean_obj_tag(v_openComment_x3f_2203_) == 1)
{
lean_object* v_val_2204_; lean_object* v_toComment_2205_; lean_object* v_firstNewlinePos_2206_; lean_object* v_ws_2207_; lean_object* v_closedComments_2208_; lean_object* v_commentNestingLevel_2209_; uint8_t v_kind_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; uint8_t v___x_2217_; 
v_val_2204_ = lean_ctor_get(v_openComment_x3f_2203_, 0);
v_toComment_2205_ = lean_ctor_get(v_val_2204_, 0);
v_firstNewlinePos_2206_ = lean_ctor_get(v_a_2202_, 0);
v_ws_2207_ = lean_ctor_get(v_a_2202_, 1);
v_closedComments_2208_ = lean_ctor_get(v_a_2202_, 2);
v_commentNestingLevel_2209_ = lean_ctor_get(v_a_2202_, 4);
v_kind_2210_ = lean_ctor_get_uint8(v_toComment_2205_, sizeof(void*)*3);
v___x_2211_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(v_kind_2210_);
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = lean_string_utf8_byte_size(v___x_2211_);
lean_inc_ref(v___x_2211_);
v___x_2214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2211_);
lean_ctor_set(v___x_2214_, 1, v___x_2212_);
lean_ctor_set(v___x_2214_, 2, v___x_2213_);
v___x_2215_ = l_String_Slice_positions(v___x_2214_);
v___x_2216_ = 1;
v___x_2217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg(v___x_2214_, v___x_2211_, v___x_2215_, v___x_2216_);
lean_dec_ref(v___x_2211_);
lean_dec_ref_known(v___x_2214_, 3);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_a_2202_);
return v___x_2219_;
}
else
{
lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
lean_inc(v_commentNestingLevel_2209_);
lean_inc_ref(v_closedComments_2208_);
lean_inc_ref(v_ws_2207_);
lean_inc(v_firstNewlinePos_2206_);
lean_inc(v_val_2204_);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; 
v_unused_2231_ = lean_ctor_get(v_a_2202_, 4);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_a_2202_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_a_2202_, 2);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_a_2202_, 1);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_a_2202_, 0);
lean_dec(v_unused_2235_);
v___x_2221_ = v_a_2202_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_dec(v_a_2202_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_array_push(v_closedComments_2208_, v_val_2204_);
v___x_2225_ = lean_box(0);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v___x_2225_);
lean_ctor_set(v___x_2221_, 2, v___x_2224_);
v___x_2227_ = v___x_2221_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_firstNewlinePos_2206_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_ws_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_commentNestingLevel_2209_);
v___x_2227_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2223_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v_a_2202_);
return v___x_2237_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0(lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_inst_2240_, lean_object* v_R_2241_, lean_object* v_a_2242_, uint8_t v_b_2243_, lean_object* v_c_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___redArg(v___x_2238_, v___x_2239_, v_a_2242_, v_b_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0___boxed(lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_inst_2248_, lean_object* v_R_2249_, lean_object* v_a_2250_, lean_object* v_b_2251_, lean_object* v_c_2252_){
_start:
{
uint8_t v_b_boxed_2253_; uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_b_boxed_2253_ = lean_unbox(v_b_2251_);
v_res_2254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment_spec__0(v___x_2246_, v___x_2247_, v_inst_2248_, v_R_2249_, v_a_2250_, v_b_boxed_2253_, v_c_2252_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy(lean_object* v_pre_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_firstNewlinePos_2258_; lean_object* v_ws_2259_; lean_object* v_closedComments_2260_; lean_object* v_openComment_x3f_2261_; lean_object* v_commentNestingLevel_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2297_; 
v_firstNewlinePos_2258_ = lean_ctor_get(v_a_2257_, 0);
v_ws_2259_ = lean_ctor_get(v_a_2257_, 1);
v_closedComments_2260_ = lean_ctor_get(v_a_2257_, 2);
v_openComment_x3f_2261_ = lean_ctor_get(v_a_2257_, 3);
v_commentNestingLevel_2262_ = lean_ctor_get(v_a_2257_, 4);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_a_2257_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2264_ = v_a_2257_;
v_isShared_2265_ = v_isSharedCheck_2297_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_commentNestingLevel_2262_);
lean_inc(v_openComment_x3f_2261_);
lean_inc(v_closedComments_2260_);
lean_inc(v_ws_2259_);
lean_inc(v_firstNewlinePos_2258_);
lean_dec(v_a_2257_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2297_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___y_2269_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_spec__0(v_pre_2256_, v_ws_2259_);
if (lean_obj_tag(v_openComment_x3f_2261_) == 0)
{
v___y_2269_ = v_openComment_x3f_2261_;
goto v___jp_2268_;
}
else
{
lean_object* v_val_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2296_; 
v_val_2274_ = lean_ctor_get(v_openComment_x3f_2261_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_openComment_x3f_2261_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2276_ = v_openComment_x3f_2261_;
v_isShared_2277_ = v_isSharedCheck_2296_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_val_2274_);
lean_dec(v_openComment_x3f_2261_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2296_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_toComment_2278_; lean_object* v_raw_2279_; lean_object* v_startColumnOffset_2280_; lean_object* v_startPos_2281_; lean_object* v_endPos_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2295_; 
v_toComment_2278_ = lean_ctor_get(v_val_2274_, 0);
v_raw_2279_ = lean_ctor_get(v_val_2274_, 1);
v_startColumnOffset_2280_ = lean_ctor_get(v_val_2274_, 2);
v_startPos_2281_ = lean_ctor_get(v_val_2274_, 3);
v_endPos_2282_ = lean_ctor_get(v_val_2274_, 4);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_val_2274_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2284_ = v_val_2274_;
v_isShared_2285_ = v_isSharedCheck_2295_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_endPos_2282_);
lean_inc(v_startPos_2281_);
lean_inc(v_startColumnOffset_2280_);
lean_inc(v_raw_2279_);
lean_inc(v_toComment_2278_);
lean_dec(v_val_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2295_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2286_ = lean_string_append(v_raw_2279_, v_pre_2256_);
v___x_2287_ = lean_string_utf8_byte_size(v_pre_2256_);
v___x_2288_ = lean_nat_add(v_endPos_2282_, v___x_2287_);
lean_dec(v_endPos_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v___x_2288_);
lean_ctor_set(v___x_2284_, 1, v___x_2286_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_toComment_2278_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_startColumnOffset_2280_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_startPos_2281_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2290_);
v___x_2292_ = v___x_2276_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
v___y_2269_ = v___x_2292_;
goto v___jp_2268_;
}
}
}
}
}
v___jp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 3, v___y_2269_);
lean_ctor_set(v___x_2264_, 1, v___x_2267_);
v___x_2271_ = v___x_2264_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_firstNewlinePos_2258_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_closedComments_2260_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v___y_2269_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v_commentNestingLevel_2262_);
v___x_2271_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2266_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy___boxed(lean_object* v_pre_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy(v_pre_2298_, v_a_2299_);
lean_dec_ref(v_pre_2298_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(lean_object* v_pat_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_ws_2303_; lean_object* v_str_2304_; lean_object* v_startInclusive_2305_; lean_object* v_endExclusive_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_ws_2303_ = lean_ctor_get(v_a_2302_, 1);
v_str_2304_ = lean_ctor_get(v_ws_2303_, 0);
v_startInclusive_2305_ = lean_ctor_get(v_ws_2303_, 1);
v_endExclusive_2306_ = lean_ctor_get(v_ws_2303_, 2);
v___x_2307_ = lean_string_utf8_byte_size(v_pat_2301_);
v___x_2308_ = lean_nat_sub(v_endExclusive_2306_, v_startInclusive_2305_);
v___x_2309_ = lean_nat_dec_le(v___x_2307_, v___x_2308_);
lean_dec(v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_box(v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_a_2302_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_string_memcmp(v_str_2304_, v_pat_2301_, v_startInclusive_2305_, v___x_2312_, v___x_2307_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_box(v___x_2313_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v_a_2302_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; lean_object* v_snd_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
v___x_2316_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy(v_pat_2301_, v_a_2302_);
v_snd_2317_ = lean_ctor_get(v___x_2316_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2316_, 0);
lean_dec(v_unused_2326_);
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_snd_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_box(v___x_2313_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_snd_2317_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse___boxed(lean_object* v_pat_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(v_pat_2327_, v_a_2328_);
lean_dec_ref(v_pat_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryNestComment(lean_object* v_a_2330_){
_start:
{
lean_object* v_openComment_x3f_2331_; 
v_openComment_x3f_2331_ = lean_ctor_get(v_a_2330_, 3);
if (lean_obj_tag(v_openComment_x3f_2331_) == 1)
{
lean_object* v_val_2332_; lean_object* v_toComment_2333_; uint8_t v_kind_2334_; uint8_t v___x_2335_; 
v_val_2332_ = lean_ctor_get(v_openComment_x3f_2331_, 0);
v_toComment_2333_ = lean_ctor_get(v_val_2332_, 0);
v_kind_2334_ = lean_ctor_get_uint8(v_toComment_2333_, sizeof(void*)*3);
v___x_2335_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting(v_kind_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_box(v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_2330_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_fst_2340_; uint8_t v___x_2341_; 
v___x_2338_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(v_kind_2334_);
v___x_2339_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(v___x_2338_, v_a_2330_);
lean_dec_ref(v___x_2338_);
v_fst_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_fst_2340_);
v___x_2341_ = lean_unbox(v_fst_2340_);
lean_dec(v_fst_2340_);
if (v___x_2341_ == 0)
{
return v___x_2339_;
}
else
{
lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2364_; 
v_snd_2342_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2365_);
v___x_2344_ = v___x_2339_;
v_isShared_2345_ = v_isSharedCheck_2364_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_dec(v___x_2339_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2364_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_firstNewlinePos_2346_; lean_object* v_ws_2347_; lean_object* v_closedComments_2348_; lean_object* v_openComment_x3f_2349_; lean_object* v_commentNestingLevel_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2363_; 
v_firstNewlinePos_2346_ = lean_ctor_get(v_snd_2342_, 0);
v_ws_2347_ = lean_ctor_get(v_snd_2342_, 1);
v_closedComments_2348_ = lean_ctor_get(v_snd_2342_, 2);
v_openComment_x3f_2349_ = lean_ctor_get(v_snd_2342_, 3);
v_commentNestingLevel_2350_ = lean_ctor_get(v_snd_2342_, 4);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_snd_2342_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2352_ = v_snd_2342_;
v_isShared_2353_ = v_isSharedCheck_2363_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_commentNestingLevel_2350_);
lean_inc(v_openComment_x3f_2349_);
lean_inc(v_closedComments_2348_);
lean_inc(v_ws_2347_);
lean_inc(v_firstNewlinePos_2346_);
lean_dec(v_snd_2342_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2363_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_commentNestingLevel_2350_, v___x_2354_);
lean_dec(v_commentNestingLevel_2350_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 4, v___x_2355_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_firstNewlinePos_2346_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_ws_2347_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_closedComments_2348_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_openComment_x3f_2349_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_box(v___x_2335_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___x_2357_);
lean_ctor_set(v___x_2344_, 0, v___x_2358_);
v___x_2360_ = v___x_2344_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2357_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = 0;
v___x_2367_ = lean_box(v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_a_2330_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment_spec__0(lean_object* v_msg_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_Fmt_instInhabitedPendingComment_default;
v___x_2371_ = lean_panic_fn_borrowed(v___x_2370_, v_msg_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__2));
v___x_2376_ = lean_unsigned_to_nat(14u);
v___x_2377_ = lean_unsigned_to_nat(22u);
v___x_2378_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__1));
v___x_2379_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__0));
v___x_2380_ = l_mkPanicMessageWithDecl(v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_, v___x_2375_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment(lean_object* v_a_2381_){
_start:
{
lean_object* v_openComment_x3f_2382_; 
v_openComment_x3f_2382_ = lean_ctor_get(v_a_2381_, 3);
lean_inc(v_openComment_x3f_2382_);
if (lean_obj_tag(v_openComment_x3f_2382_) == 1)
{
lean_object* v_val_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2448_; 
v_val_2383_ = lean_ctor_get(v_openComment_x3f_2382_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_openComment_x3f_2382_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2385_ = v_openComment_x3f_2382_;
v_isShared_2386_ = v_isSharedCheck_2448_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_val_2383_);
lean_dec(v_openComment_x3f_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2448_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v_toComment_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2443_; 
v_toComment_2387_ = lean_ctor_get(v_val_2383_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_val_2383_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; lean_object* v_unused_2447_; 
v_unused_2444_ = lean_ctor_get(v_val_2383_, 4);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_val_2383_, 3);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_val_2383_, 2);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_val_2383_, 1);
lean_dec(v_unused_2447_);
v___x_2389_ = v_val_2383_;
v_isShared_2390_ = v_isSharedCheck_2443_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_toComment_2387_);
lean_dec(v_val_2383_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2443_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
uint8_t v_kind_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_fst_2394_; lean_object* v_snd_2395_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; uint8_t v___x_2408_; 
v_kind_2391_ = lean_ctor_get_uint8(v_toComment_2387_, sizeof(void*)*3);
lean_dec_ref(v_toComment_2387_);
v___x_2392_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_endSymbol(v_kind_2391_);
v___x_2393_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(v___x_2392_, v_a_2381_);
lean_dec_ref(v___x_2392_);
v_fst_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_fst_2394_);
v_snd_2395_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_snd_2395_);
v___x_2408_ = lean_unbox(v_fst_2394_);
if (v___x_2408_ == 0)
{
lean_dec(v_snd_2395_);
lean_dec(v_fst_2394_);
lean_del_object(v___x_2389_);
lean_del_object(v___x_2385_);
return v___x_2393_;
}
else
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2440_; 
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; lean_object* v_unused_2442_; 
v_unused_2441_ = lean_ctor_get(v___x_2393_, 1);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v___x_2393_, 0);
lean_dec(v_unused_2442_);
v___x_2410_ = v___x_2393_;
v_isShared_2411_ = v_isSharedCheck_2440_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v___x_2393_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2440_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_firstNewlinePos_2412_; lean_object* v_ws_2413_; lean_object* v_closedComments_2414_; lean_object* v_openComment_x3f_2415_; lean_object* v_commentNestingLevel_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2439_; 
v_firstNewlinePos_2412_ = lean_ctor_get(v_snd_2395_, 0);
v_ws_2413_ = lean_ctor_get(v_snd_2395_, 1);
v_closedComments_2414_ = lean_ctor_get(v_snd_2395_, 2);
v_openComment_x3f_2415_ = lean_ctor_get(v_snd_2395_, 3);
v_commentNestingLevel_2416_ = lean_ctor_get(v_snd_2395_, 4);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_snd_2395_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2418_ = v_snd_2395_;
v_isShared_2419_ = v_isSharedCheck_2439_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_commentNestingLevel_2416_);
lean_inc(v_openComment_x3f_2415_);
lean_inc(v_closedComments_2414_);
lean_inc(v_ws_2413_);
lean_inc(v_firstNewlinePos_2412_);
lean_dec(v_snd_2395_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2439_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___y_2421_; 
if (lean_obj_tag(v_openComment_x3f_2415_) == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
v___x_2437_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment_spec__0(v___x_2436_);
v___y_2421_ = v___x_2437_;
goto v___jp_2420_;
}
else
{
lean_object* v_val_2438_; 
v_val_2438_ = lean_ctor_get(v_openComment_x3f_2415_, 0);
lean_inc(v_val_2438_);
lean_dec_ref_known(v_openComment_x3f_2415_, 1);
v___y_2421_ = v_val_2438_;
goto v___jp_2420_;
}
v___jp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2422_ = lean_unsigned_to_nat(1u);
v___x_2423_ = lean_nat_sub(v_commentNestingLevel_2416_, v___x_2422_);
lean_dec(v_commentNestingLevel_2416_);
v___x_2424_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_hasNesting(v_kind_2391_);
if (v___x_2424_ == 0)
{
lean_del_object(v___x_2418_);
lean_del_object(v___x_2410_);
lean_del_object(v___x_2385_);
v___y_2397_ = v_closedComments_2414_;
v___y_2398_ = v_ws_2413_;
v___y_2399_ = v___y_2421_;
v___y_2400_ = v___x_2423_;
v___y_2401_ = v_firstNewlinePos_2412_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_nat_dec_eq(v___x_2423_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2428_; 
lean_del_object(v___x_2389_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___y_2421_);
v___x_2428_ = v___x_2385_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___y_2421_);
v___x_2428_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2430_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 4, v___x_2423_);
lean_ctor_set(v___x_2418_, 3, v___x_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_firstNewlinePos_2412_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_ws_2413_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_closedComments_2414_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v___x_2423_);
v___x_2430_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v___x_2430_);
v___x_2432_ = v___x_2410_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_fst_2394_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_del_object(v___x_2418_);
lean_del_object(v___x_2410_);
lean_del_object(v___x_2385_);
v___y_2397_ = v_closedComments_2414_;
v___y_2398_ = v_ws_2413_;
v___y_2399_ = v___y_2421_;
v___y_2400_ = v___x_2423_;
v___y_2401_ = v_firstNewlinePos_2412_;
goto v___jp_2396_;
}
}
}
}
}
}
v___jp_2396_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = lean_array_push(v___y_2397_, v___y_2399_);
v___x_2403_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 4, v___y_2400_);
lean_ctor_set(v___x_2389_, 3, v___x_2403_);
lean_ctor_set(v___x_2389_, 2, v___x_2402_);
lean_ctor_set(v___x_2389_, 1, v___y_2398_);
lean_ctor_set(v___x_2389_, 0, v___y_2401_);
v___x_2405_ = v___x_2389_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___y_2401_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___y_2398_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v___y_2400_);
v___x_2405_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_fst_2394_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
return v___x_2406_;
}
}
}
}
}
else
{
uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec(v_openComment_x3f_2382_);
v___x_2449_ = 0;
v___x_2450_ = lean_box(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v_a_2381_);
return v___x_2451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_skip(lean_object* v_a_2452_){
_start:
{
lean_object* v_ws_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_ws_2453_ = lean_ctor_get(v_a_2452_, 1);
v___x_2454_ = lean_unsigned_to_nat(0u);
v___x_2455_ = l_String_Slice_Pos_get_x3f(v_ws_2453_, v___x_2454_);
if (lean_obj_tag(v___x_2455_) == 1)
{
lean_object* v_val_2456_; lean_object* v___x_2457_; uint32_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_val_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = ((lean_object*)(l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__2___redArg___closed__0));
v___x_2458_ = lean_unbox_uint32(v_val_2456_);
lean_dec(v_val_2456_);
v___x_2459_ = lean_string_push(v___x_2457_, v___x_2458_);
v___x_2460_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_advanceBy(v___x_2459_, v_a_2452_);
lean_dec_ref(v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec(v___x_2455_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v_a_2452_);
return v___x_2462_;
}
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v___x_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0(lean_object* v_msg_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0, &l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0___closed__0);
v___x_2468_ = lean_panic_fn_borrowed(v___x_2467_, v_msg_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0(lean_object* v_x_2469_){
_start:
{
lean_object* v_startPos_2470_; 
v_startPos_2470_ = lean_ctor_get(v_x_2469_, 4);
lean_inc(v_startPos_2470_);
return v_startPos_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0___boxed(lean_object* v_x_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___lam__0(v_x_2471_);
lean_dec_ref(v_x_2471_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment(lean_object* v_lineInfos_2475_, lean_object* v_originalTokenRange_2476_, uint8_t v_originalWhitespaceKind_2477_, uint8_t v_kind_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_ws_2480_; lean_object* v_firstNewlinePos_2481_; lean_object* v_str_2482_; lean_object* v_startInclusive_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2548_; 
v_ws_2480_ = lean_ctor_get(v_a_2479_, 1);
lean_inc_ref(v_ws_2480_);
v_firstNewlinePos_2481_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_firstNewlinePos_2481_);
v_str_2482_ = lean_ctor_get(v_ws_2480_, 0);
v_startInclusive_2483_ = lean_ctor_get(v_ws_2480_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_ws_2480_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v_ws_2480_, 2);
lean_dec(v_unused_2549_);
v___x_2485_ = v_ws_2480_;
v_isShared_2486_ = v_isSharedCheck_2548_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_startInclusive_2483_);
lean_inc(v_str_2482_);
lean_dec(v_ws_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2548_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___y_2488_; lean_object* v___y_2489_; uint8_t v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; uint8_t v___y_2495_; lean_object* v___y_2508_; lean_object* v___y_2509_; uint8_t v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2517_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___f_2542_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__0));
v___f_2543_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1));
lean_inc(v_startInclusive_2483_);
v___x_2544_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_2475_, v_startInclusive_2483_, v___f_2542_, v___f_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
v___x_2546_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0(v___x_2545_);
v___y_2517_ = v___x_2546_;
goto v___jp_2516_;
}
else
{
lean_object* v_val_2547_; 
v_val_2547_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_val_2547_);
lean_dec_ref_known(v___x_2544_, 1);
v___y_2517_ = v_val_2547_;
goto v___jp_2516_;
}
v___jp_2487_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_inc_n(v___y_2489_, 2);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2489_);
lean_ctor_set(v___x_2496_, 1, v___y_2489_);
v___x_2497_ = lean_mk_empty_array_with_capacity(v___y_2489_);
lean_dec(v___y_2489_);
v___x_2498_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2498_, 0, v_originalTokenRange_2476_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3, v_kind_2478_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 1, v___y_2495_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_2477_);
v___x_2499_ = lean_string_utf8_byte_size(v___y_2492_);
v___x_2500_ = lean_nat_add(v_startInclusive_2483_, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___y_2492_);
lean_ctor_set(v___x_2501_, 2, v___y_2488_);
lean_ctor_set(v___x_2501_, 3, v_startInclusive_2483_);
lean_ctor_set(v___x_2501_, 4, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2504_, 0, v___y_2491_);
lean_ctor_set(v___x_2504_, 1, v___y_2494_);
lean_ctor_set(v___x_2504_, 2, v___y_2493_);
lean_ctor_set(v___x_2504_, 3, v___x_2502_);
lean_ctor_set(v___x_2504_, 4, v___x_2503_);
v___x_2505_ = lean_box(v___y_2490_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
return v___x_2506_;
}
v___jp_2507_:
{
uint8_t v___x_2515_; 
v___x_2515_ = 1;
v___y_2488_ = v___y_2508_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
v___y_2491_ = v___y_2512_;
v___y_2492_ = v___y_2511_;
v___y_2493_ = v___y_2513_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___x_2515_;
goto v___jp_2487_;
}
v___jp_2516_:
{
lean_object* v_snd_2518_; lean_object* v_startPos_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_fst_2522_; uint8_t v___x_2523_; 
v_snd_2518_ = lean_ctor_get(v___y_2517_, 1);
lean_inc(v_snd_2518_);
lean_dec_ref(v___y_2517_);
v_startPos_2519_ = lean_ctor_get(v_snd_2518_, 4);
lean_inc(v_startPos_2519_);
lean_dec(v_snd_2518_);
v___x_2520_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_Kind_startSymbol(v_kind_2478_);
v___x_2521_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryParse(v___x_2520_, v_a_2479_);
v_fst_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_fst_2522_);
v___x_2523_ = lean_unbox(v_fst_2522_);
if (v___x_2523_ == 0)
{
lean_dec(v_fst_2522_);
lean_dec_ref(v___x_2520_);
lean_dec(v_startPos_2519_);
lean_del_object(v___x_2485_);
lean_dec(v_startInclusive_2483_);
lean_dec_ref(v_str_2482_);
lean_dec(v_firstNewlinePos_2481_);
lean_dec_ref(v_originalTokenRange_2476_);
return v___x_2521_;
}
else
{
lean_object* v_snd_2524_; lean_object* v___x_2525_; lean_object* v_firstNewlinePos_2526_; lean_object* v_ws_2527_; lean_object* v_closedComments_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v_snd_2524_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2524_);
lean_dec_ref(v___x_2521_);
v___x_2525_ = lean_string_utf8_byte_size(v_str_2482_);
v_firstNewlinePos_2526_ = lean_ctor_get(v_snd_2524_, 0);
lean_inc(v_firstNewlinePos_2526_);
v_ws_2527_ = lean_ctor_get(v_snd_2524_, 1);
lean_inc_ref(v_ws_2527_);
v_closedComments_2528_ = lean_ctor_get(v_snd_2524_, 2);
lean_inc_ref(v_closedComments_2528_);
lean_dec(v_snd_2524_);
v___x_2529_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_str_2482_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 2, v___x_2525_);
lean_ctor_set(v___x_2485_, 1, v___x_2529_);
v___x_2531_ = v___x_2485_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_str_2482_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v___x_2525_);
v___x_2531_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = l_String_Slice_pos_x21(v___x_2531_, v_startPos_2519_);
lean_dec(v_startPos_2519_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = l_String_slice_x21(v_str_2482_, v___x_2532_, v_startInclusive_2483_);
lean_dec(v___x_2532_);
v___x_2534_ = l_String_Slice_positions(v___x_2533_);
v___x_2535_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__2___redArg(v___x_2533_, v___x_2534_, v___x_2529_);
lean_dec_ref(v___x_2533_);
if (v_originalWhitespaceKind_2477_ == 0)
{
uint8_t v___x_2536_; 
lean_dec(v_firstNewlinePos_2481_);
v___x_2536_ = lean_unbox(v_fst_2522_);
lean_dec(v_fst_2522_);
v___y_2508_ = v___x_2535_;
v___y_2509_ = v___x_2529_;
v___y_2510_ = v___x_2536_;
v___y_2511_ = v___x_2520_;
v___y_2512_ = v_firstNewlinePos_2526_;
v___y_2513_ = v_closedComments_2528_;
v___y_2514_ = v_ws_2527_;
goto v___jp_2507_;
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_nat_dec_le(v_firstNewlinePos_2481_, v_startInclusive_2483_);
lean_dec(v_firstNewlinePos_2481_);
if (v___x_2537_ == 0)
{
uint8_t v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = 0;
v___x_2539_ = lean_unbox(v_fst_2522_);
lean_dec(v_fst_2522_);
v___y_2488_ = v___x_2535_;
v___y_2489_ = v___x_2529_;
v___y_2490_ = v___x_2539_;
v___y_2491_ = v_firstNewlinePos_2526_;
v___y_2492_ = v___x_2520_;
v___y_2493_ = v_closedComments_2528_;
v___y_2494_ = v_ws_2527_;
v___y_2495_ = v___x_2538_;
goto v___jp_2487_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_unbox(v_fst_2522_);
lean_dec(v_fst_2522_);
v___y_2508_ = v___x_2535_;
v___y_2509_ = v___x_2529_;
v___y_2510_ = v___x_2540_;
v___y_2511_ = v___x_2520_;
v___y_2512_ = v_firstNewlinePos_2526_;
v___y_2513_ = v_closedComments_2528_;
v___y_2514_ = v_ws_2527_;
goto v___jp_2507_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___boxed(lean_object* v_lineInfos_2550_, lean_object* v_originalTokenRange_2551_, lean_object* v_originalWhitespaceKind_2552_, lean_object* v_kind_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2555_; uint8_t v_kind_boxed_2556_; lean_object* v_res_2557_; 
v_originalWhitespaceKind_boxed_2555_ = lean_unbox(v_originalWhitespaceKind_2552_);
v_kind_boxed_2556_ = lean_unbox(v_kind_2553_);
v_res_2557_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment(v_lineInfos_2550_, v_originalTokenRange_2551_, v_originalWhitespaceKind_boxed_2555_, v_kind_boxed_2556_, v_a_2554_);
lean_dec_ref(v_lineInfos_2550_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0(lean_object* v_lineInfos_2558_, lean_object* v_originalTokenRange_2559_, uint8_t v_originalWhitespaceKind_2560_, lean_object* v_as_2561_, size_t v_sz_2562_, size_t v_i_2563_, uint8_t v_b_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_lt(v_i_2563_, v_sz_2562_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref(v_originalTokenRange_2559_);
v___x_2567_ = lean_box(v_b_2564_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___y_2565_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v_fst_2572_; uint8_t v___x_2573_; 
v_a_2569_ = lean_array_uget_borrowed(v_as_2561_, v_i_2563_);
v___x_2570_ = lean_unbox(v_a_2569_);
lean_inc_ref(v_originalTokenRange_2559_);
v___x_2571_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment(v_lineInfos_2558_, v_originalTokenRange_2559_, v_originalWhitespaceKind_2560_, v___x_2570_, v___y_2565_);
v_fst_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_fst_2572_);
v___x_2573_ = lean_unbox(v_fst_2572_);
if (v___x_2573_ == 0)
{
lean_object* v_snd_2574_; size_t v___x_2575_; size_t v___x_2576_; 
lean_dec(v_fst_2572_);
v_snd_2574_ = lean_ctor_get(v___x_2571_, 1);
lean_inc(v_snd_2574_);
lean_dec_ref(v___x_2571_);
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2563_, v___x_2575_);
v_i_2563_ = v___x_2576_;
v___y_2565_ = v_snd_2574_;
goto _start;
}
else
{
lean_object* v_snd_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_originalTokenRange_2559_);
v_snd_2578_ = lean_ctor_get(v___x_2571_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2571_, 0);
lean_dec(v_unused_2586_);
v___x_2580_ = v___x_2571_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_snd_2578_);
lean_dec(v___x_2571_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_snd_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0___boxed(lean_object* v_lineInfos_2587_, lean_object* v_originalTokenRange_2588_, lean_object* v_originalWhitespaceKind_2589_, lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2595_; size_t v_sz_boxed_2596_; size_t v_i_boxed_2597_; uint8_t v_b_boxed_2598_; lean_object* v_res_2599_; 
v_originalWhitespaceKind_boxed_2595_ = lean_unbox(v_originalWhitespaceKind_2589_);
v_sz_boxed_2596_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2597_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_b_boxed_2598_ = lean_unbox(v_b_2593_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0(v_lineInfos_2587_, v_originalTokenRange_2588_, v_originalWhitespaceKind_boxed_2595_, v_as_2590_, v_sz_boxed_2596_, v_i_boxed_2597_, v_b_boxed_2598_, v___y_2594_);
lean_dec_ref(v_as_2590_);
lean_dec_ref(v_lineInfos_2587_);
return v_res_2599_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2600_ = 0;
v___x_2601_ = lean_unsigned_to_nat(2u);
v___x_2602_ = lean_mk_empty_array_with_capacity(v___x_2601_);
v___x_2603_ = lean_box(v___x_2600_);
v___x_2604_ = lean_array_push(v___x_2602_, v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1(void){
_start:
{
uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_kinds_2608_; 
v___x_2605_ = 1;
v___x_2606_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__0);
v___x_2607_ = lean_box(v___x_2605_);
v_kinds_2608_ = lean_array_push(v___x_2606_, v___x_2607_);
return v_kinds_2608_;
}
}
static size_t _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v_kinds_2609_; size_t v_sz_2610_; 
v_kinds_2609_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1);
v_sz_2610_ = lean_array_size(v_kinds_2609_);
return v_sz_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg(lean_object* v_lineInfos_2611_, lean_object* v_originalTokenRange_2612_, uint8_t v_originalWhitespaceKind_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_ws_2615_; lean_object* v_openComment_x3f_2616_; lean_object* v_startInclusive_2617_; lean_object* v_endExclusive_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_ws_2615_ = lean_ctor_get(v___y_2614_, 1);
v_openComment_x3f_2616_ = lean_ctor_get(v___y_2614_, 3);
v_startInclusive_2617_ = lean_ctor_get(v_ws_2615_, 1);
v_endExclusive_2618_ = lean_ctor_get(v_ws_2615_, 2);
v___x_2619_ = lean_nat_sub(v_endExclusive_2618_, v_startInclusive_2617_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_nat_dec_eq(v___x_2619_, v___x_2620_);
lean_dec(v___x_2619_);
if (v___x_2621_ == 0)
{
if (lean_obj_tag(v_openComment_x3f_2616_) == 0)
{
lean_object* v_kinds_2622_; size_t v_sz_2623_; size_t v___x_2624_; lean_object* v___x_2625_; lean_object* v_fst_2626_; uint8_t v___x_2627_; 
v_kinds_2622_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__1);
v_sz_2623_ = lean_usize_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___closed__2);
v___x_2624_ = ((size_t)0ULL);
lean_inc_ref(v_originalTokenRange_2612_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__0(v_lineInfos_2611_, v_originalTokenRange_2612_, v_originalWhitespaceKind_2613_, v_kinds_2622_, v_sz_2623_, v___x_2624_, v___x_2621_, v___y_2614_);
v_fst_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_fst_2626_);
v___x_2627_ = lean_unbox(v_fst_2626_);
lean_dec(v_fst_2626_);
if (v___x_2627_ == 0)
{
lean_object* v_snd_2628_; lean_object* v___x_2629_; lean_object* v_snd_2630_; 
v_snd_2628_ = lean_ctor_get(v___x_2625_, 1);
lean_inc(v_snd_2628_);
lean_dec_ref(v___x_2625_);
v___x_2629_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_skip(v_snd_2628_);
v_snd_2630_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_snd_2630_);
lean_dec_ref(v___x_2629_);
v___y_2614_ = v_snd_2630_;
goto _start;
}
else
{
lean_object* v_snd_2632_; 
v_snd_2632_ = lean_ctor_get(v___x_2625_, 1);
lean_inc(v_snd_2632_);
lean_dec_ref(v___x_2625_);
v___y_2614_ = v_snd_2632_;
goto _start;
}
}
else
{
lean_object* v___x_2634_; lean_object* v_fst_2635_; uint8_t v___x_2636_; 
v___x_2634_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment(v___y_2614_);
v_fst_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_fst_2635_);
v___x_2636_ = lean_unbox(v_fst_2635_);
lean_dec(v_fst_2635_);
if (v___x_2636_ == 0)
{
lean_object* v_snd_2637_; lean_object* v___x_2638_; lean_object* v_fst_2639_; uint8_t v___x_2640_; 
v_snd_2637_ = lean_ctor_get(v___x_2634_, 1);
lean_inc(v_snd_2637_);
lean_dec_ref(v___x_2634_);
v___x_2638_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryNestComment(v_snd_2637_);
v_fst_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_fst_2639_);
v___x_2640_ = lean_unbox(v_fst_2639_);
lean_dec(v_fst_2639_);
if (v___x_2640_ == 0)
{
lean_object* v_snd_2641_; lean_object* v___x_2642_; lean_object* v_snd_2643_; 
v_snd_2641_ = lean_ctor_get(v___x_2638_, 1);
lean_inc(v_snd_2641_);
lean_dec_ref(v___x_2638_);
v___x_2642_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_skip(v_snd_2641_);
v_snd_2643_ = lean_ctor_get(v___x_2642_, 1);
lean_inc(v_snd_2643_);
lean_dec_ref(v___x_2642_);
v___y_2614_ = v_snd_2643_;
goto _start;
}
else
{
lean_object* v_snd_2645_; 
v_snd_2645_ = lean_ctor_get(v___x_2638_, 1);
lean_inc(v_snd_2645_);
lean_dec_ref(v___x_2638_);
v___y_2614_ = v_snd_2645_;
goto _start;
}
}
else
{
lean_object* v_snd_2647_; 
v_snd_2647_ = lean_ctor_get(v___x_2634_, 1);
lean_inc(v_snd_2647_);
lean_dec_ref(v___x_2634_);
v___y_2614_ = v_snd_2647_;
goto _start;
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v_originalTokenRange_2612_);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___y_2614_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg___boxed(lean_object* v_lineInfos_2651_, lean_object* v_originalTokenRange_2652_, lean_object* v_originalWhitespaceKind_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2655_; lean_object* v_res_2656_; 
v_originalWhitespaceKind_boxed_2655_ = lean_unbox(v_originalWhitespaceKind_2653_);
v_res_2656_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg(v_lineInfos_2651_, v_originalTokenRange_2652_, v_originalWhitespaceKind_boxed_2655_, v___y_2654_);
lean_dec_ref(v_lineInfos_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go(lean_object* v_lineInfos_2657_, lean_object* v_originalTokenRange_2658_, uint8_t v_originalWhitespaceKind_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2661_; lean_object* v_snd_2662_; lean_object* v___x_2663_; 
v___x_2661_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg(v_lineInfos_2657_, v_originalTokenRange_2658_, v_originalWhitespaceKind_2659_, v_a_2660_);
v_snd_2662_ = lean_ctor_get(v___x_2661_, 1);
lean_inc(v_snd_2662_);
lean_dec_ref(v___x_2661_);
v___x_2663_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_terminateEndOfWhitespaceComment(v_snd_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go___boxed(lean_object* v_lineInfos_2664_, lean_object* v_originalTokenRange_2665_, lean_object* v_originalWhitespaceKind_2666_, lean_object* v_a_2667_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2668_; lean_object* v_res_2669_; 
v_originalWhitespaceKind_boxed_2668_ = lean_unbox(v_originalWhitespaceKind_2666_);
v_res_2669_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go(v_lineInfos_2664_, v_originalTokenRange_2665_, v_originalWhitespaceKind_boxed_2668_, v_a_2667_);
lean_dec_ref(v_lineInfos_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1(lean_object* v_lineInfos_2670_, lean_object* v_originalTokenRange_2671_, uint8_t v_originalWhitespaceKind_2672_, lean_object* v_inst_2673_, lean_object* v_a_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___redArg(v_lineInfos_2670_, v_originalTokenRange_2671_, v_originalWhitespaceKind_2672_, v___y_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1___boxed(lean_object* v_lineInfos_2677_, lean_object* v_originalTokenRange_2678_, lean_object* v_originalWhitespaceKind_2679_, lean_object* v_inst_2680_, lean_object* v_a_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2683_; lean_object* v_res_2684_; 
v_originalWhitespaceKind_boxed_2683_ = lean_unbox(v_originalWhitespaceKind_2679_);
v_res_2684_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go_spec__1(v_lineInfos_2677_, v_originalTokenRange_2678_, v_originalWhitespaceKind_boxed_2683_, v_inst_2680_, v_a_2681_, v___y_2682_);
lean_dec_ref(v_lineInfos_2677_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0(lean_object* v___y_2685_){
_start:
{
lean_inc(v___y_2685_);
return v___y_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0___boxed(lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___lam__0(v___y_2686_);
lean_dec(v___y_2686_);
return v_res_2687_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable(lean_object* v_newlinePositions_2689_, lean_object* v_group_2690_, lean_object* v_c_2691_){
_start:
{
lean_object* v_toComment_2692_; uint8_t v_kind_2693_; 
v_toComment_2692_ = lean_ctor_get(v_group_2690_, 0);
v_kind_2693_ = lean_ctor_get_uint8(v_toComment_2692_, sizeof(void*)*3);
if (v_kind_2693_ == 0)
{
lean_object* v_toComment_2694_; uint8_t v_kind_2695_; 
v_toComment_2694_ = lean_ctor_get(v_c_2691_, 0);
lean_inc_ref(v_toComment_2694_);
v_kind_2695_ = lean_ctor_get_uint8(v_toComment_2694_, sizeof(void*)*3);
if (v_kind_2695_ == 0)
{
lean_object* v_startColumnOffset_2696_; lean_object* v_endPos_2697_; uint8_t v_placement_2698_; lean_object* v_startColumnOffset_2699_; lean_object* v_startPos_2700_; uint8_t v_placement_2701_; lean_object* v___f_2702_; lean_object* v___f_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; 
v_startColumnOffset_2696_ = lean_ctor_get(v_group_2690_, 2);
v_endPos_2697_ = lean_ctor_get(v_group_2690_, 4);
v_placement_2698_ = lean_ctor_get_uint8(v_toComment_2692_, sizeof(void*)*3 + 1);
v_startColumnOffset_2699_ = lean_ctor_get(v_c_2691_, 2);
lean_inc(v_startColumnOffset_2699_);
v_startPos_2700_ = lean_ctor_get(v_c_2691_, 3);
lean_inc(v_startPos_2700_);
lean_dec_ref(v_c_2691_);
v_placement_2701_ = lean_ctor_get_uint8(v_toComment_2694_, sizeof(void*)*3 + 1);
lean_dec_ref(v_toComment_2694_);
v___f_2702_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___closed__0));
v___f_2703_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1));
v___x_2704_ = 1;
v___x_2705_ = 0;
if (v_placement_2698_ == 0)
{
if (v_placement_2701_ == 0)
{
lean_dec(v_startColumnOffset_2699_);
goto v___jp_2706_;
}
else
{
uint8_t v___x_2711_; 
v___x_2711_ = lean_nat_dec_eq(v_startColumnOffset_2696_, v_startColumnOffset_2699_);
lean_dec(v_startColumnOffset_2699_);
if (v___x_2711_ == 0)
{
lean_dec(v_startPos_2700_);
return v___x_2705_;
}
else
{
goto v___jp_2706_;
}
}
}
else
{
lean_dec(v_startColumnOffset_2699_);
if (v_placement_2701_ == 0)
{
lean_dec(v_startPos_2700_);
return v___x_2705_;
}
else
{
goto v___jp_2706_;
}
}
v___jp_2706_:
{
lean_object* v_newlineBeforeC_x3f_2707_; 
v_newlineBeforeC_x3f_2707_ = l_Lean_Fmt_binSearchRightmost___redArg(v_newlinePositions_2689_, v_startPos_2700_, v___f_2702_, v___f_2703_);
if (lean_obj_tag(v_newlineBeforeC_x3f_2707_) == 1)
{
lean_object* v_val_2708_; lean_object* v_snd_2709_; uint8_t v___x_2710_; 
v_val_2708_ = lean_ctor_get(v_newlineBeforeC_x3f_2707_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_newlineBeforeC_x3f_2707_, 1);
v_snd_2709_ = lean_ctor_get(v_val_2708_, 1);
lean_inc(v_snd_2709_);
lean_dec(v_val_2708_);
v___x_2710_ = lean_nat_dec_lt(v_snd_2709_, v_endPos_2697_);
lean_dec(v_snd_2709_);
if (v___x_2710_ == 0)
{
return v___x_2705_;
}
else
{
return v___x_2704_;
}
}
else
{
lean_dec(v_newlineBeforeC_x3f_2707_);
return v___x_2704_;
}
}
}
else
{
uint8_t v___x_2712_; 
lean_dec_ref(v_toComment_2694_);
lean_dec_ref(v_c_2691_);
v___x_2712_ = 0;
return v___x_2712_;
}
}
else
{
uint8_t v___x_2713_; 
lean_dec_ref(v_c_2691_);
v___x_2713_ = 0;
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable___boxed(lean_object* v_newlinePositions_2714_, lean_object* v_group_2715_, lean_object* v_c_2716_){
_start:
{
uint8_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable(v_newlinePositions_2714_, v_group_2715_, v_c_2716_);
lean_dec_ref(v_group_2715_);
lean_dec_ref(v_newlinePositions_2714_);
v_r_2718_ = lean_box(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg(lean_object* v_initialWs_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_){
_start:
{
lean_object* v_str_2722_; lean_object* v_startInclusive_2723_; lean_object* v_endExclusive_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_str_2722_ = lean_ctor_get(v_initialWs_2719_, 0);
v_startInclusive_2723_ = lean_ctor_get(v_initialWs_2719_, 1);
v_endExclusive_2724_ = lean_ctor_get(v_initialWs_2719_, 2);
v___x_2725_ = lean_nat_sub(v_endExclusive_2724_, v_startInclusive_2723_);
v___x_2726_ = lean_nat_dec_eq(v_a_2720_, v___x_2725_);
lean_dec(v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; uint32_t v___x_2728_; uint32_t v___x_2729_; uint8_t v___x_2730_; 
v___x_2727_ = lean_nat_add(v_startInclusive_2723_, v_a_2720_);
v___x_2728_ = lean_string_utf8_get_fast(v_str_2722_, v___x_2727_);
v___x_2729_ = 10;
v___x_2730_ = lean_uint32_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v_a_2720_);
v___x_2731_ = lean_string_utf8_next_fast(v_str_2722_, v___x_2727_);
lean_dec(v___x_2727_);
v___x_2732_ = lean_nat_sub(v___x_2731_, v_startInclusive_2723_);
v_a_2720_ = v___x_2732_;
goto _start;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = lean_string_utf8_next_fast(v_str_2722_, v___x_2727_);
v___x_2735_ = lean_nat_sub(v___x_2734_, v___x_2727_);
v___x_2736_ = lean_nat_add(v_a_2720_, v___x_2735_);
lean_dec(v___x_2735_);
lean_dec(v_a_2720_);
v___x_2737_ = lean_array_push(v_b_2721_, v___x_2727_);
v_a_2720_ = v___x_2736_;
v_b_2721_ = v___x_2737_;
goto _start;
}
}
else
{
lean_dec(v_a_2720_);
return v_b_2721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg___boxed(lean_object* v_initialWs_2739_, lean_object* v_a_2740_, lean_object* v_b_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg(v_initialWs_2739_, v_a_2740_, v_b_2741_);
lean_dec_ref(v_initialWs_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg(lean_object* v_newlinePositions_2743_, lean_object* v___x_2744_, lean_object* v_a_2745_, lean_object* v_b_2746_){
_start:
{
lean_object* v_array_2747_; lean_object* v_start_2748_; lean_object* v_stop_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2828_; 
v_array_2747_ = lean_ctor_get(v_a_2745_, 0);
v_start_2748_ = lean_ctor_get(v_a_2745_, 1);
v_stop_2749_ = lean_ctor_get(v_a_2745_, 2);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_a_2745_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2751_ = v_a_2745_;
v_isShared_2752_ = v_isSharedCheck_2828_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_stop_2749_);
lean_inc(v_start_2748_);
lean_inc(v_array_2747_);
lean_dec(v_a_2745_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2828_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_nat_dec_lt(v_start_2748_, v_stop_2749_);
if (v___x_2753_ == 0)
{
lean_del_object(v___x_2751_);
lean_dec(v_stop_2749_);
lean_dec(v_start_2748_);
lean_dec_ref(v_array_2747_);
return v_b_2746_;
}
else
{
lean_object* v_fst_2754_; lean_object* v_snd_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2827_; 
v_fst_2754_ = lean_ctor_get(v_b_2746_, 0);
v_snd_2755_ = lean_ctor_get(v_b_2746_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_b_2746_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2757_ = v_b_2746_;
v_isShared_2758_ = v_isSharedCheck_2827_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_snd_2755_);
lean_inc(v_fst_2754_);
lean_dec(v_b_2746_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2827_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2759_ = lean_unsigned_to_nat(1u);
v___x_2760_ = lean_nat_add(v_start_2748_, v___x_2759_);
lean_inc_ref(v_array_2747_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2760_);
v___x_2762_ = v___x_2751_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_array_2747_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_stop_2749_);
v___x_2762_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; uint8_t v___x_2770_; 
v___x_2763_ = lean_array_fget(v_array_2747_, v_start_2748_);
lean_dec(v_start_2748_);
lean_dec_ref(v_array_2747_);
lean_inc(v___x_2763_);
v___x_2770_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_isGroupable(v_newlinePositions_2743_, v_snd_2755_, v___x_2763_);
if (v___x_2770_ == 0)
{
goto v___jp_2764_;
}
else
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_nat_dec_eq(v___x_2744_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v_toComment_2773_; lean_object* v_originalWhitespaceRange_2774_; lean_object* v_toComment_2775_; lean_object* v_originalWhitespaceRange_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2823_; 
lean_del_object(v___x_2757_);
v_toComment_2773_ = lean_ctor_get(v_snd_2755_, 0);
lean_inc_ref(v_toComment_2773_);
v_originalWhitespaceRange_2774_ = lean_ctor_get(v_toComment_2773_, 1);
lean_inc_ref(v_originalWhitespaceRange_2774_);
v_toComment_2775_ = lean_ctor_get(v___x_2763_, 0);
lean_inc_ref(v_toComment_2775_);
v_originalWhitespaceRange_2776_ = lean_ctor_get(v_toComment_2775_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_toComment_2775_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; lean_object* v_unused_2825_; 
v_unused_2824_ = lean_ctor_get(v_toComment_2775_, 2);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_toComment_2775_, 0);
lean_dec(v_unused_2825_);
v___x_2778_ = v_toComment_2775_;
v_isShared_2779_ = v_isSharedCheck_2823_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_originalWhitespaceRange_2776_);
lean_dec(v_toComment_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2823_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_raw_2780_; lean_object* v_startColumnOffset_2781_; lean_object* v_startPos_2782_; uint8_t v_placement_2783_; lean_object* v_originalTokenRange_2784_; uint8_t v_originalWhitespaceKind_2785_; lean_object* v_start_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2821_; 
v_raw_2780_ = lean_ctor_get(v_snd_2755_, 1);
lean_inc_ref(v_raw_2780_);
v_startColumnOffset_2781_ = lean_ctor_get(v_snd_2755_, 2);
lean_inc(v_startColumnOffset_2781_);
v_startPos_2782_ = lean_ctor_get(v_snd_2755_, 3);
lean_inc(v_startPos_2782_);
lean_dec(v_snd_2755_);
v_placement_2783_ = lean_ctor_get_uint8(v_toComment_2773_, sizeof(void*)*3 + 1);
v_originalTokenRange_2784_ = lean_ctor_get(v_toComment_2773_, 0);
lean_inc_ref(v_originalTokenRange_2784_);
v_originalWhitespaceKind_2785_ = lean_ctor_get_uint8(v_toComment_2773_, sizeof(void*)*3 + 2);
lean_dec_ref(v_toComment_2773_);
v_start_2786_ = lean_ctor_get(v_originalWhitespaceRange_2774_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_originalWhitespaceRange_2774_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_originalWhitespaceRange_2774_, 1);
lean_dec(v_unused_2822_);
v___x_2788_ = v_originalWhitespaceRange_2774_;
v_isShared_2789_ = v_isSharedCheck_2821_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_start_2786_);
lean_dec(v_originalWhitespaceRange_2774_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2821_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_raw_2790_; lean_object* v_endPos_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2817_; 
v_raw_2790_ = lean_ctor_get(v___x_2763_, 1);
v_endPos_2791_ = lean_ctor_get(v___x_2763_, 4);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; lean_object* v_unused_2819_; lean_object* v_unused_2820_; 
v_unused_2818_ = lean_ctor_get(v___x_2763_, 3);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v___x_2763_, 2);
lean_dec(v_unused_2819_);
v_unused_2820_ = lean_ctor_get(v___x_2763_, 0);
lean_dec(v_unused_2820_);
v___x_2793_ = v___x_2763_;
v_isShared_2794_ = v_isSharedCheck_2817_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_endPos_2791_);
lean_inc(v_raw_2790_);
lean_dec(v___x_2763_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2817_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_stop_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2815_; 
v_stop_2795_ = lean_ctor_get(v_originalWhitespaceRange_2776_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_originalWhitespaceRange_2776_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_originalWhitespaceRange_2776_, 0);
lean_dec(v_unused_2816_);
v___x_2797_ = v_originalWhitespaceRange_2776_;
v_isShared_2798_ = v_isSharedCheck_2815_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_stop_2795_);
lean_dec(v_originalWhitespaceRange_2776_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2815_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint8_t v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = 0;
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_start_2786_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_start_2786_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_stop_2795_);
v___x_2801_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__String_indent___closed__0));
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 2, v___x_2802_);
lean_ctor_set(v___x_2778_, 1, v___x_2801_);
lean_ctor_set(v___x_2778_, 0, v_originalTokenRange_2784_);
v___x_2804_ = v___x_2778_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_originalTokenRange_2784_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3, v___x_2799_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3 + 1, v_placement_2783_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_2785_);
v___x_2805_ = lean_string_append(v_raw_2780_, v_raw_2790_);
lean_dec_ref(v_raw_2790_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 3, v_startPos_2782_);
lean_ctor_set(v___x_2793_, 2, v_startColumnOffset_2781_);
lean_ctor_set(v___x_2793_, 1, v___x_2805_);
lean_ctor_set(v___x_2793_, 0, v___x_2804_);
v___x_2807_ = v___x_2793_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_startColumnOffset_2781_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_startPos_2782_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_endPos_2791_);
v___x_2807_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2807_);
lean_ctor_set(v___x_2788_, 0, v_fst_2754_);
v___x_2809_ = v___x_2788_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_fst_2754_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
v_a_2745_ = v___x_2762_;
v_b_2746_ = v___x_2809_;
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
else
{
goto v___jp_2764_;
}
}
v___jp_2764_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_array_push(v_fst_2754_, v_snd_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2763_);
lean_ctor_set(v___x_2757_, 0, v___x_2765_);
v___x_2767_ = v___x_2757_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2763_);
v___x_2767_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
v_a_2745_ = v___x_2762_;
v_b_2746_ = v___x_2767_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg___boxed(lean_object* v_newlinePositions_2829_, lean_object* v___x_2830_, lean_object* v_a_2831_, lean_object* v_b_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg(v_newlinePositions_2829_, v___x_2830_, v_a_2831_, v_b_2832_);
lean_dec(v___x_2830_);
lean_dec_ref(v_newlinePositions_2829_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments(lean_object* v_initialWs_2838_, lean_object* v_comments_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v_newlinePositions_2841_; uint8_t v___x_2842_; 
v___x_2840_ = lean_array_get_size(v_comments_2839_);
v_newlinePositions_2841_ = lean_unsigned_to_nat(0u);
v___x_2842_ = lean_nat_dec_eq(v___x_2840_, v_newlinePositions_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v_newlinePositions_2844_; lean_object* v___x_2845_; lean_object* v_group_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_fst_2851_; lean_object* v_snd_2852_; lean_object* v___x_2853_; 
v___x_2843_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__0));
v_newlinePositions_2844_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg(v_initialWs_2838_, v_newlinePositions_2841_, v___x_2843_);
v___x_2845_ = l_Lean_Fmt_instInhabitedPendingComment_default;
v_group_2846_ = lean_array_get(v___x_2845_, v_comments_2839_, v_newlinePositions_2841_);
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = l_Array_toSubarray___redArg(v_comments_2839_, v___x_2847_, v___x_2840_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2843_);
lean_ctor_set(v___x_2849_, 1, v_group_2846_);
v___x_2850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg(v_newlinePositions_2844_, v___x_2840_, v___x_2848_, v___x_2849_);
lean_dec_ref(v_newlinePositions_2844_);
v_fst_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_fst_2851_);
v_snd_2852_ = lean_ctor_get(v___x_2850_, 1);
lean_inc(v_snd_2852_);
lean_dec_ref(v___x_2850_);
v___x_2853_ = lean_array_push(v_fst_2851_, v_snd_2852_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; 
lean_dec_ref(v_comments_2839_);
v___x_2854_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__1));
return v___x_2854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___boxed(lean_object* v_initialWs_2855_, lean_object* v_comments_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments(v_initialWs_2855_, v_comments_2856_);
lean_dec_ref(v_initialWs_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0(lean_object* v_initialWs_2858_, lean_object* v_inst_2859_, lean_object* v_R_2860_, lean_object* v_a_2861_, lean_object* v_b_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___redArg(v_initialWs_2858_, v_a_2861_, v_b_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0___boxed(lean_object* v_initialWs_2864_, lean_object* v_inst_2865_, lean_object* v_R_2866_, lean_object* v_a_2867_, lean_object* v_b_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__0(v_initialWs_2864_, v_inst_2865_, v_R_2866_, v_a_2867_, v_b_2868_);
lean_dec_ref(v_initialWs_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1(lean_object* v_newlinePositions_2870_, lean_object* v___x_2871_, lean_object* v_inst_2872_, lean_object* v_R_2873_, lean_object* v_a_2874_, lean_object* v_b_2875_, lean_object* v_c_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___redArg(v_newlinePositions_2870_, v___x_2871_, v_a_2874_, v_b_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1___boxed(lean_object* v_newlinePositions_2878_, lean_object* v___x_2879_, lean_object* v_inst_2880_, lean_object* v_R_2881_, lean_object* v_a_2882_, lean_object* v_b_2883_, lean_object* v_c_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments_spec__1(v_newlinePositions_2878_, v___x_2879_, v_inst_2880_, v_R_2881_, v_a_2882_, v_b_2883_, v_c_2884_);
lean_dec(v___x_2879_);
lean_dec_ref(v_newlinePositions_2878_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0(size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_bs_2888_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2889_ == 0)
{
return v_bs_2888_;
}
else
{
lean_object* v_v_2890_; lean_object* v___x_2891_; lean_object* v_bs_x27_2892_; lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v_v_2890_ = lean_array_uget(v_bs_2888_, v_i_2887_);
v___x_2891_ = lean_unsigned_to_nat(0u);
v_bs_x27_2892_ = lean_array_uset(v_bs_2888_, v_i_2887_, v___x_2891_);
v___x_2893_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize(v_v_2890_);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_add(v_i_2887_, v___x_2894_);
v___x_2896_ = lean_array_uset(v_bs_x27_2892_, v_i_2887_, v___x_2893_);
v_i_2887_ = v___x_2895_;
v_bs_2888_ = v___x_2896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0___boxed(lean_object* v_sz_2898_, lean_object* v_i_2899_, lean_object* v_bs_2900_){
_start:
{
size_t v_sz_boxed_2901_; size_t v_i_boxed_2902_; lean_object* v_res_2903_; 
v_sz_boxed_2901_ = lean_unbox_usize(v_sz_2898_);
lean_dec(v_sz_2898_);
v_i_boxed_2902_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0(v_sz_boxed_2901_, v_i_boxed_2902_, v_bs_2900_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg(lean_object* v_initialWs_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_){
_start:
{
lean_object* v_str_2907_; lean_object* v_startInclusive_2908_; lean_object* v_endExclusive_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_str_2907_ = lean_ctor_get(v_initialWs_2904_, 0);
v_startInclusive_2908_ = lean_ctor_get(v_initialWs_2904_, 1);
v_endExclusive_2909_ = lean_ctor_get(v_initialWs_2904_, 2);
v___x_2910_ = lean_nat_sub(v_endExclusive_2909_, v_startInclusive_2908_);
v___x_2911_ = lean_nat_dec_eq(v_a_2905_, v___x_2910_);
lean_dec(v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; uint32_t v___x_2913_; uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2912_ = lean_nat_add(v_startInclusive_2908_, v_a_2905_);
v___x_2913_ = lean_string_utf8_get_fast(v_str_2907_, v___x_2912_);
v___x_2914_ = 10;
v___x_2915_ = lean_uint32_dec_eq(v___x_2913_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_dec(v_a_2905_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_string_utf8_next_fast(v_str_2907_, v___x_2912_);
lean_dec(v___x_2912_);
v___x_2918_ = lean_nat_sub(v___x_2917_, v_startInclusive_2908_);
v_a_2905_ = v___x_2918_;
v_b_2906_ = v___x_2916_;
goto _start;
}
else
{
lean_object* v___x_2920_; 
lean_dec(v___x_2912_);
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2905_);
return v___x_2920_;
}
}
else
{
lean_dec(v_a_2905_);
lean_inc(v_b_2906_);
return v_b_2906_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg___boxed(lean_object* v_initialWs_2921_, lean_object* v_a_2922_, lean_object* v_b_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg(v_initialWs_2921_, v_a_2922_, v_b_2923_);
lean_dec(v_b_2923_);
lean_dec_ref(v_initialWs_2921_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_parseComments(lean_object* v_lineInfos_2925_, lean_object* v_originalTokenRange_2926_, uint8_t v_originalWhitespaceKind_2927_, lean_object* v_initialWs_2928_){
_start:
{
lean_object* v___y_2930_; lean_object* v_searcher_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_searcher_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_box(0);
v___x_2946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg(v_initialWs_2928_, v_searcher_2944_, v___x_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_startInclusive_2947_; lean_object* v_endExclusive_2948_; lean_object* v___x_2949_; 
v_startInclusive_2947_ = lean_ctor_get(v_initialWs_2928_, 1);
v_endExclusive_2948_ = lean_ctor_get(v_initialWs_2928_, 2);
v___x_2949_ = lean_nat_sub(v_endExclusive_2948_, v_startInclusive_2947_);
v___y_2930_ = v___x_2949_;
goto v___jp_2929_;
}
else
{
lean_object* v_val_2950_; 
v_val_2950_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_val_2950_);
lean_dec_ref_known(v___x_2946_, 1);
v___y_2930_ = v_val_2950_;
goto v___jp_2929_;
}
v___jp_2929_:
{
lean_object* v_startInclusive_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v_snd_2938_; lean_object* v_closedComments_2939_; lean_object* v_comments_2940_; size_t v_sz_2941_; size_t v___x_2942_; lean_object* v_finalized_2943_; 
v_startInclusive_2931_ = lean_ctor_get(v_initialWs_2928_, 1);
v___x_2932_ = lean_nat_add(v_startInclusive_2931_, v___y_2930_);
lean_dec(v___y_2930_);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments___closed__1));
v___x_2935_ = lean_box(0);
lean_inc_ref(v_initialWs_2928_);
v___x_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2932_);
lean_ctor_set(v___x_2936_, 1, v_initialWs_2928_);
lean_ctor_set(v___x_2936_, 2, v___x_2934_);
lean_ctor_set(v___x_2936_, 3, v___x_2935_);
lean_ctor_set(v___x_2936_, 4, v___x_2933_);
v___x_2937_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_go(v_lineInfos_2925_, v_originalTokenRange_2926_, v_originalWhitespaceKind_2927_, v___x_2936_);
v_snd_2938_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_snd_2938_);
lean_dec_ref(v___x_2937_);
v_closedComments_2939_ = lean_ctor_get(v_snd_2938_, 2);
lean_inc_ref(v_closedComments_2939_);
lean_dec(v_snd_2938_);
v_comments_2940_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_groupComments(v_initialWs_2928_, v_closedComments_2939_);
lean_dec_ref(v_initialWs_2928_);
v_sz_2941_ = lean_array_size(v_comments_2940_);
v___x_2942_ = ((size_t)0ULL);
v_finalized_2943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_parseComments_spec__0(v_sz_2941_, v___x_2942_, v_comments_2940_);
return v_finalized_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_parseComments___boxed(lean_object* v_lineInfos_2951_, lean_object* v_originalTokenRange_2952_, lean_object* v_originalWhitespaceKind_2953_, lean_object* v_initialWs_2954_){
_start:
{
uint8_t v_originalWhitespaceKind_boxed_2955_; lean_object* v_res_2956_; 
v_originalWhitespaceKind_boxed_2955_ = lean_unbox(v_originalWhitespaceKind_2953_);
v_res_2956_ = l_Lean_Fmt_parseComments(v_lineInfos_2951_, v_originalTokenRange_2952_, v_originalWhitespaceKind_boxed_2955_, v_initialWs_2954_);
lean_dec_ref(v_lineInfos_2951_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1(lean_object* v_initialWs_2957_, lean_object* v_inst_2958_, lean_object* v_R_2959_, lean_object* v_a_2960_, lean_object* v_b_2961_, lean_object* v_c_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___redArg(v_initialWs_2957_, v_a_2960_, v_b_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1___boxed(lean_object* v_initialWs_2964_, lean_object* v_inst_2965_, lean_object* v_R_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v_c_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_parseComments_spec__1(v_initialWs_2964_, v_inst_2965_, v_R_2966_, v_a_2967_, v_b_2968_, v_c_2969_);
lean_dec(v_b_2968_);
lean_dec_ref(v_initialWs_2964_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice(lean_object* v_stx_2973_, lean_object* v_s_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_str_2976_; lean_object* v_startPos_2977_; lean_object* v_stopPos_2978_; uint8_t v___x_2987_; 
v_str_2976_ = lean_ctor_get(v_s_2974_, 0);
lean_inc_ref(v_str_2976_);
v_startPos_2977_ = lean_ctor_get(v_s_2974_, 1);
lean_inc(v_startPos_2977_);
v_stopPos_2978_ = lean_ctor_get(v_s_2974_, 2);
lean_inc(v_stopPos_2978_);
v___x_2987_ = lean_string_is_valid_pos(v_str_2976_, v_startPos_2977_);
if (v___x_2987_ == 0)
{
lean_dec_ref(v_a_2975_);
goto v___jp_2979_;
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_string_is_valid_pos(v_str_2976_, v_stopPos_2978_);
if (v___x_2988_ == 0)
{
lean_dec_ref(v_a_2975_);
goto v___jp_2979_;
}
else
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_nat_dec_le(v_startPos_2977_, v_stopPos_2978_);
if (v___x_2989_ == 0)
{
lean_dec_ref(v_a_2975_);
goto v___jp_2979_;
}
else
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_stx_2973_);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_s_2974_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; lean_object* v_unused_3000_; lean_object* v_unused_3001_; 
v_unused_2999_ = lean_ctor_get(v_s_2974_, 2);
lean_dec(v_unused_2999_);
v_unused_3000_ = lean_ctor_get(v_s_2974_, 1);
lean_dec(v_unused_3000_);
v_unused_3001_ = lean_ctor_get(v_s_2974_, 0);
lean_dec(v_unused_3001_);
v___x_2991_ = v_s_2974_;
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_s_2974_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_str_2976_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_startPos_2977_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_stopPos_2978_);
v___x_2994_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v_a_2975_);
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
}
}
}
v___jp_2979_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_s_2974_);
v___x_2981_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__0));
v___x_2982_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice___closed__1));
v___x_2983_ = lean_string_utf8_extract(v_str_2976_, v_startPos_2977_, v_stopPos_2978_);
lean_dec(v_stopPos_2978_);
lean_dec(v_startPos_2977_);
lean_dec_ref(v_str_2976_);
v___x_2984_ = lean_string_append(v___x_2982_, v___x_2983_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_2985_, 0, v_stx_2973_);
lean_ctor_set(v___x_2985_, 1, v___x_2980_);
lean_ctor_set(v___x_2985_, 2, v___x_2981_);
lean_ctor_set(v___x_2985_, 3, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(lean_object* v_a_3002_, lean_object* v_x_3003_){
_start:
{
if (lean_obj_tag(v_x_3003_) == 0)
{
uint8_t v___x_3004_; 
v___x_3004_ = 0;
return v___x_3004_;
}
else
{
lean_object* v_key_3005_; lean_object* v_tail_3006_; uint8_t v___x_3007_; 
v_key_3005_ = lean_ctor_get(v_x_3003_, 0);
v_tail_3006_ = lean_ctor_get(v_x_3003_, 2);
v___x_3007_ = l_Lean_Syntax_instBEqRange_beq(v_key_3005_, v_a_3002_);
if (v___x_3007_ == 0)
{
v_x_3003_ = v_tail_3006_;
goto _start;
}
else
{
return v___x_3007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg___boxed(lean_object* v_a_3009_, lean_object* v_x_3010_){
_start:
{
uint8_t v_res_3011_; lean_object* v_r_3012_; 
v_res_3011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(v_a_3009_, v_x_3010_);
lean_dec(v_x_3010_);
lean_dec_ref(v_a_3009_);
v_r_3012_ = lean_box(v_res_3011_);
return v_r_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2___lam__0(lean_object* v_a_3013_, lean_object* v_x_3014_){
_start:
{
if (lean_obj_tag(v_x_3014_) == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_mk_empty_array_with_capacity(v___x_3015_);
v___x_3017_ = lean_array_push(v___x_3016_, v_a_3013_);
v___x_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
return v___x_3018_;
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3027_; 
v_val_3019_ = lean_ctor_get(v_x_3014_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_x_3014_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3021_ = v_x_3014_;
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_val_3019_);
lean_dec(v_x_3014_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = lean_array_push(v_val_3019_, v_a_3013_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2(lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_x_3030_){
_start:
{
if (lean_obj_tag(v_x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_val_3033_; lean_object* v___x_3034_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2___lam__0(v_a_3028_, v___x_3031_);
v_val_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_val_3033_);
lean_dec(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3029_);
lean_ctor_set(v___x_3034_, 1, v_val_3033_);
lean_ctor_set(v___x_3034_, 2, v_x_3030_);
return v___x_3034_;
}
else
{
lean_object* v_key_3035_; lean_object* v_value_3036_; lean_object* v_tail_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3052_; 
v_key_3035_ = lean_ctor_get(v_x_3030_, 0);
v_value_3036_ = lean_ctor_get(v_x_3030_, 1);
v_tail_3037_ = lean_ctor_get(v_x_3030_, 2);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_x_3030_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3039_ = v_x_3030_;
v_isShared_3040_ = v_isSharedCheck_3052_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_tail_3037_);
lean_inc(v_value_3036_);
lean_inc(v_key_3035_);
lean_dec(v_x_3030_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3052_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Syntax_instBEqRange_beq(v_key_3035_, v_a_3029_);
if (v___x_3041_ == 0)
{
lean_object* v_tail_3042_; lean_object* v___x_3044_; 
v_tail_3042_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2(v_a_3028_, v_a_3029_, v_tail_3037_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 2, v_tail_3042_);
v___x_3044_ = v___x_3039_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_key_3035_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_value_3036_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_tail_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_val_3048_; lean_object* v___x_3050_; 
lean_dec(v_key_3035_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_value_3036_);
v___x_3047_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2___lam__0(v_a_3028_, v___x_3046_);
v_val_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_val_3048_);
lean_dec(v___x_3047_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 1, v_val_3048_);
lean_ctor_set(v___x_3039_, 0, v_a_3029_);
v___x_3050_ = v___x_3039_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3029_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_val_3048_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_tail_3037_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
if (lean_obj_tag(v_x_3054_) == 0)
{
return v_x_3053_;
}
else
{
lean_object* v_key_3055_; lean_object* v_value_3056_; lean_object* v_tail_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3080_; 
v_key_3055_ = lean_ctor_get(v_x_3054_, 0);
v_value_3056_ = lean_ctor_get(v_x_3054_, 1);
v_tail_3057_ = lean_ctor_get(v_x_3054_, 2);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_x_3054_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3059_ = v_x_3054_;
v_isShared_3060_ = v_isSharedCheck_3080_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_tail_3057_);
lean_inc(v_value_3056_);
lean_inc(v_key_3055_);
lean_dec(v_x_3054_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3080_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; uint64_t v___x_3062_; uint64_t v___x_3063_; uint64_t v___x_3064_; uint64_t v_fold_3065_; uint64_t v___x_3066_; uint64_t v___x_3067_; uint64_t v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; size_t v___x_3071_; size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3061_ = lean_array_get_size(v_x_3053_);
v___x_3062_ = l_Lean_Syntax_instHashableRange_hash(v_key_3055_);
v___x_3063_ = 32ULL;
v___x_3064_ = lean_uint64_shift_right(v___x_3062_, v___x_3063_);
v_fold_3065_ = lean_uint64_xor(v___x_3062_, v___x_3064_);
v___x_3066_ = 16ULL;
v___x_3067_ = lean_uint64_shift_right(v_fold_3065_, v___x_3066_);
v___x_3068_ = lean_uint64_xor(v_fold_3065_, v___x_3067_);
v___x_3069_ = lean_uint64_to_usize(v___x_3068_);
v___x_3070_ = lean_usize_of_nat(v___x_3061_);
v___x_3071_ = ((size_t)1ULL);
v___x_3072_ = lean_usize_sub(v___x_3070_, v___x_3071_);
v___x_3073_ = lean_usize_land(v___x_3069_, v___x_3072_);
v___x_3074_ = lean_array_uget_borrowed(v_x_3053_, v___x_3073_);
lean_inc(v___x_3074_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 2, v___x_3074_);
v___x_3076_ = v___x_3059_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_key_3055_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_value_3056_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_array_uset(v_x_3053_, v___x_3073_, v___x_3076_);
v_x_3053_ = v___x_3077_;
v_x_3054_ = v_tail_3057_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3081_, lean_object* v_source_3082_, lean_object* v_target_3083_){
_start:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_array_get_size(v_source_3082_);
v___x_3085_ = lean_nat_dec_lt(v_i_3081_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_dec_ref(v_source_3082_);
lean_dec(v_i_3081_);
return v_target_3083_;
}
else
{
lean_object* v_es_3086_; lean_object* v___x_3087_; lean_object* v_source_3088_; lean_object* v_target_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_es_3086_ = lean_array_fget(v_source_3082_, v_i_3081_);
v___x_3087_ = lean_box(0);
v_source_3088_ = lean_array_fset(v_source_3082_, v_i_3081_, v___x_3087_);
v_target_3089_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4___redArg(v_target_3083_, v_es_3086_);
v___x_3090_ = lean_unsigned_to_nat(1u);
v___x_3091_ = lean_nat_add(v_i_3081_, v___x_3090_);
lean_dec(v_i_3081_);
v_i_3081_ = v___x_3091_;
v_source_3082_ = v_source_3088_;
v_target_3083_ = v_target_3089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1___redArg(lean_object* v_data_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_nbuckets_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3094_ = lean_array_get_size(v_data_3093_);
v___x_3095_ = lean_unsigned_to_nat(2u);
v_nbuckets_3096_ = lean_nat_mul(v___x_3094_, v___x_3095_);
v___x_3097_ = lean_unsigned_to_nat(0u);
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_mk_array(v_nbuckets_3096_, v___x_3098_);
v___x_3100_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2___redArg(v___x_3097_, v_data_3093_, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0(lean_object* v_a_3101_, lean_object* v_m_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_size_3104_; lean_object* v_buckets_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3155_; 
v_size_3104_ = lean_ctor_get(v_m_3102_, 0);
v_buckets_3105_ = lean_ctor_get(v_m_3102_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_m_3102_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3107_ = v_m_3102_;
v_isShared_3108_ = v_isSharedCheck_3155_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_buckets_3105_);
lean_inc(v_size_3104_);
lean_dec(v_m_3102_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3155_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v_fold_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; lean_object* v_bkt_3122_; uint8_t v___x_3123_; 
v___x_3109_ = lean_array_get_size(v_buckets_3105_);
v___x_3110_ = l_Lean_Syntax_instHashableRange_hash(v_a_3103_);
v___x_3111_ = 32ULL;
v___x_3112_ = lean_uint64_shift_right(v___x_3110_, v___x_3111_);
v_fold_3113_ = lean_uint64_xor(v___x_3110_, v___x_3112_);
v___x_3114_ = 16ULL;
v___x_3115_ = lean_uint64_shift_right(v_fold_3113_, v___x_3114_);
v___x_3116_ = lean_uint64_xor(v_fold_3113_, v___x_3115_);
v___x_3117_ = lean_uint64_to_usize(v___x_3116_);
v___x_3118_ = lean_usize_of_nat(v___x_3109_);
v___x_3119_ = ((size_t)1ULL);
v___x_3120_ = lean_usize_sub(v___x_3118_, v___x_3119_);
v___x_3121_ = lean_usize_land(v___x_3117_, v___x_3120_);
v_bkt_3122_ = lean_array_uget_borrowed(v_buckets_3105_, v___x_3121_);
v___x_3123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(v_a_3103_, v_bkt_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_size_x27_3127_; lean_object* v___x_3128_; lean_object* v_buckets_x27_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_mk_empty_array_with_capacity(v___x_3124_);
v___x_3126_ = lean_array_push(v___x_3125_, v_a_3101_);
v_size_x27_3127_ = lean_nat_add(v_size_3104_, v___x_3124_);
lean_dec(v_size_3104_);
lean_inc(v_bkt_3122_);
v___x_3128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3103_);
lean_ctor_set(v___x_3128_, 1, v___x_3126_);
lean_ctor_set(v___x_3128_, 2, v_bkt_3122_);
v_buckets_x27_3129_ = lean_array_uset(v_buckets_3105_, v___x_3121_, v___x_3128_);
v___x_3130_ = lean_unsigned_to_nat(4u);
v___x_3131_ = lean_nat_mul(v_size_x27_3127_, v___x_3130_);
v___x_3132_ = lean_unsigned_to_nat(3u);
v___x_3133_ = lean_nat_div(v___x_3131_, v___x_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_array_get_size(v_buckets_x27_3129_);
v___x_3135_ = lean_nat_dec_le(v___x_3133_, v___x_3134_);
lean_dec(v___x_3133_);
if (v___x_3135_ == 0)
{
lean_object* v_val_3136_; lean_object* v___x_3138_; 
v_val_3136_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1___redArg(v_buckets_x27_3129_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_val_3136_);
lean_ctor_set(v___x_3107_, 0, v_size_x27_3127_);
v___x_3138_ = v___x_3107_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_size_x27_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_val_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
else
{
lean_object* v___x_3141_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_buckets_x27_3129_);
lean_ctor_set(v___x_3107_, 0, v_size_x27_3127_);
v___x_3141_ = v___x_3107_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_size_x27_3127_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_buckets_x27_3129_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
else
{
lean_object* v___x_3143_; lean_object* v_buckets_x27_3144_; lean_object* v_bkt_x27_3145_; lean_object* v___y_3147_; uint8_t v___x_3152_; 
lean_inc(v_bkt_3122_);
v___x_3143_ = lean_box(0);
v_buckets_x27_3144_ = lean_array_uset(v_buckets_3105_, v___x_3121_, v___x_3143_);
lean_inc_ref(v_a_3103_);
v_bkt_x27_3145_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__2(v_a_3101_, v_a_3103_, v_bkt_3122_);
v___x_3152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(v_a_3103_, v_bkt_x27_3145_);
lean_dec_ref(v_a_3103_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_sub(v_size_3104_, v___x_3153_);
lean_dec(v_size_3104_);
v___y_3147_ = v___x_3154_;
goto v___jp_3146_;
}
else
{
v___y_3147_ = v_size_3104_;
goto v___jp_3146_;
}
v___jp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = lean_array_uset(v_buckets_x27_3144_, v___x_3121_, v_bkt_x27_3145_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___x_3148_);
lean_ctor_set(v___x_3107_, 0, v___y_3147_);
v___x_3150_ = v___x_3107_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___y_3147_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0(lean_object* v_x_3156_){
_start:
{
lean_object* v_startPos_3157_; 
v_startPos_3157_ = lean_ctor_get(v_x_3156_, 4);
lean_inc(v_startPos_3157_);
return v_startPos_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0___boxed(lean_object* v_x_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___lam__0(v_x_3158_);
lean_dec_ref(v_x_3158_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1(lean_object* v_lineInfos_3161_, lean_object* v_range_3162_, lean_object* v_as_3163_, size_t v_sz_3164_, size_t v_i_3165_, lean_object* v_b_3166_, lean_object* v___y_3167_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_usize_dec_lt(v_i_3165_, v_sz_3164_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v_range_3162_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_b_3166_);
lean_ctor_set(v___x_3169_, 1, v___y_3167_);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
return v___x_3170_;
}
else
{
lean_object* v_a_3171_; uint8_t v_kind_3172_; uint8_t v_placement_3173_; lean_object* v_originalWhitespaceRange_3174_; lean_object* v___x_3175_; lean_object* v___y_3177_; lean_object* v___y_3192_; 
v_a_3171_ = lean_array_uget_borrowed(v_as_3163_, v_i_3165_);
v_kind_3172_ = lean_ctor_get_uint8(v_a_3171_, sizeof(void*)*3);
v_placement_3173_ = lean_ctor_get_uint8(v_a_3171_, sizeof(void*)*3 + 1);
v_originalWhitespaceRange_3174_ = lean_ctor_get(v_a_3171_, 1);
v___x_3175_ = lean_box(0);
if (v_kind_3172_ == 0)
{
if (v_placement_3173_ == 0)
{
lean_object* v_start_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; 
v_start_3198_ = lean_ctor_get(v_originalWhitespaceRange_3174_, 0);
v___f_3199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___closed__0));
v___f_3200_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1));
lean_inc(v_start_3198_);
v___x_3201_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_3161_, v_start_3198_, v___f_3199_, v___f_3200_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
v___x_3203_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment_spec__0(v___x_3202_);
v___y_3192_ = v___x_3203_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3204_; 
v_val_3204_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v___x_3201_, 1);
v___y_3192_ = v_val_3204_;
goto v___jp_3191_;
}
}
else
{
lean_inc_ref(v_range_3162_);
v___y_3177_ = v_range_3162_;
goto v___jp_3176_;
}
}
else
{
lean_inc_ref(v_range_3162_);
v___y_3177_ = v_range_3162_;
goto v___jp_3176_;
}
v___jp_3176_:
{
lean_object* v_pendingComments_3178_; lean_object* v_comments_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
v_pendingComments_3178_ = lean_ctor_get(v___y_3167_, 0);
v_comments_3179_ = lean_ctor_get(v___y_3167_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___y_3167_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3181_ = v___y_3167_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_comments_3179_);
lean_inc(v_pendingComments_3178_);
lean_dec(v___y_3167_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
lean_inc(v_a_3171_);
v___x_3183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0(v_a_3171_, v_comments_3179_, v___y_3177_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3183_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_pendingComments_3178_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
size_t v___x_3186_; size_t v___x_3187_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3165_, v___x_3186_);
v_i_3165_ = v___x_3187_;
v_b_3166_ = v___x_3175_;
v___y_3167_ = v___x_3185_;
goto _start;
}
}
}
v___jp_3191_:
{
lean_object* v_snd_3193_; lean_object* v_tokenRanges_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_snd_3193_ = lean_ctor_get(v___y_3192_, 1);
lean_inc(v_snd_3193_);
lean_dec_ref(v___y_3192_);
v_tokenRanges_3194_ = lean_ctor_get(v_snd_3193_, 3);
lean_inc_ref(v_tokenRanges_3194_);
lean_dec(v_snd_3193_);
v___x_3195_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_array_get(v___x_3195_, v_tokenRanges_3194_, v___x_3196_);
lean_dec_ref(v_tokenRanges_3194_);
v___y_3177_ = v___x_3197_;
goto v___jp_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1___boxed(lean_object* v_lineInfos_3205_, lean_object* v_range_3206_, lean_object* v_as_3207_, lean_object* v_sz_3208_, lean_object* v_i_3209_, lean_object* v_b_3210_, lean_object* v___y_3211_){
_start:
{
size_t v_sz_boxed_3212_; size_t v_i_boxed_3213_; lean_object* v_res_3214_; 
v_sz_boxed_3212_ = lean_unbox_usize(v_sz_3208_);
lean_dec(v_sz_3208_);
v_i_boxed_3213_ = lean_unbox_usize(v_i_3209_);
lean_dec(v_i_3209_);
v_res_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1(v_lineInfos_3205_, v_range_3206_, v_as_3207_, v_sz_boxed_3212_, v_i_boxed_3213_, v_b_3210_, v___y_3211_);
lean_dec_ref(v_as_3207_);
lean_dec_ref(v_lineInfos_3205_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments(lean_object* v_lineInfos_3215_, lean_object* v_range_3216_, lean_object* v_newComments_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3219_ = lean_array_get_size(v_newComments_3217_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_nat_dec_eq(v___x_3219_, v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; size_t v_sz_3223_; size_t v___x_3224_; lean_object* v___x_3225_; 
v___x_3222_ = lean_box(0);
v_sz_3223_ = lean_array_size(v_newComments_3217_);
v___x_3224_ = ((size_t)0ULL);
v___x_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__1(v_lineInfos_3215_, v_range_3216_, v_newComments_3217_, v_sz_3223_, v___x_3224_, v___x_3222_, v_a_3218_);
if (lean_obj_tag(v___x_3225_) == 0)
{
return v___x_3225_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3242_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3242_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3242_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_snd_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3240_; 
v_snd_3230_ = lean_ctor_get(v_a_3226_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_a_3226_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v_a_3226_, 0);
lean_dec(v_unused_3241_);
v___x_3232_ = v_a_3226_;
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_snd_3230_);
lean_dec(v_a_3226_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3222_);
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_snd_3230_);
v___x_3235_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3237_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3235_);
v___x_3237_ = v___x_3228_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_dec_ref(v_range_3216_);
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v_a_3218_);
v___x_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments___boxed(lean_object* v_lineInfos_3246_, lean_object* v_range_3247_, lean_object* v_newComments_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments(v_lineInfos_3246_, v_range_3247_, v_newComments_3248_, v_a_3249_);
lean_dec_ref(v_newComments_3248_);
lean_dec_ref(v_lineInfos_3246_);
return v_res_3250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0(lean_object* v_00_u03b2_3251_, lean_object* v_a_3252_, lean_object* v_x_3253_){
_start:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___redArg(v_a_3252_, v_x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3255_, lean_object* v_a_3256_, lean_object* v_x_3257_){
_start:
{
uint8_t v_res_3258_; lean_object* v_r_3259_; 
v_res_3258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__0(v_00_u03b2_3255_, v_a_3256_, v_x_3257_);
lean_dec(v_x_3257_);
lean_dec_ref(v_a_3256_);
v_r_3259_ = lean_box(v_res_3258_);
return v_r_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1(lean_object* v_00_u03b2_3260_, lean_object* v_data_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1___redArg(v_data_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3263_, lean_object* v_i_3264_, lean_object* v_source_3265_, lean_object* v_target_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2___redArg(v_i_3264_, v_source_3265_, v_target_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments_spec__0_spec__1_spec__2_spec__4___redArg(v_x_3269_, v_x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0(lean_object* v_as_3272_, size_t v_sz_3273_, size_t v_i_3274_, lean_object* v_b_3275_){
_start:
{
lean_object* v_a_3277_; uint8_t v___x_3281_; 
v___x_3281_ = lean_usize_dec_lt(v_i_3274_, v_sz_3273_);
if (v___x_3281_ == 0)
{
return v_b_3275_;
}
else
{
lean_object* v_fst_3282_; lean_object* v_snd_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3297_; 
v_fst_3282_ = lean_ctor_get(v_b_3275_, 0);
v_snd_3283_ = lean_ctor_get(v_b_3275_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_b_3275_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3285_ = v_b_3275_;
v_isShared_3286_ = v_isSharedCheck_3297_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_snd_3283_);
lean_inc(v_fst_3282_);
lean_dec(v_b_3275_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3297_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_a_3287_; uint8_t v_placement_3288_; 
v_a_3287_ = lean_array_uget_borrowed(v_as_3272_, v_i_3274_);
v_placement_3288_ = lean_ctor_get_uint8(v_a_3287_, sizeof(void*)*3 + 1);
if (v_placement_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
lean_inc(v_a_3287_);
v___x_3289_ = lean_array_push(v_fst_3282_, v_a_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3289_);
v___x_3291_ = v___x_3285_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_snd_3283_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
v_a_3277_ = v___x_3291_;
goto v___jp_3276_;
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
lean_inc(v_a_3287_);
v___x_3293_ = lean_array_push(v_snd_3283_, v_a_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3293_);
v___x_3295_ = v___x_3285_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_fst_3282_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
v_a_3277_ = v___x_3295_;
goto v___jp_3276_;
}
}
}
}
v___jp_3276_:
{
size_t v___x_3278_; size_t v___x_3279_; 
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_add(v_i_3274_, v___x_3278_);
v_i_3274_ = v___x_3279_;
v_b_3275_ = v_a_3277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0___boxed(lean_object* v_as_3298_, lean_object* v_sz_3299_, lean_object* v_i_3300_, lean_object* v_b_3301_){
_start:
{
size_t v_sz_boxed_3302_; size_t v_i_boxed_3303_; lean_object* v_res_3304_; 
v_sz_boxed_3302_ = lean_unbox_usize(v_sz_3299_);
lean_dec(v_sz_3299_);
v_i_boxed_3303_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0(v_as_3298_, v_sz_boxed_3302_, v_i_boxed_3303_, v_b_3301_);
lean_dec_ref(v_as_3298_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(lean_object* v_lineInfos_3309_, lean_object* v_stx_3310_, lean_object* v_info_3311_, lean_object* v_a_3312_){
_start:
{
uint8_t v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = 0;
v___x_3314_ = l_Lean_SourceInfo_getRange_x3f(v___x_3313_, v_info_3311_);
if (lean_obj_tag(v___x_3314_) == 1)
{
lean_object* v_val_3315_; lean_object* v_pendingComments_3317_; lean_object* v_comments_3318_; lean_object* v___x_3391_; 
v_val_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3391_ = l_Lean_SourceInfo_getLeading_x3f(v_info_3311_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_pendingComments_3392_; lean_object* v_comments_3393_; 
v_pendingComments_3392_ = lean_ctor_get(v_a_3312_, 0);
lean_inc_ref(v_pendingComments_3392_);
v_comments_3393_ = lean_ctor_get(v_a_3312_, 1);
lean_inc_ref(v_comments_3393_);
lean_dec_ref(v_a_3312_);
v_pendingComments_3317_ = v_pendingComments_3392_;
v_comments_3318_ = v_comments_3393_;
goto v___jp_3316_;
}
else
{
lean_object* v_val_3394_; lean_object* v___x_3395_; 
v_val_3394_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc(v_stx_3310_);
v___x_3395_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice(v_stx_3310_, v_val_3394_, v_a_3312_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_val_3315_);
lean_dec(v_stx_3310_);
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v_snd_3405_; lean_object* v_fst_3406_; lean_object* v_pendingComments_3407_; lean_object* v_comments_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_a_3404_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3395_, 1);
v_snd_3405_ = lean_ctor_get(v_a_3404_, 1);
lean_inc(v_snd_3405_);
v_fst_3406_ = lean_ctor_get(v_a_3404_, 0);
lean_inc(v_fst_3406_);
lean_dec(v_a_3404_);
v_pendingComments_3407_ = lean_ctor_get(v_snd_3405_, 0);
lean_inc_ref(v_pendingComments_3407_);
v_comments_3408_ = lean_ctor_get(v_snd_3405_, 1);
lean_inc_ref(v_comments_3408_);
lean_dec(v_snd_3405_);
v___x_3409_ = 0;
lean_inc(v_val_3315_);
v___x_3410_ = l_Lean_Fmt_parseComments(v_lineInfos_3309_, v_val_3315_, v___x_3409_, v_fst_3406_);
v___x_3411_ = l_Array_append___redArg(v_pendingComments_3407_, v___x_3410_);
lean_dec_ref(v___x_3410_);
v_pendingComments_3317_ = v___x_3411_;
v_comments_3318_ = v_comments_3408_;
goto v___jp_3316_;
}
}
v___jp_3316_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0));
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v_comments_3318_);
lean_inc(v_val_3315_);
v___x_3321_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments(v_lineInfos_3309_, v_val_3315_, v_pendingComments_3317_, v___x_3320_);
lean_dec_ref(v_pendingComments_3317_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_dec(v_val_3315_);
lean_dec(v_stx_3310_);
return v___x_3321_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3390_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3390_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3390_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_snd_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3388_; 
v_snd_3326_ = lean_ctor_get(v_a_3322_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_a_3322_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_a_3322_, 0);
lean_dec(v_unused_3389_);
v___x_3328_ = v_a_3322_;
v_isShared_3329_ = v_isSharedCheck_3388_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_snd_3326_);
lean_dec(v_a_3322_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3388_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_3311_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_dec(v_val_3315_);
lean_dec(v_stx_3310_);
v___x_3331_ = lean_box(0);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3331_);
v___x_3333_ = v___x_3328_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_snd_3326_);
v___x_3333_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3335_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3333_);
v___x_3335_ = v___x_3324_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_val_3338_; lean_object* v___x_3339_; 
lean_del_object(v___x_3328_);
lean_del_object(v___x_3324_);
v_val_3338_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3338_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3339_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice(v_stx_3310_, v_val_3338_, v_snd_3326_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_val_3315_);
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; size_t v_sz_3354_; size_t v___x_3355_; lean_object* v___x_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3359_; 
v_a_3348_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3339_, 1);
v_fst_3349_ = lean_ctor_get(v_a_3348_, 0);
lean_inc(v_fst_3349_);
v_snd_3350_ = lean_ctor_get(v_a_3348_, 1);
lean_inc(v_snd_3350_);
lean_dec(v_a_3348_);
v___x_3351_ = 1;
lean_inc(v_val_3315_);
v___x_3352_ = l_Lean_Fmt_parseComments(v_lineInfos_3309_, v_val_3315_, v___x_3351_, v_fst_3349_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__1));
v_sz_3354_ = lean_array_size(v___x_3352_);
v___x_3355_ = ((size_t)0ULL);
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments_spec__0(v___x_3352_, v_sz_3354_, v___x_3355_, v___x_3353_);
lean_dec_ref(v___x_3352_);
v_fst_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_fst_3357_);
v_snd_3358_ = lean_ctor_get(v___x_3356_, 1);
lean_inc(v_snd_3358_);
lean_dec_ref(v___x_3356_);
v___x_3359_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_addComments(v_lineInfos_3309_, v_val_3315_, v_fst_3357_, v_snd_3350_);
lean_dec(v_fst_3357_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_dec(v_snd_3358_);
return v___x_3359_;
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3387_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3387_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3387_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_snd_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3385_; 
v_snd_3364_ = lean_ctor_get(v_a_3360_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_a_3360_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v_a_3360_, 0);
lean_dec(v_unused_3386_);
v___x_3366_ = v_a_3360_;
v_isShared_3367_ = v_isSharedCheck_3385_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_snd_3364_);
lean_dec(v_a_3360_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3385_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_pendingComments_3368_; lean_object* v_comments_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3384_; 
v_pendingComments_3368_ = lean_ctor_get(v_snd_3364_, 0);
v_comments_3369_ = lean_ctor_get(v_snd_3364_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_snd_3364_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3371_ = v_snd_3364_;
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_comments_3369_);
lean_inc(v_pendingComments_3368_);
lean_dec(v_snd_3364_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3373_ = lean_box(0);
v___x_3374_ = l_Array_append___redArg(v_pendingComments_3368_, v_snd_3358_);
lean_dec(v_snd_3358_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3374_);
v___x_3376_ = v___x_3371_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_comments_3369_);
v___x_3376_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3376_);
lean_ctor_set(v___x_3366_, 0, v___x_3373_);
v___x_3378_ = v___x_3366_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3378_);
v___x_3380_ = v___x_3362_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
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
}
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v___x_3314_);
lean_dec(v_stx_3310_);
v___x_3412_ = lean_box(0);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_a_3312_);
v___x_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___boxed(lean_object* v_lineInfos_3415_, lean_object* v_stx_3416_, lean_object* v_info_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(v_lineInfos_3415_, v_stx_3416_, v_info_3417_, v_a_3418_);
lean_dec(v_info_3417_);
lean_dec_ref(v_lineInfos_3415_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments(lean_object* v_lineInfos_3420_, lean_object* v_stx_3421_, lean_object* v_info_3422_, lean_object* v___tk_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(v_lineInfos_3420_, v_stx_3421_, v_info_3422_, v_a_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___boxed(lean_object* v_lineInfos_3426_, lean_object* v_stx_3427_, lean_object* v_info_3428_, lean_object* v___tk_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments(v_lineInfos_3426_, v_stx_3427_, v_info_3428_, v___tk_3429_, v_a_3430_);
lean_dec_ref(v___tk_3429_);
lean_dec(v_info_3428_);
lean_dec_ref(v_lineInfos_3426_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go(lean_object* v_lineInfos_3435_, lean_object* v_stx_3436_, lean_object* v_stx_3437_, lean_object* v_a_3438_){
_start:
{
switch(lean_obj_tag(v_stx_3437_))
{
case 0:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v_stx_3436_);
v___x_3439_ = lean_box(0);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v_a_3438_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
case 1:
{
lean_object* v_kind_3442_; lean_object* v_args_3443_; lean_object* v___y_3445_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_kind_3442_ = lean_ctor_get(v_stx_3437_, 1);
lean_inc(v_kind_3442_);
v_args_3443_ = lean_ctor_get(v_stx_3437_, 2);
lean_inc_ref(v_args_3443_);
lean_dec_ref_known(v_stx_3437_, 3);
v___x_3467_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___closed__1));
v___x_3468_ = lean_name_eq(v_kind_3442_, v___x_3467_);
lean_dec(v_kind_3442_);
if (v___x_3468_ == 0)
{
v___y_3445_ = v_a_3438_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_array_get_size(v_args_3443_);
v___x_3471_ = lean_nat_dec_lt(v___x_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
v___y_3445_ = v_a_3438_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_array_fget(v_args_3443_, v___x_3469_);
lean_dec_ref(v_args_3443_);
v_stx_3437_ = v___x_3472_;
goto _start;
}
}
v___jp_3444_:
{
lean_object* v___x_3446_; size_t v_sz_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3446_ = lean_box(0);
v_sz_3447_ = lean_array_size(v_args_3443_);
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0(v_lineInfos_3435_, v_stx_3436_, v_args_3443_, v_sz_3447_, v___x_3448_, v___x_3446_, v___y_3445_);
lean_dec_ref(v_args_3443_);
if (lean_obj_tag(v___x_3449_) == 0)
{
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3466_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3466_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3466_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_snd_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3464_; 
v_snd_3454_ = lean_ctor_get(v_a_3450_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3450_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v_a_3450_, 0);
lean_dec(v_unused_3465_);
v___x_3456_ = v_a_3450_;
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_snd_3454_);
lean_dec(v_a_3450_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3446_);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_snd_3454_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3459_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_info_3474_; lean_object* v___x_3475_; 
v_info_3474_ = lean_ctor_get(v_stx_3437_, 0);
lean_inc(v_info_3474_);
lean_dec_ref_known(v_stx_3437_, 2);
v___x_3475_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(v_lineInfos_3435_, v_stx_3436_, v_info_3474_, v_a_3438_);
lean_dec(v_info_3474_);
return v___x_3475_;
}
default: 
{
lean_object* v_info_3476_; lean_object* v_rawVal_3477_; lean_object* v___x_3478_; 
v_info_3476_ = lean_ctor_get(v_stx_3437_, 0);
lean_inc(v_info_3476_);
v_rawVal_3477_ = lean_ctor_get(v_stx_3437_, 1);
lean_inc_ref(v_rawVal_3477_);
lean_dec_ref_known(v_stx_3437_, 4);
lean_inc(v_stx_3436_);
v___x_3478_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_toSlice(v_stx_3436_, v_rawVal_3477_, v_a_3438_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v_info_3476_);
lean_dec(v_stx_3436_);
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v_snd_3488_; lean_object* v___x_3489_; 
v_a_3487_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3478_, 1);
v_snd_3488_ = lean_ctor_get(v_a_3487_, 1);
lean_inc(v_snd_3488_);
lean_dec(v_a_3487_);
v___x_3489_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg(v_lineInfos_3435_, v_stx_3436_, v_info_3476_, v_snd_3488_);
lean_dec(v_info_3476_);
return v___x_3489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0(lean_object* v_lineInfos_3490_, lean_object* v_stx_3491_, lean_object* v_as_3492_, size_t v_sz_3493_, size_t v_i_3494_, lean_object* v_b_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_usize_dec_lt(v_i_3494_, v_sz_3493_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_stx_3491_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_b_3495_);
lean_ctor_set(v___x_3498_, 1, v___y_3496_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_array_uget_borrowed(v_as_3492_, v_i_3494_);
lean_inc(v_a_3500_);
lean_inc(v_stx_3491_);
v___x_3501_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go(v_lineInfos_3490_, v_stx_3491_, v_a_3500_, v___y_3496_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec(v_stx_3491_);
return v___x_3501_;
}
else
{
lean_object* v_a_3502_; lean_object* v_snd_3503_; lean_object* v___x_3504_; size_t v___x_3505_; size_t v___x_3506_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_snd_3503_ = lean_ctor_get(v_a_3502_, 1);
lean_inc(v_snd_3503_);
lean_dec(v_a_3502_);
v___x_3504_ = lean_box(0);
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_add(v_i_3494_, v___x_3505_);
v_i_3494_ = v___x_3506_;
v_b_3495_ = v___x_3504_;
v___y_3496_ = v_snd_3503_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0___boxed(lean_object* v_lineInfos_3508_, lean_object* v_stx_3509_, lean_object* v_as_3510_, lean_object* v_sz_3511_, lean_object* v_i_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_){
_start:
{
size_t v_sz_boxed_3515_; size_t v_i_boxed_3516_; lean_object* v_res_3517_; 
v_sz_boxed_3515_ = lean_unbox_usize(v_sz_3511_);
lean_dec(v_sz_3511_);
v_i_boxed_3516_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go_spec__0(v_lineInfos_3508_, v_stx_3509_, v_as_3510_, v_sz_boxed_3515_, v_i_boxed_3516_, v_b_3513_, v___y_3514_);
lean_dec_ref(v_as_3510_);
lean_dec_ref(v_lineInfos_3508_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go___boxed(lean_object* v_lineInfos_3518_, lean_object* v_stx_3519_, lean_object* v_stx_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go(v_lineInfos_3518_, v_stx_3519_, v_stx_3520_, v_a_3521_);
lean_dec_ref(v_lineInfos_3518_);
return v_res_3522_;
}
}
static lean_object* _init_l_Lean_Fmt_collectComments___closed__0(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_box(0);
v___x_3524_ = lean_unsigned_to_nat(16u);
v___x_3525_ = lean_mk_array(v___x_3524_, v___x_3523_);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_Fmt_collectComments___closed__1(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_obj_once(&l_Lean_Fmt_collectComments___closed__0, &l_Lean_Fmt_collectComments___closed__0_once, _init_l_Lean_Fmt_collectComments___closed__0);
v___x_3527_ = lean_unsigned_to_nat(0u);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
lean_ctor_set(v___x_3528_, 1, v___x_3526_);
return v___x_3528_;
}
}
static lean_object* _init_l_Lean_Fmt_collectComments___closed__2(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_obj_once(&l_Lean_Fmt_collectComments___closed__1, &l_Lean_Fmt_collectComments___closed__1_once, _init_l_Lean_Fmt_collectComments___closed__1);
v___x_3530_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__0));
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectComments(lean_object* v_lineInfos_3532_, lean_object* v_stx_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_obj_once(&l_Lean_Fmt_collectComments___closed__2, &l_Lean_Fmt_collectComments___closed__2_once, _init_l_Lean_Fmt_collectComments___closed__2);
lean_inc(v_stx_3533_);
v___x_3535_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_go(v_lineInfos_3532_, v_stx_3533_, v_stx_3533_, v___x_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3553_; 
v_a_3544_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3546_ = v___x_3535_;
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3535_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v_snd_3548_; lean_object* v_comments_3549_; lean_object* v___x_3551_; 
v_snd_3548_ = lean_ctor_get(v_a_3544_, 1);
lean_inc(v_snd_3548_);
lean_dec(v_a_3544_);
v_comments_3549_ = lean_ctor_get(v_snd_3548_, 1);
lean_inc_ref(v_comments_3549_);
lean_dec(v_snd_3548_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v_comments_3549_);
v___x_3551_ = v___x_3546_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_comments_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_collectComments___boxed(lean_object* v_lineInfos_3554_, lean_object* v_stx_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Fmt_collectComments(v_lineInfos_3554_, v_stx_3555_);
lean_dec_ref(v_lineInfos_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(lean_object* v___x_3557_, lean_object* v___x_3558_, lean_object* v___x_3559_, lean_object* v_a_3560_, lean_object* v_b_3561_){
_start:
{
lean_object* v_startInclusive_3562_; lean_object* v_endExclusive_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_startInclusive_3562_ = lean_ctor_get(v___x_3557_, 1);
v_endExclusive_3563_ = lean_ctor_get(v___x_3557_, 2);
v___x_3564_ = lean_nat_sub(v_endExclusive_3563_, v_startInclusive_3562_);
v___x_3565_ = lean_nat_dec_eq(v_a_3560_, v___x_3564_);
lean_dec(v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3566_ = lean_nat_add(v___x_3558_, v_a_3560_);
lean_dec(v_a_3560_);
v___x_3567_ = lean_string_utf8_next_fast(v___x_3559_, v___x_3566_);
lean_dec(v___x_3566_);
v___x_3568_ = lean_nat_sub(v___x_3567_, v___x_3558_);
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_nat_add(v_b_3561_, v___x_3569_);
lean_dec(v_b_3561_);
v_a_3560_ = v___x_3568_;
v_b_3561_ = v___x_3570_;
goto _start;
}
else
{
lean_dec(v_a_3560_);
return v_b_3561_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg___boxed(lean_object* v___x_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v_a_3575_, lean_object* v_b_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(v___x_3572_, v___x_3573_, v___x_3574_, v_a_3575_, v_b_3576_);
lean_dec_ref(v___x_3574_);
lean_dec(v___x_3573_);
lean_dec_ref(v___x_3572_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__2(lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
if (lean_obj_tag(v_x_3579_) == 0)
{
return v_x_3578_;
}
else
{
lean_object* v_key_3580_; lean_object* v_tail_3581_; lean_object* v___x_3582_; 
v_key_3580_ = lean_ctor_get(v_x_3579_, 0);
lean_inc(v_key_3580_);
v_tail_3581_ = lean_ctor_get(v_x_3579_, 2);
lean_inc(v_tail_3581_);
lean_dec_ref_known(v_x_3579_, 3);
v___x_3582_ = lean_array_push(v_x_3578_, v_key_3580_);
v_x_3578_ = v___x_3582_;
v_x_3579_ = v_tail_3581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3(lean_object* v_as_3584_, size_t v_i_3585_, size_t v_stop_3586_, lean_object* v_b_3587_){
_start:
{
uint8_t v___x_3588_; 
v___x_3588_ = lean_usize_dec_eq(v_i_3585_, v_stop_3586_);
if (v___x_3588_ == 0)
{
lean_object* v___x_3589_; lean_object* v___x_3590_; size_t v___x_3591_; size_t v___x_3592_; 
v___x_3589_ = lean_array_uget_borrowed(v_as_3584_, v_i_3585_);
lean_inc(v___x_3589_);
v___x_3590_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__2(v_b_3587_, v___x_3589_);
v___x_3591_ = ((size_t)1ULL);
v___x_3592_ = lean_usize_add(v_i_3585_, v___x_3591_);
v_i_3585_ = v___x_3592_;
v_b_3587_ = v___x_3590_;
goto _start;
}
else
{
return v_b_3587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3___boxed(lean_object* v_as_3594_, lean_object* v_i_3595_, lean_object* v_stop_3596_, lean_object* v_b_3597_){
_start:
{
size_t v_i_boxed_3598_; size_t v_stop_boxed_3599_; lean_object* v_res_3600_; 
v_i_boxed_3598_ = lean_unbox_usize(v_i_3595_);
lean_dec(v_i_3595_);
v_stop_boxed_3599_ = lean_unbox_usize(v_stop_3596_);
lean_dec(v_stop_3596_);
v_res_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3(v_as_3594_, v_i_boxed_3598_, v_stop_boxed_3599_, v_b_3597_);
lean_dec_ref(v_as_3594_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg(lean_object* v_rendering_3601_, lean_object* v_a_3602_, lean_object* v_b_3603_){
_start:
{
lean_object* v_array_3604_; lean_object* v_start_3605_; lean_object* v_stop_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3647_; 
v_array_3604_ = lean_ctor_get(v_a_3602_, 0);
v_start_3605_ = lean_ctor_get(v_a_3602_, 1);
v_stop_3606_ = lean_ctor_get(v_a_3602_, 2);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3608_ = v_a_3602_;
v_isShared_3609_ = v_isSharedCheck_3647_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_stop_3606_);
lean_inc(v_start_3605_);
lean_inc(v_array_3604_);
lean_dec(v_a_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3647_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_nat_dec_lt(v_start_3605_, v_stop_3606_);
if (v___x_3610_ == 0)
{
lean_del_object(v___x_3608_);
lean_dec(v_stop_3606_);
lean_dec(v_start_3605_);
lean_dec_ref(v_array_3604_);
return v_b_3603_;
}
else
{
lean_object* v_fst_3611_; lean_object* v_snd_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3646_; 
v_fst_3611_ = lean_ctor_get(v_b_3603_, 0);
v_snd_3612_ = lean_ctor_get(v_b_3603_, 1);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_b_3603_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3614_ = v_b_3603_;
v_isShared_3615_ = v_isSharedCheck_3646_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_snd_3612_);
lean_inc(v_fst_3611_);
lean_dec(v_b_3603_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3646_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; lean_object* v_startInclusive_3617_; lean_object* v_endExclusive_3618_; lean_object* v_str_3619_; lean_object* v_startInclusive_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3616_ = lean_array_fget(v_array_3604_, v_start_3605_);
v_startInclusive_3617_ = lean_ctor_get(v___x_3616_, 0);
v_endExclusive_3618_ = lean_ctor_get(v___x_3616_, 1);
v_str_3619_ = lean_ctor_get(v_rendering_3601_, 0);
v_startInclusive_3620_ = lean_ctor_get(v_rendering_3601_, 1);
v___x_3621_ = lean_unsigned_to_nat(1u);
v___x_3622_ = lean_nat_add(v_start_3605_, v___x_3621_);
lean_dec(v_start_3605_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v___x_3622_);
v___x_3624_ = v___x_3608_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_array_3604_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_stop_3606_);
v___x_3624_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___y_3632_; uint8_t v___x_3641_; 
v___x_3625_ = lean_nat_add(v_startInclusive_3620_, v_startInclusive_3617_);
v___x_3626_ = lean_nat_add(v_startInclusive_3620_, v_endExclusive_3618_);
lean_inc(v___x_3625_);
lean_inc_ref(v_str_3619_);
v___x_3627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3627_, 0, v_str_3619_);
lean_ctor_set(v___x_3627_, 1, v___x_3625_);
lean_ctor_set(v___x_3627_, 2, v___x_3626_);
v___x_3628_ = l_String_Slice_positions(v___x_3627_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(v___x_3627_, v___x_3625_, v_str_3619_, v___x_3628_, v___x_3629_);
lean_dec(v___x_3625_);
lean_dec_ref_known(v___x_3627_, 3);
v___x_3641_ = lean_nat_dec_lt(v___x_3630_, v_snd_3612_);
if (v___x_3641_ == 0)
{
uint8_t v___x_3642_; 
v___x_3642_ = lean_nat_dec_eq(v___x_3630_, v_snd_3612_);
if (v___x_3642_ == 0)
{
v___y_3632_ = v___x_3642_;
goto v___jp_3631_;
}
else
{
lean_object* v_startInclusive_3643_; uint8_t v___x_3644_; 
v_startInclusive_3643_ = lean_ctor_get(v_fst_3611_, 0);
v___x_3644_ = lean_nat_dec_lt(v_startInclusive_3617_, v_startInclusive_3643_);
v___y_3632_ = v___x_3644_;
goto v___jp_3631_;
}
}
else
{
v___y_3632_ = v___x_3641_;
goto v___jp_3631_;
}
v___jp_3631_:
{
if (v___y_3632_ == 0)
{
lean_object* v___x_3634_; 
lean_dec(v___x_3630_);
lean_dec(v___x_3616_);
if (v_isShared_3615_ == 0)
{
v___x_3634_ = v___x_3614_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_fst_3611_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_snd_3612_);
v___x_3634_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
v_a_3602_ = v___x_3624_;
v_b_3603_ = v___x_3634_;
goto _start;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec(v_snd_3612_);
lean_dec(v_fst_3611_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 1, v___x_3630_);
lean_ctor_set(v___x_3614_, 0, v___x_3616_);
v___x_3638_ = v___x_3614_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v___x_3630_);
v___x_3638_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
v_a_3602_ = v___x_3624_;
v_b_3603_ = v___x_3638_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg___boxed(lean_object* v_rendering_3648_, lean_object* v_a_3649_, lean_object* v_b_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg(v_rendering_3648_, v_a_3649_, v_b_3650_);
lean_dec_ref(v_rendering_3648_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(lean_object* v_rendering_3652_, lean_object* v_ranges_3653_){
_start:
{
lean_object* v___y_3655_; lean_object* v_size_3674_; lean_object* v_buckets_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v_size_3674_ = lean_ctor_get(v_ranges_3653_, 0);
v_buckets_3675_ = lean_ctor_get(v_ranges_3653_, 1);
v___x_3676_ = lean_mk_empty_array_with_capacity(v_size_3674_);
v___x_3677_ = lean_unsigned_to_nat(0u);
v___x_3678_ = lean_array_get_size(v_buckets_3675_);
v___x_3679_ = lean_nat_dec_lt(v___x_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
v___y_3655_ = v___x_3676_;
goto v___jp_3654_;
}
else
{
uint8_t v___x_3680_; 
v___x_3680_ = lean_nat_dec_le(v___x_3678_, v___x_3678_);
if (v___x_3680_ == 0)
{
if (v___x_3679_ == 0)
{
v___y_3655_ = v___x_3676_;
goto v___jp_3654_;
}
else
{
size_t v___x_3681_; size_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3681_ = ((size_t)0ULL);
v___x_3682_ = lean_usize_of_nat(v___x_3678_);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3(v_buckets_3675_, v___x_3681_, v___x_3682_, v___x_3676_);
v___y_3655_ = v___x_3683_;
goto v___jp_3654_;
}
}
else
{
size_t v___x_3684_; size_t v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = ((size_t)0ULL);
v___x_3685_ = lean_usize_of_nat(v___x_3678_);
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__3(v_buckets_3675_, v___x_3684_, v___x_3685_, v___x_3676_);
v___y_3655_ = v___x_3686_;
goto v___jp_3654_;
}
}
v___jp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_bestRange_3658_; lean_object* v_startInclusive_3659_; lean_object* v_endExclusive_3660_; lean_object* v_str_3661_; lean_object* v_startInclusive_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v_bestLength_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_fst_3673_; 
v___x_3656_ = l_String_Slice_instInhabitedSubslice(v_rendering_3652_);
v___x_3657_ = lean_unsigned_to_nat(0u);
v_bestRange_3658_ = lean_array_get(v___x_3656_, v___y_3655_, v___x_3657_);
lean_dec_ref(v___x_3656_);
v_startInclusive_3659_ = lean_ctor_get(v_bestRange_3658_, 0);
v_endExclusive_3660_ = lean_ctor_get(v_bestRange_3658_, 1);
v_str_3661_ = lean_ctor_get(v_rendering_3652_, 0);
v_startInclusive_3662_ = lean_ctor_get(v_rendering_3652_, 1);
v___x_3663_ = lean_nat_add(v_startInclusive_3662_, v_startInclusive_3659_);
v___x_3664_ = lean_nat_add(v_startInclusive_3662_, v_endExclusive_3660_);
lean_inc(v___x_3663_);
lean_inc_ref(v_str_3661_);
v___x_3665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3665_, 0, v_str_3661_);
lean_ctor_set(v___x_3665_, 1, v___x_3663_);
lean_ctor_set(v___x_3665_, 2, v___x_3664_);
v___x_3666_ = l_String_Slice_positions(v___x_3665_);
v_bestLength_3667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(v___x_3665_, v___x_3663_, v_str_3661_, v___x_3666_, v___x_3657_);
lean_dec(v___x_3663_);
lean_dec_ref_known(v___x_3665_, 3);
v___x_3668_ = lean_unsigned_to_nat(1u);
v___x_3669_ = lean_array_get_size(v___y_3655_);
v___x_3670_ = l_Array_toSubarray___redArg(v___y_3655_, v___x_3668_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_bestRange_3658_);
lean_ctor_set(v___x_3671_, 1, v_bestLength_3667_);
v___x_3672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg(v_rendering_3652_, v___x_3670_, v___x_3671_);
v_fst_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_fst_3673_);
lean_dec_ref(v___x_3672_);
return v_fst_3673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange___boxed(lean_object* v_rendering_3687_, lean_object* v_ranges_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(v_rendering_3687_, v_ranges_3688_);
lean_dec_ref(v_ranges_3688_);
lean_dec_ref(v_rendering_3687_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0(lean_object* v___x_3690_, lean_object* v___x_3691_, lean_object* v___x_3692_, lean_object* v_inst_3693_, lean_object* v_R_3694_, lean_object* v_a_3695_, lean_object* v_b_3696_, lean_object* v_c_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___redArg(v___x_3690_, v___x_3691_, v___x_3692_, v_a_3695_, v_b_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0___boxed(lean_object* v___x_3699_, lean_object* v___x_3700_, lean_object* v___x_3701_, lean_object* v_inst_3702_, lean_object* v_R_3703_, lean_object* v_a_3704_, lean_object* v_b_3705_, lean_object* v_c_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__0(v___x_3699_, v___x_3700_, v___x_3701_, v_inst_3702_, v_R_3703_, v_a_3704_, v_b_3705_, v_c_3706_);
lean_dec_ref(v___x_3701_);
lean_dec(v___x_3700_);
lean_dec_ref(v___x_3699_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1(lean_object* v_rendering_3708_, lean_object* v_inst_3709_, lean_object* v_R_3710_, lean_object* v_a_3711_, lean_object* v_b_3712_, lean_object* v_c_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___redArg(v_rendering_3708_, v_a_3711_, v_b_3712_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1___boxed(lean_object* v_rendering_3715_, lean_object* v_inst_3716_, lean_object* v_R_3717_, lean_object* v_a_3718_, lean_object* v_b_3719_, lean_object* v_c_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange_spec__1(v_rendering_3715_, v_inst_3716_, v_R_3717_, v_a_3718_, v_b_3719_, v_c_3720_);
lean_dec_ref(v_rendering_3715_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__2(lean_object* v_rendering_3722_, lean_object* v_msg_3723_){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
v___x_3725_ = l_Lean_Syntax_instInhabitedRange_default;
lean_inc_ref(v_rendering_3722_);
v___x_3726_ = lean_alloc_closure((void*)(l_instBEqSubslice__lean_beq___boxed), 3, 1);
lean_closure_set(v___x_3726_, 0, v_rendering_3722_);
v___x_3727_ = lean_alloc_closure((void*)(l_instHashableSubslice__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_3727_, 0, v_rendering_3722_);
v___x_3728_ = l_Std_HashSet_instInhabited(lean_box(0), v___x_3726_, v___x_3727_);
lean_dec_ref(v___x_3727_);
lean_dec_ref(v___x_3726_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3725_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3724_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_panic_fn_borrowed(v___x_3730_, v_msg_3723_);
lean_dec_ref_known(v___x_3730_, 2);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0(lean_object* v_x_3732_){
_start:
{
lean_object* v_fst_3733_; lean_object* v_start_3734_; 
v_fst_3733_ = lean_ctor_get(v_x_3732_, 0);
v_start_3734_ = lean_ctor_get(v_fst_3733_, 0);
lean_inc(v_start_3734_);
return v_start_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0___boxed(lean_object* v_x_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__0(v_x_3735_);
lean_dec_ref(v_x_3735_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1(lean_object* v_x_3737_){
_start:
{
lean_object* v_fst_3738_; lean_object* v_stop_3739_; 
v_fst_3738_ = lean_ctor_get(v_x_3737_, 0);
v_stop_3739_ = lean_ctor_get(v_fst_3738_, 1);
lean_inc(v_stop_3739_);
return v_stop_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1___boxed(lean_object* v_x_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___lam__1(v_x_3740_);
lean_dec_ref(v_x_3740_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1(lean_object* v_as_3742_, size_t v_sz_3743_, size_t v_i_3744_, lean_object* v_b_3745_){
_start:
{
lean_object* v_a_3747_; uint8_t v___x_3751_; 
v___x_3751_ = lean_usize_dec_lt(v_i_3744_, v_sz_3743_);
if (v___x_3751_ == 0)
{
return v_b_3745_;
}
else
{
lean_object* v_fst_3752_; lean_object* v_snd_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3767_; 
v_fst_3752_ = lean_ctor_get(v_b_3745_, 0);
v_snd_3753_ = lean_ctor_get(v_b_3745_, 1);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_b_3745_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3755_ = v_b_3745_;
v_isShared_3756_ = v_isSharedCheck_3767_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_snd_3753_);
lean_inc(v_fst_3752_);
lean_dec(v_b_3745_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3767_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_a_3757_; uint8_t v_kind_3763_; 
v_a_3757_ = lean_array_uget_borrowed(v_as_3742_, v_i_3744_);
v_kind_3763_ = lean_ctor_get_uint8(v_a_3757_, sizeof(void*)*3);
if (v_kind_3763_ == 1)
{
uint8_t v_placement_3764_; 
v_placement_3764_ = lean_ctor_get_uint8(v_a_3757_, sizeof(void*)*3 + 1);
if (v_placement_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_del_object(v___x_3755_);
lean_inc(v_a_3757_);
v___x_3765_ = lean_array_push(v_fst_3752_, v_a_3757_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_snd_3753_);
v_a_3747_ = v___x_3766_;
goto v___jp_3746_;
}
else
{
goto v___jp_3758_;
}
}
else
{
goto v___jp_3758_;
}
v___jp_3758_:
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_inc(v_a_3757_);
v___x_3759_ = lean_array_push(v_snd_3753_, v_a_3757_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v___x_3759_);
v___x_3761_ = v___x_3755_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_fst_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
v_a_3747_ = v___x_3761_;
goto v___jp_3746_;
}
}
}
}
v___jp_3746_:
{
size_t v___x_3748_; size_t v___x_3749_; 
v___x_3748_ = ((size_t)1ULL);
v___x_3749_ = lean_usize_add(v_i_3744_, v___x_3748_);
v_i_3744_ = v___x_3749_;
v_b_3745_ = v_a_3747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1___boxed(lean_object* v_as_3768_, lean_object* v_sz_3769_, lean_object* v_i_3770_, lean_object* v_b_3771_){
_start:
{
size_t v_sz_boxed_3772_; size_t v_i_boxed_3773_; lean_object* v_res_3774_; 
v_sz_boxed_3772_ = lean_unbox_usize(v_sz_3769_);
lean_dec(v_sz_3769_);
v_i_boxed_3773_ = lean_unbox_usize(v_i_3770_);
lean_dec(v_i_3770_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1(v_as_3768_, v_sz_boxed_3772_, v_i_boxed_3773_, v_b_3771_);
lean_dec_ref(v_as_3768_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg(lean_object* v_a_3775_, lean_object* v_x_3776_){
_start:
{
if (lean_obj_tag(v_x_3776_) == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_box(0);
return v___x_3777_;
}
else
{
lean_object* v_key_3778_; lean_object* v_value_3779_; lean_object* v_tail_3780_; uint8_t v___x_3781_; 
v_key_3778_ = lean_ctor_get(v_x_3776_, 0);
v_value_3779_ = lean_ctor_get(v_x_3776_, 1);
v_tail_3780_ = lean_ctor_get(v_x_3776_, 2);
v___x_3781_ = l_Lean_Syntax_instBEqRange_beq(v_key_3778_, v_a_3775_);
if (v___x_3781_ == 0)
{
v_x_3776_ = v_tail_3780_;
goto _start;
}
else
{
lean_object* v___x_3783_; 
lean_inc(v_value_3779_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_value_3779_);
return v___x_3783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg___boxed(lean_object* v_a_3784_, lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg(v_a_3784_, v_x_3785_);
lean_dec(v_x_3785_);
lean_dec_ref(v_a_3784_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg(lean_object* v_m_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v_buckets_3789_; lean_object* v___x_3790_; uint64_t v___x_3791_; uint64_t v___x_3792_; uint64_t v___x_3793_; uint64_t v_fold_3794_; uint64_t v___x_3795_; uint64_t v___x_3796_; uint64_t v___x_3797_; size_t v___x_3798_; size_t v___x_3799_; size_t v___x_3800_; size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_buckets_3789_ = lean_ctor_get(v_m_3787_, 1);
v___x_3790_ = lean_array_get_size(v_buckets_3789_);
v___x_3791_ = l_Lean_Syntax_instHashableRange_hash(v_a_3788_);
v___x_3792_ = 32ULL;
v___x_3793_ = lean_uint64_shift_right(v___x_3791_, v___x_3792_);
v_fold_3794_ = lean_uint64_xor(v___x_3791_, v___x_3793_);
v___x_3795_ = 16ULL;
v___x_3796_ = lean_uint64_shift_right(v_fold_3794_, v___x_3795_);
v___x_3797_ = lean_uint64_xor(v_fold_3794_, v___x_3796_);
v___x_3798_ = lean_uint64_to_usize(v___x_3797_);
v___x_3799_ = lean_usize_of_nat(v___x_3790_);
v___x_3800_ = ((size_t)1ULL);
v___x_3801_ = lean_usize_sub(v___x_3799_, v___x_3800_);
v___x_3802_ = lean_usize_land(v___x_3798_, v___x_3801_);
v___x_3803_ = lean_array_uget_borrowed(v_buckets_3789_, v___x_3802_);
v___x_3804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg(v_a_3788_, v___x_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg___boxed(lean_object* v_m_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg(v_m_3805_, v_a_3806_);
lean_dec_ref(v_a_3806_);
lean_dec_ref(v_m_3805_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges(lean_object* v_rendering_3810_, lean_object* v_syntaxToRendered_3811_, lean_object* v_syntaxToRenderedByStart_3812_, lean_object* v_syntaxToRenderedByStop_3813_, lean_object* v_range_3814_, lean_object* v_comments_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg(v_syntaxToRendered_3811_, v_range_3814_);
if (lean_obj_tag(v___x_3816_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_dec_ref(v_range_3814_);
v_val_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_val_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(v_rendering_3810_, v_val_3817_);
lean_dec(v_val_3817_);
lean_dec_ref(v_rendering_3810_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set(v___x_3819_, 1, v_comments_3815_);
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_mk_empty_array_with_capacity(v___x_3820_);
v___x_3822_ = lean_array_push(v___x_3821_, v___x_3819_);
return v___x_3822_;
}
else
{
lean_object* v___x_3823_; size_t v_sz_3824_; size_t v___x_3825_; lean_object* v___x_3826_; lean_object* v_fst_3827_; lean_object* v_snd_3828_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v_start_3856_; lean_object* v_stop_3857_; lean_object* v___f_3858_; lean_object* v___f_3859_; lean_object* v___y_3861_; lean_object* v___f_3868_; lean_object* v___x_3869_; 
lean_dec(v___x_3816_);
v___x_3823_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_collectComments_collectTokenComments___redArg___closed__1));
v_sz_3824_ = lean_array_size(v_comments_3815_);
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__1(v_comments_3815_, v_sz_3824_, v___x_3825_, v___x_3823_);
lean_dec_ref(v_comments_3815_);
v_fst_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_fst_3827_);
v_snd_3828_ = lean_ctor_get(v___x_3826_, 1);
lean_inc(v_snd_3828_);
lean_dec_ref(v___x_3826_);
v_start_3856_ = lean_ctor_get(v_range_3814_, 0);
lean_inc(v_start_3856_);
v_stop_3857_ = lean_ctor_get(v_range_3814_, 1);
lean_inc(v_stop_3857_);
lean_dec_ref(v_range_3814_);
v___f_3858_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__0));
v___f_3859_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1));
v___f_3868_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___closed__1));
v___x_3869_ = l_Lean_Fmt_binSearchRightmost___redArg(v_syntaxToRenderedByStop_3813_, v_stop_3857_, v___f_3868_, v___f_3859_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
lean_inc_ref(v_rendering_3810_);
v___x_3871_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__2(v_rendering_3810_, v___x_3870_);
v___y_3861_ = v___x_3871_;
goto v___jp_3860_;
}
else
{
lean_object* v_val_3872_; 
v_val_3872_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v___x_3869_, 1);
v___y_3861_ = v_val_3872_;
goto v___jp_3860_;
}
v___jp_3829_:
{
lean_object* v_snd_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3854_; 
v_snd_3832_ = lean_ctor_get(v___y_3831_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___y_3831_);
if (v_isSharedCheck_3854_ == 0)
{
lean_object* v_unused_3855_; 
v_unused_3855_ = lean_ctor_get(v___y_3831_, 0);
lean_dec(v_unused_3855_);
v___x_3834_ = v___y_3831_;
v_isShared_3835_ = v_isSharedCheck_3854_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_snd_3832_);
lean_dec(v___y_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3854_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_snd_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3852_; 
v_snd_3836_ = lean_ctor_get(v_snd_3832_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_snd_3832_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v_snd_3832_, 0);
lean_dec(v_unused_3853_);
v___x_3838_ = v_snd_3832_;
v_isShared_3839_ = v_isSharedCheck_3852_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_snd_3836_);
lean_dec(v_snd_3832_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3852_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(v_rendering_3810_, v___y_3830_);
lean_dec_ref(v___y_3830_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 1, v_fst_3827_);
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_fst_3827_);
v___x_3842_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_findBestCommentRange(v_rendering_3810_, v_snd_3836_);
lean_dec(v_snd_3836_);
lean_dec_ref(v_rendering_3810_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v_snd_3828_);
lean_ctor_set(v___x_3834_, 0, v___x_3843_);
v___x_3845_ = v___x_3834_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_snd_3828_);
v___x_3845_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3846_ = lean_unsigned_to_nat(2u);
v___x_3847_ = lean_mk_empty_array_with_capacity(v___x_3846_);
v___x_3848_ = lean_array_push(v___x_3847_, v___x_3842_);
v___x_3849_ = lean_array_push(v___x_3848_, v___x_3845_);
return v___x_3849_;
}
}
}
}
}
v___jp_3860_:
{
lean_object* v_snd_3862_; lean_object* v_snd_3863_; lean_object* v___x_3864_; 
v_snd_3862_ = lean_ctor_get(v___y_3861_, 1);
lean_inc(v_snd_3862_);
lean_dec_ref(v___y_3861_);
v_snd_3863_ = lean_ctor_get(v_snd_3862_, 1);
lean_inc(v_snd_3863_);
lean_dec(v_snd_3862_);
v___x_3864_ = l_Lean_Fmt_binSearchLeftmost___redArg(v_syntaxToRenderedByStart_3812_, v_start_3856_, v___f_3858_, v___f_3859_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
lean_inc_ref(v_rendering_3810_);
v___x_3866_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__2(v_rendering_3810_, v___x_3865_);
v___y_3830_ = v_snd_3863_;
v___y_3831_ = v___x_3866_;
goto v___jp_3829_;
}
else
{
lean_object* v_val_3867_; 
v_val_3867_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v___x_3864_, 1);
v___y_3830_ = v_snd_3863_;
v___y_3831_ = v_val_3867_;
goto v___jp_3829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges___boxed(lean_object* v_rendering_3873_, lean_object* v_syntaxToRendered_3874_, lean_object* v_syntaxToRenderedByStart_3875_, lean_object* v_syntaxToRenderedByStop_3876_, lean_object* v_range_3877_, lean_object* v_comments_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges(v_rendering_3873_, v_syntaxToRendered_3874_, v_syntaxToRenderedByStart_3875_, v_syntaxToRenderedByStop_3876_, v_range_3877_, v_comments_3878_);
lean_dec_ref(v_syntaxToRenderedByStop_3876_);
lean_dec_ref(v_syntaxToRenderedByStart_3875_);
lean_dec_ref(v_syntaxToRendered_3874_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0(lean_object* v_00_u03b2_3880_, lean_object* v_m_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___redArg(v_m_3881_, v_a_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0___boxed(lean_object* v_00_u03b2_3884_, lean_object* v_m_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0(v_00_u03b2_3884_, v_m_3885_, v_a_3886_);
lean_dec_ref(v_a_3886_);
lean_dec_ref(v_m_3885_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0(lean_object* v_00_u03b2_3888_, lean_object* v_a_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___redArg(v_a_3889_, v_x_3890_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3892_, lean_object* v_a_3893_, lean_object* v_x_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges_spec__0_spec__0(v_00_u03b2_3892_, v_a_3893_, v_x_3894_);
lean_dec(v_x_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3895_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(uint8_t v___x_3896_, lean_object* v_x_3897_, lean_object* v_x_3898_){
_start:
{
uint8_t v___y_3900_; lean_object* v_fst_3902_; lean_object* v_fst_3903_; lean_object* v_start_3904_; lean_object* v_start_3905_; uint8_t v___x_3906_; 
v_fst_3902_ = lean_ctor_get(v_x_3897_, 0);
v_fst_3903_ = lean_ctor_get(v_x_3898_, 0);
v_start_3904_ = lean_ctor_get(v_fst_3902_, 0);
v_start_3905_ = lean_ctor_get(v_fst_3903_, 0);
v___x_3906_ = l_instOrdRaw__lean_ord(v_start_3904_, v_start_3905_);
if (v___x_3906_ == 1)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3907_ = l_Lean_Syntax_Range_bsize(v_fst_3902_);
v___x_3908_ = l_Lean_Syntax_Range_bsize(v_fst_3903_);
v___x_3909_ = lean_nat_dec_lt(v___x_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_nat_dec_eq(v___x_3907_, v___x_3908_);
lean_dec(v___x_3908_);
lean_dec(v___x_3907_);
if (v___x_3910_ == 0)
{
return v___x_3910_;
}
else
{
v___y_3900_ = v___x_3906_;
goto v___jp_3899_;
}
}
else
{
lean_dec(v___x_3908_);
lean_dec(v___x_3907_);
return v___x_3909_;
}
}
else
{
v___y_3900_ = v___x_3906_;
goto v___jp_3899_;
}
v___jp_3899_:
{
if (v___y_3900_ == 0)
{
return v___x_3896_;
}
else
{
uint8_t v___x_3901_; 
v___x_3901_ = 0;
return v___x_3901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0___boxed(lean_object* v___x_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_){
_start:
{
uint8_t v___x_2799__boxed_3914_; uint8_t v_res_3915_; lean_object* v_r_3916_; 
v___x_2799__boxed_3914_ = lean_unbox(v___x_3911_);
v_res_3915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(v___x_2799__boxed_3914_, v_x_3912_, v_x_3913_);
lean_dec_ref(v_x_3913_);
lean_dec_ref(v_x_3912_);
v_r_3916_ = lean_box(v_res_3915_);
return v_r_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg(lean_object* v_hi_3917_, lean_object* v_pivot_3918_, lean_object* v_as_3919_, lean_object* v_i_3920_, lean_object* v_k_3921_){
_start:
{
uint8_t v___y_3933_; uint8_t v___x_3934_; 
v___x_3934_ = lean_nat_dec_lt(v_k_3921_, v_hi_3917_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec(v_k_3921_);
v___x_3935_ = lean_array_fswap(v_as_3919_, v_i_3920_, v_hi_3917_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v_i_3920_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
return v___x_3936_;
}
else
{
lean_object* v___x_3937_; lean_object* v_fst_3938_; lean_object* v_fst_3939_; lean_object* v_start_3940_; lean_object* v_start_3941_; uint8_t v___x_3942_; 
v___x_3937_ = lean_array_fget_borrowed(v_as_3919_, v_k_3921_);
v_fst_3938_ = lean_ctor_get(v___x_3937_, 0);
v_fst_3939_ = lean_ctor_get(v_pivot_3918_, 0);
v_start_3940_ = lean_ctor_get(v_fst_3938_, 0);
v_start_3941_ = lean_ctor_get(v_fst_3939_, 0);
v___x_3942_ = l_instOrdRaw__lean_ord(v_start_3940_, v_start_3941_);
if (v___x_3942_ == 1)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3943_ = l_Lean_Syntax_Range_bsize(v_fst_3938_);
v___x_3944_ = l_Lean_Syntax_Range_bsize(v_fst_3939_);
v___x_3945_ = lean_nat_dec_lt(v___x_3943_, v___x_3944_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_eq(v___x_3943_, v___x_3944_);
lean_dec(v___x_3944_);
lean_dec(v___x_3943_);
if (v___x_3946_ == 0)
{
goto v___jp_3922_;
}
else
{
v___y_3933_ = v___x_3942_;
goto v___jp_3932_;
}
}
else
{
lean_dec(v___x_3944_);
lean_dec(v___x_3943_);
goto v___jp_3926_;
}
}
else
{
v___y_3933_ = v___x_3942_;
goto v___jp_3932_;
}
}
v___jp_3922_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_k_3921_, v___x_3923_);
lean_dec(v_k_3921_);
v_k_3921_ = v___x_3924_;
goto _start;
}
v___jp_3926_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_array_fswap(v_as_3919_, v_i_3920_, v_k_3921_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_i_3920_, v___x_3928_);
lean_dec(v_i_3920_);
v___x_3930_ = lean_nat_add(v_k_3921_, v___x_3928_);
lean_dec(v_k_3921_);
v_as_3919_ = v___x_3927_;
v_i_3920_ = v___x_3929_;
v_k_3921_ = v___x_3930_;
goto _start;
}
v___jp_3932_:
{
if (v___y_3933_ == 0)
{
goto v___jp_3926_;
}
else
{
goto v___jp_3922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg___boxed(lean_object* v_hi_3947_, lean_object* v_pivot_3948_, lean_object* v_as_3949_, lean_object* v_i_3950_, lean_object* v_k_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg(v_hi_3947_, v_pivot_3948_, v_as_3949_, v_i_3950_, v_k_3951_);
lean_dec_ref(v_pivot_3948_);
lean_dec(v_hi_3947_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(lean_object* v_n_3953_, lean_object* v_as_3954_, lean_object* v_lo_3955_, lean_object* v_hi_3956_){
_start:
{
lean_object* v___y_3958_; uint8_t v___x_3968_; 
v___x_3968_ = lean_nat_dec_lt(v_lo_3955_, v_hi_3956_);
if (v___x_3968_ == 0)
{
lean_dec(v_lo_3955_);
return v_as_3954_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_mid_3971_; lean_object* v___y_3973_; lean_object* v___y_3979_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3969_ = lean_nat_add(v_lo_3955_, v_hi_3956_);
v___x_3970_ = lean_unsigned_to_nat(1u);
v_mid_3971_ = lean_nat_shiftr(v___x_3969_, v___x_3970_);
lean_dec(v___x_3969_);
v___x_3984_ = lean_array_fget_borrowed(v_as_3954_, v_mid_3971_);
v___x_3985_ = lean_array_fget_borrowed(v_as_3954_, v_lo_3955_);
v___x_3986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(v___x_3968_, v___x_3984_, v___x_3985_);
if (v___x_3986_ == 0)
{
v___y_3979_ = v_as_3954_;
goto v___jp_3978_;
}
else
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_array_fswap(v_as_3954_, v_lo_3955_, v_mid_3971_);
v___y_3979_ = v___x_3987_;
goto v___jp_3978_;
}
v___jp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3974_ = lean_array_fget_borrowed(v___y_3973_, v_mid_3971_);
v___x_3975_ = lean_array_fget_borrowed(v___y_3973_, v_hi_3956_);
v___x_3976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(v___x_3968_, v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_dec(v_mid_3971_);
v___y_3958_ = v___y_3973_;
goto v___jp_3957_;
}
else
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_array_fswap(v___y_3973_, v_mid_3971_, v_hi_3956_);
lean_dec(v_mid_3971_);
v___y_3958_ = v___x_3977_;
goto v___jp_3957_;
}
}
v___jp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3980_ = lean_array_fget_borrowed(v___y_3979_, v_hi_3956_);
v___x_3981_ = lean_array_fget_borrowed(v___y_3979_, v_lo_3955_);
v___x_3982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___lam__0(v___x_3968_, v___x_3980_, v___x_3981_);
if (v___x_3982_ == 0)
{
v___y_3973_ = v___y_3979_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_array_fswap(v___y_3979_, v_lo_3955_, v_hi_3956_);
v___y_3973_ = v___x_3983_;
goto v___jp_3972_;
}
}
}
v___jp_3957_:
{
lean_object* v_pivot_3959_; lean_object* v___x_3960_; lean_object* v_fst_3961_; lean_object* v_snd_3962_; uint8_t v___x_3963_; 
v_pivot_3959_ = lean_array_fget(v___y_3958_, v_hi_3956_);
lean_inc_n(v_lo_3955_, 2);
v___x_3960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg(v_hi_3956_, v_pivot_3959_, v___y_3958_, v_lo_3955_, v_lo_3955_);
lean_dec(v_pivot_3959_);
v_fst_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_fst_3961_);
v_snd_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_snd_3962_);
lean_dec_ref(v___x_3960_);
v___x_3963_ = lean_nat_dec_le(v_hi_3956_, v_fst_3961_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(v_n_3953_, v_snd_3962_, v_lo_3955_, v_fst_3961_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_nat_add(v_fst_3961_, v___x_3965_);
lean_dec(v_fst_3961_);
v_as_3954_ = v___x_3964_;
v_lo_3955_ = v___x_3966_;
goto _start;
}
else
{
lean_dec(v_fst_3961_);
lean_dec(v_lo_3955_);
return v_snd_3962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg___boxed(lean_object* v_n_3988_, lean_object* v_as_3989_, lean_object* v_lo_3990_, lean_object* v_hi_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(v_n_3988_, v_as_3989_, v_lo_3990_, v_hi_3991_);
lean_dec(v_hi_3991_);
lean_dec(v_n_3988_);
return v_res_3992_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(uint8_t v___x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_){
_start:
{
uint8_t v___y_3997_; lean_object* v_fst_3999_; lean_object* v_fst_4000_; lean_object* v_stop_4001_; lean_object* v_stop_4002_; uint8_t v___x_4003_; 
v_fst_3999_ = lean_ctor_get(v_x_3994_, 0);
v_fst_4000_ = lean_ctor_get(v_x_3995_, 0);
v_stop_4001_ = lean_ctor_get(v_fst_3999_, 1);
v_stop_4002_ = lean_ctor_get(v_fst_4000_, 1);
v___x_4003_ = l_instOrdRaw__lean_ord(v_stop_4001_, v_stop_4002_);
if (v___x_4003_ == 1)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_4004_ = l_Lean_Syntax_Range_bsize(v_fst_3999_);
v___x_4005_ = l_Lean_Syntax_Range_bsize(v_fst_4000_);
v___x_4006_ = lean_nat_dec_lt(v___x_4004_, v___x_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_eq(v___x_4004_, v___x_4005_);
lean_dec(v___x_4005_);
lean_dec(v___x_4004_);
if (v___x_4007_ == 0)
{
return v___x_4007_;
}
else
{
v___y_3997_ = v___x_4003_;
goto v___jp_3996_;
}
}
else
{
lean_dec(v___x_4005_);
lean_dec(v___x_4004_);
return v___x_4006_;
}
}
else
{
v___y_3997_ = v___x_4003_;
goto v___jp_3996_;
}
v___jp_3996_:
{
if (v___y_3997_ == 0)
{
return v___x_3993_;
}
else
{
uint8_t v___x_3998_; 
v___x_3998_ = 0;
return v___x_3998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0___boxed(lean_object* v___x_4008_, lean_object* v_x_4009_, lean_object* v_x_4010_){
_start:
{
uint8_t v___x_2932__boxed_4011_; uint8_t v_res_4012_; lean_object* v_r_4013_; 
v___x_2932__boxed_4011_ = lean_unbox(v___x_4008_);
v_res_4012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(v___x_2932__boxed_4011_, v_x_4009_, v_x_4010_);
lean_dec_ref(v_x_4010_);
lean_dec_ref(v_x_4009_);
v_r_4013_ = lean_box(v_res_4012_);
return v_r_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg(lean_object* v_hi_4014_, lean_object* v_pivot_4015_, lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_k_4018_){
_start:
{
uint8_t v___y_4030_; uint8_t v___x_4031_; 
v___x_4031_ = lean_nat_dec_lt(v_k_4018_, v_hi_4014_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec(v_k_4018_);
v___x_4032_ = lean_array_fswap(v_as_4016_, v_i_4017_, v_hi_4014_);
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v_i_4017_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; lean_object* v_fst_4035_; lean_object* v_fst_4036_; lean_object* v_stop_4037_; lean_object* v_stop_4038_; uint8_t v___x_4039_; 
v___x_4034_ = lean_array_fget_borrowed(v_as_4016_, v_k_4018_);
v_fst_4035_ = lean_ctor_get(v___x_4034_, 0);
v_fst_4036_ = lean_ctor_get(v_pivot_4015_, 0);
v_stop_4037_ = lean_ctor_get(v_fst_4035_, 1);
v_stop_4038_ = lean_ctor_get(v_fst_4036_, 1);
v___x_4039_ = l_instOrdRaw__lean_ord(v_stop_4037_, v_stop_4038_);
if (v___x_4039_ == 1)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; 
v___x_4040_ = l_Lean_Syntax_Range_bsize(v_fst_4035_);
v___x_4041_ = l_Lean_Syntax_Range_bsize(v_fst_4036_);
v___x_4042_ = lean_nat_dec_lt(v___x_4040_, v___x_4041_);
if (v___x_4042_ == 0)
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_nat_dec_eq(v___x_4040_, v___x_4041_);
lean_dec(v___x_4041_);
lean_dec(v___x_4040_);
if (v___x_4043_ == 0)
{
goto v___jp_4019_;
}
else
{
v___y_4030_ = v___x_4039_;
goto v___jp_4029_;
}
}
else
{
lean_dec(v___x_4041_);
lean_dec(v___x_4040_);
goto v___jp_4023_;
}
}
else
{
v___y_4030_ = v___x_4039_;
goto v___jp_4029_;
}
}
v___jp_4019_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_unsigned_to_nat(1u);
v___x_4021_ = lean_nat_add(v_k_4018_, v___x_4020_);
lean_dec(v_k_4018_);
v_k_4018_ = v___x_4021_;
goto _start;
}
v___jp_4023_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4024_ = lean_array_fswap(v_as_4016_, v_i_4017_, v_k_4018_);
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_nat_add(v_i_4017_, v___x_4025_);
lean_dec(v_i_4017_);
v___x_4027_ = lean_nat_add(v_k_4018_, v___x_4025_);
lean_dec(v_k_4018_);
v_as_4016_ = v___x_4024_;
v_i_4017_ = v___x_4026_;
v_k_4018_ = v___x_4027_;
goto _start;
}
v___jp_4029_:
{
if (v___y_4030_ == 0)
{
goto v___jp_4023_;
}
else
{
goto v___jp_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg___boxed(lean_object* v_hi_4044_, lean_object* v_pivot_4045_, lean_object* v_as_4046_, lean_object* v_i_4047_, lean_object* v_k_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg(v_hi_4044_, v_pivot_4045_, v_as_4046_, v_i_4047_, v_k_4048_);
lean_dec_ref(v_pivot_4045_);
lean_dec(v_hi_4044_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(lean_object* v_n_4050_, lean_object* v_as_4051_, lean_object* v_lo_4052_, lean_object* v_hi_4053_){
_start:
{
lean_object* v___y_4055_; uint8_t v___x_4065_; 
v___x_4065_ = lean_nat_dec_lt(v_lo_4052_, v_hi_4053_);
if (v___x_4065_ == 0)
{
lean_dec(v_lo_4052_);
return v_as_4051_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v_mid_4068_; lean_object* v___y_4070_; lean_object* v___y_4076_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
v___x_4066_ = lean_nat_add(v_lo_4052_, v_hi_4053_);
v___x_4067_ = lean_unsigned_to_nat(1u);
v_mid_4068_ = lean_nat_shiftr(v___x_4066_, v___x_4067_);
lean_dec(v___x_4066_);
v___x_4081_ = lean_array_fget_borrowed(v_as_4051_, v_mid_4068_);
v___x_4082_ = lean_array_fget_borrowed(v_as_4051_, v_lo_4052_);
v___x_4083_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(v___x_4065_, v___x_4081_, v___x_4082_);
if (v___x_4083_ == 0)
{
v___y_4076_ = v_as_4051_;
goto v___jp_4075_;
}
else
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_array_fswap(v_as_4051_, v_lo_4052_, v_mid_4068_);
v___y_4076_ = v___x_4084_;
goto v___jp_4075_;
}
v___jp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4071_ = lean_array_fget_borrowed(v___y_4070_, v_mid_4068_);
v___x_4072_ = lean_array_fget_borrowed(v___y_4070_, v_hi_4053_);
v___x_4073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(v___x_4065_, v___x_4071_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_dec(v_mid_4068_);
v___y_4055_ = v___y_4070_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_array_fswap(v___y_4070_, v_mid_4068_, v_hi_4053_);
lean_dec(v_mid_4068_);
v___y_4055_ = v___x_4074_;
goto v___jp_4054_;
}
}
v___jp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4077_ = lean_array_fget_borrowed(v___y_4076_, v_hi_4053_);
v___x_4078_ = lean_array_fget_borrowed(v___y_4076_, v_lo_4052_);
v___x_4079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___lam__0(v___x_4065_, v___x_4077_, v___x_4078_);
if (v___x_4079_ == 0)
{
v___y_4070_ = v___y_4076_;
goto v___jp_4069_;
}
else
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_array_fswap(v___y_4076_, v_lo_4052_, v_hi_4053_);
v___y_4070_ = v___x_4080_;
goto v___jp_4069_;
}
}
}
v___jp_4054_:
{
lean_object* v_pivot_4056_; lean_object* v___x_4057_; lean_object* v_fst_4058_; lean_object* v_snd_4059_; uint8_t v___x_4060_; 
v_pivot_4056_ = lean_array_fget(v___y_4055_, v_hi_4053_);
lean_inc_n(v_lo_4052_, 2);
v___x_4057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg(v_hi_4053_, v_pivot_4056_, v___y_4055_, v_lo_4052_, v_lo_4052_);
lean_dec(v_pivot_4056_);
v_fst_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_fst_4058_);
v_snd_4059_ = lean_ctor_get(v___x_4057_, 1);
lean_inc(v_snd_4059_);
lean_dec_ref(v___x_4057_);
v___x_4060_ = lean_nat_dec_le(v_hi_4053_, v_fst_4058_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(v_n_4050_, v_snd_4059_, v_lo_4052_, v_fst_4058_);
v___x_4062_ = lean_unsigned_to_nat(1u);
v___x_4063_ = lean_nat_add(v_fst_4058_, v___x_4062_);
lean_dec(v_fst_4058_);
v_as_4051_ = v___x_4061_;
v_lo_4052_ = v___x_4063_;
goto _start;
}
else
{
lean_dec(v_fst_4058_);
lean_dec(v_lo_4052_);
return v_snd_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg___boxed(lean_object* v_n_4085_, lean_object* v_as_4086_, lean_object* v_lo_4087_, lean_object* v_hi_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(v_n_4085_, v_as_4086_, v_lo_4087_, v_hi_4088_);
lean_dec(v_hi_4088_);
lean_dec(v_n_4085_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg(lean_object* v_hi_4090_, lean_object* v_pivot_4091_, lean_object* v_as_4092_, lean_object* v_i_4093_, lean_object* v_k_4094_){
_start:
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_nat_dec_lt(v_k_4094_, v_hi_4090_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v_k_4094_);
v___x_4096_ = lean_array_fswap(v_as_4092_, v_i_4093_, v_hi_4090_);
v___x_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4097_, 0, v_i_4093_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
return v___x_4097_;
}
else
{
lean_object* v___x_4098_; lean_object* v_fst_4099_; lean_object* v_fst_4100_; uint8_t v___x_4101_; uint8_t v___x_4102_; uint8_t v___x_4103_; 
v___x_4098_ = lean_array_fget_borrowed(v_as_4092_, v_k_4094_);
v_fst_4099_ = lean_ctor_get(v___x_4098_, 0);
v_fst_4100_ = lean_ctor_get(v_pivot_4091_, 0);
v___x_4101_ = l_Lean_Fmt_compareRanges(v_fst_4099_, v_fst_4100_);
v___x_4102_ = 0;
v___x_4103_ = l_instDecidableEqOrdering(v___x_4101_, v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_unsigned_to_nat(1u);
v___x_4105_ = lean_nat_add(v_k_4094_, v___x_4104_);
lean_dec(v_k_4094_);
v_k_4094_ = v___x_4105_;
goto _start;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4107_ = lean_array_fswap(v_as_4092_, v_i_4093_, v_k_4094_);
v___x_4108_ = lean_unsigned_to_nat(1u);
v___x_4109_ = lean_nat_add(v_i_4093_, v___x_4108_);
lean_dec(v_i_4093_);
v___x_4110_ = lean_nat_add(v_k_4094_, v___x_4108_);
lean_dec(v_k_4094_);
v_as_4092_ = v___x_4107_;
v_i_4093_ = v___x_4109_;
v_k_4094_ = v___x_4110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg___boxed(lean_object* v_hi_4112_, lean_object* v_pivot_4113_, lean_object* v_as_4114_, lean_object* v_i_4115_, lean_object* v_k_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg(v_hi_4112_, v_pivot_4113_, v_as_4114_, v_i_4115_, v_k_4116_);
lean_dec_ref(v_pivot_4113_);
lean_dec(v_hi_4112_);
return v_res_4117_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(lean_object* v_x_4118_, lean_object* v_x_4119_){
_start:
{
lean_object* v_fst_4120_; lean_object* v_fst_4121_; uint8_t v___x_4122_; uint8_t v___x_4123_; uint8_t v___x_4124_; 
v_fst_4120_ = lean_ctor_get(v_x_4118_, 0);
v_fst_4121_ = lean_ctor_get(v_x_4119_, 0);
v___x_4122_ = l_Lean_Fmt_compareRanges(v_fst_4120_, v_fst_4121_);
v___x_4123_ = 0;
v___x_4124_ = l_instDecidableEqOrdering(v___x_4122_, v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0___boxed(lean_object* v_x_4125_, lean_object* v_x_4126_){
_start:
{
uint8_t v_res_4127_; lean_object* v_r_4128_; 
v_res_4127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(v_x_4125_, v_x_4126_);
lean_dec_ref(v_x_4126_);
lean_dec_ref(v_x_4125_);
v_r_4128_ = lean_box(v_res_4127_);
return v_r_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(lean_object* v_n_4129_, lean_object* v_as_4130_, lean_object* v_lo_4131_, lean_object* v_hi_4132_){
_start:
{
lean_object* v___y_4134_; uint8_t v___x_4144_; 
v___x_4144_ = lean_nat_dec_lt(v_lo_4131_, v_hi_4132_);
if (v___x_4144_ == 0)
{
lean_dec(v_lo_4131_);
return v_as_4130_;
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v_mid_4147_; lean_object* v___y_4149_; lean_object* v___y_4155_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v___x_4145_ = lean_nat_add(v_lo_4131_, v_hi_4132_);
v___x_4146_ = lean_unsigned_to_nat(1u);
v_mid_4147_ = lean_nat_shiftr(v___x_4145_, v___x_4146_);
lean_dec(v___x_4145_);
v___x_4160_ = lean_array_fget_borrowed(v_as_4130_, v_mid_4147_);
v___x_4161_ = lean_array_fget_borrowed(v_as_4130_, v_lo_4131_);
v___x_4162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(v___x_4160_, v___x_4161_);
if (v___x_4162_ == 0)
{
v___y_4155_ = v_as_4130_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_array_fswap(v_as_4130_, v_lo_4131_, v_mid_4147_);
v___y_4155_ = v___x_4163_;
goto v___jp_4154_;
}
v___jp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4150_ = lean_array_fget_borrowed(v___y_4149_, v_mid_4147_);
v___x_4151_ = lean_array_fget_borrowed(v___y_4149_, v_hi_4132_);
v___x_4152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(v___x_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_dec(v_mid_4147_);
v___y_4134_ = v___y_4149_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4153_; 
v___x_4153_ = lean_array_fswap(v___y_4149_, v_mid_4147_, v_hi_4132_);
lean_dec(v_mid_4147_);
v___y_4134_ = v___x_4153_;
goto v___jp_4133_;
}
}
v___jp_4154_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v___x_4156_ = lean_array_fget_borrowed(v___y_4155_, v_hi_4132_);
v___x_4157_ = lean_array_fget_borrowed(v___y_4155_, v_lo_4131_);
v___x_4158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___lam__0(v___x_4156_, v___x_4157_);
if (v___x_4158_ == 0)
{
v___y_4149_ = v___y_4155_;
goto v___jp_4148_;
}
else
{
lean_object* v___x_4159_; 
v___x_4159_ = lean_array_fswap(v___y_4155_, v_lo_4131_, v_hi_4132_);
v___y_4149_ = v___x_4159_;
goto v___jp_4148_;
}
}
}
v___jp_4133_:
{
lean_object* v_pivot_4135_; lean_object* v___x_4136_; lean_object* v_fst_4137_; lean_object* v_snd_4138_; uint8_t v___x_4139_; 
v_pivot_4135_ = lean_array_fget(v___y_4134_, v_hi_4132_);
lean_inc_n(v_lo_4131_, 2);
v___x_4136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg(v_hi_4132_, v_pivot_4135_, v___y_4134_, v_lo_4131_, v_lo_4131_);
lean_dec(v_pivot_4135_);
v_fst_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_fst_4137_);
v_snd_4138_ = lean_ctor_get(v___x_4136_, 1);
lean_inc(v_snd_4138_);
lean_dec_ref(v___x_4136_);
v___x_4139_ = lean_nat_dec_le(v_hi_4132_, v_fst_4137_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(v_n_4129_, v_snd_4138_, v_lo_4131_, v_fst_4137_);
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = lean_nat_add(v_fst_4137_, v___x_4141_);
lean_dec(v_fst_4137_);
v_as_4130_ = v___x_4140_;
v_lo_4131_ = v___x_4142_;
goto _start;
}
else
{
lean_dec(v_fst_4137_);
lean_dec(v_lo_4131_);
return v_snd_4138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg___boxed(lean_object* v_n_4164_, lean_object* v_as_4165_, lean_object* v_lo_4166_, lean_object* v_hi_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(v_n_4164_, v_as_4165_, v_lo_4166_, v_hi_4167_);
lean_dec(v_hi_4167_);
lean_dec(v_n_4164_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4(lean_object* v_x_4169_, lean_object* v_x_4170_){
_start:
{
if (lean_obj_tag(v_x_4170_) == 0)
{
return v_x_4169_;
}
else
{
lean_object* v_key_4171_; lean_object* v_value_4172_; lean_object* v_tail_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_key_4171_ = lean_ctor_get(v_x_4170_, 0);
v_value_4172_ = lean_ctor_get(v_x_4170_, 1);
v_tail_4173_ = lean_ctor_get(v_x_4170_, 2);
lean_inc(v_value_4172_);
lean_inc(v_key_4171_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v_key_4171_);
lean_ctor_set(v___x_4174_, 1, v_value_4172_);
v___x_4175_ = lean_array_push(v_x_4169_, v___x_4174_);
v_x_4169_ = v___x_4175_;
v_x_4170_ = v_tail_4173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4___boxed(lean_object* v_x_4177_, lean_object* v_x_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4(v_x_4177_, v_x_4178_);
lean_dec(v_x_4178_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5(lean_object* v_as_4180_, size_t v_i_4181_, size_t v_stop_4182_, lean_object* v_b_4183_){
_start:
{
uint8_t v___x_4184_; 
v___x_4184_ = lean_usize_dec_eq(v_i_4181_, v_stop_4182_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; size_t v___x_4187_; size_t v___x_4188_; 
v___x_4185_ = lean_array_uget_borrowed(v_as_4180_, v_i_4181_);
v___x_4186_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__4(v_b_4183_, v___x_4185_);
v___x_4187_ = ((size_t)1ULL);
v___x_4188_ = lean_usize_add(v_i_4181_, v___x_4187_);
v_i_4181_ = v___x_4188_;
v_b_4183_ = v___x_4186_;
goto _start;
}
else
{
return v_b_4183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5___boxed(lean_object* v_as_4190_, lean_object* v_i_4191_, lean_object* v_stop_4192_, lean_object* v_b_4193_){
_start:
{
size_t v_i_boxed_4194_; size_t v_stop_boxed_4195_; lean_object* v_res_4196_; 
v_i_boxed_4194_ = lean_unbox_usize(v_i_4191_);
lean_dec(v_i_4191_);
v_stop_boxed_4195_ = lean_unbox_usize(v_stop_4192_);
lean_dec(v_stop_4192_);
v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5(v_as_4190_, v_i_boxed_4194_, v_stop_boxed_4195_, v_b_4193_);
lean_dec_ref(v_as_4190_);
return v_res_4196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(lean_object* v_a_4197_, lean_object* v_x_4198_){
_start:
{
if (lean_obj_tag(v_x_4198_) == 0)
{
uint8_t v___x_4199_; 
v___x_4199_ = 0;
return v___x_4199_;
}
else
{
lean_object* v_key_4200_; lean_object* v_tail_4201_; uint8_t v___x_4202_; 
v_key_4200_ = lean_ctor_get(v_x_4198_, 0);
v_tail_4201_ = lean_ctor_get(v_x_4198_, 2);
v___x_4202_ = l_instBEqSubslice__lean_beq___redArg(v_key_4200_, v_a_4197_);
if (v___x_4202_ == 0)
{
v_x_4198_ = v_tail_4201_;
goto _start;
}
else
{
return v___x_4202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg___boxed(lean_object* v_a_4204_, lean_object* v_x_4205_){
_start:
{
uint8_t v_res_4206_; lean_object* v_r_4207_; 
v_res_4206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(v_a_4204_, v_x_4205_);
lean_dec(v_x_4205_);
lean_dec_ref(v_a_4204_);
v_r_4207_ = lean_box(v_res_4206_);
return v_r_4207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg___lam__0(lean_object* v_snd_4208_, lean_object* v_x_4209_){
_start:
{
if (lean_obj_tag(v_x_4209_) == 0)
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_snd_4208_);
return v___x_4210_;
}
else
{
lean_object* v_val_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_val_4211_ = lean_ctor_get(v_x_4209_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_x_4209_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v_x_4209_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_val_4211_);
lean_dec(v_x_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = l_Array_append___redArg(v_val_4211_, v_snd_4208_);
lean_dec_ref(v_snd_4208_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg(lean_object* v_snd_4220_, lean_object* v_a_4221_, lean_object* v_x_4222_){
_start:
{
if (lean_obj_tag(v_x_4222_) == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v_val_4225_; lean_object* v___x_4226_; 
v___x_4223_ = lean_box(0);
v___x_4224_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg___lam__0(v_snd_4220_, v___x_4223_);
v_val_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_val_4225_);
lean_dec(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4226_, 0, v_a_4221_);
lean_ctor_set(v___x_4226_, 1, v_val_4225_);
lean_ctor_set(v___x_4226_, 2, v_x_4222_);
return v___x_4226_;
}
else
{
lean_object* v_key_4227_; lean_object* v_value_4228_; lean_object* v_tail_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4244_; 
v_key_4227_ = lean_ctor_get(v_x_4222_, 0);
v_value_4228_ = lean_ctor_get(v_x_4222_, 1);
v_tail_4229_ = lean_ctor_get(v_x_4222_, 2);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_x_4222_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4231_ = v_x_4222_;
v_isShared_4232_ = v_isSharedCheck_4244_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_tail_4229_);
lean_inc(v_value_4228_);
lean_inc(v_key_4227_);
lean_dec(v_x_4222_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4244_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
uint8_t v___x_4233_; 
v___x_4233_ = l_instBEqSubslice__lean_beq___redArg(v_key_4227_, v_a_4221_);
if (v___x_4233_ == 0)
{
lean_object* v_tail_4234_; lean_object* v___x_4236_; 
v_tail_4234_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg(v_snd_4220_, v_a_4221_, v_tail_4229_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 2, v_tail_4234_);
v___x_4236_ = v___x_4231_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_key_4227_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_value_4228_);
lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_tail_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v_val_4240_; lean_object* v___x_4242_; 
lean_dec(v_key_4227_);
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_value_4228_);
v___x_4239_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg___lam__0(v_snd_4220_, v___x_4238_);
v_val_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_val_4240_);
lean_dec(v___x_4239_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 1, v_val_4240_);
lean_ctor_set(v___x_4231_, 0, v_a_4221_);
v___x_4242_ = v___x_4231_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4221_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_val_4240_);
lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_tail_4229_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___redArg(lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
if (lean_obj_tag(v_x_4246_) == 0)
{
return v_x_4245_;
}
else
{
lean_object* v_key_4247_; lean_object* v_value_4248_; lean_object* v_tail_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4272_; 
v_key_4247_ = lean_ctor_get(v_x_4246_, 0);
v_value_4248_ = lean_ctor_get(v_x_4246_, 1);
v_tail_4249_ = lean_ctor_get(v_x_4246_, 2);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_x_4246_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4251_ = v_x_4246_;
v_isShared_4252_ = v_isSharedCheck_4272_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_tail_4249_);
lean_inc(v_value_4248_);
lean_inc(v_key_4247_);
lean_dec(v_x_4246_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4272_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4253_; uint64_t v___x_4254_; uint64_t v___x_4255_; uint64_t v___x_4256_; uint64_t v_fold_4257_; uint64_t v___x_4258_; uint64_t v___x_4259_; uint64_t v___x_4260_; size_t v___x_4261_; size_t v___x_4262_; size_t v___x_4263_; size_t v___x_4264_; size_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4253_ = lean_array_get_size(v_x_4245_);
v___x_4254_ = l_instHashableSubslice__lean_hash___redArg(v_key_4247_);
v___x_4255_ = 32ULL;
v___x_4256_ = lean_uint64_shift_right(v___x_4254_, v___x_4255_);
v_fold_4257_ = lean_uint64_xor(v___x_4254_, v___x_4256_);
v___x_4258_ = 16ULL;
v___x_4259_ = lean_uint64_shift_right(v_fold_4257_, v___x_4258_);
v___x_4260_ = lean_uint64_xor(v_fold_4257_, v___x_4259_);
v___x_4261_ = lean_uint64_to_usize(v___x_4260_);
v___x_4262_ = lean_usize_of_nat(v___x_4253_);
v___x_4263_ = ((size_t)1ULL);
v___x_4264_ = lean_usize_sub(v___x_4262_, v___x_4263_);
v___x_4265_ = lean_usize_land(v___x_4261_, v___x_4264_);
v___x_4266_ = lean_array_uget_borrowed(v_x_4245_, v___x_4265_);
lean_inc(v___x_4266_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 2, v___x_4266_);
v___x_4268_ = v___x_4251_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_key_4247_);
lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_value_4248_);
lean_ctor_set(v_reuseFailAlloc_4271_, 2, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_array_uset(v_x_4245_, v___x_4265_, v___x_4268_);
v_x_4245_ = v___x_4269_;
v_x_4246_ = v_tail_4249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg(lean_object* v_rendering_4273_, lean_object* v_i_4274_, lean_object* v_source_4275_, lean_object* v_target_4276_){
_start:
{
lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4277_ = lean_array_get_size(v_source_4275_);
v___x_4278_ = lean_nat_dec_lt(v_i_4274_, v___x_4277_);
if (v___x_4278_ == 0)
{
lean_dec_ref(v_source_4275_);
lean_dec(v_i_4274_);
return v_target_4276_;
}
else
{
lean_object* v_es_4279_; lean_object* v___x_4280_; lean_object* v_source_4281_; lean_object* v_target_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v_es_4279_ = lean_array_fget(v_source_4275_, v_i_4274_);
v___x_4280_ = lean_box(0);
v_source_4281_ = lean_array_fset(v_source_4275_, v_i_4274_, v___x_4280_);
v_target_4282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___redArg(v_target_4276_, v_es_4279_);
v___x_4283_ = lean_unsigned_to_nat(1u);
v___x_4284_ = lean_nat_add(v_i_4274_, v___x_4283_);
lean_dec(v_i_4274_);
v_i_4274_ = v___x_4284_;
v_source_4275_ = v_source_4281_;
v_target_4276_ = v_target_4282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_rendering_4286_, lean_object* v_i_4287_, lean_object* v_source_4288_, lean_object* v_target_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg(v_rendering_4286_, v_i_4287_, v_source_4288_, v_target_4289_);
lean_dec_ref(v_rendering_4286_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg(lean_object* v_rendering_4291_, lean_object* v_data_4292_){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v_nbuckets_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4293_ = lean_array_get_size(v_data_4292_);
v___x_4294_ = lean_unsigned_to_nat(2u);
v_nbuckets_4295_ = lean_nat_mul(v___x_4293_, v___x_4294_);
v___x_4296_ = lean_unsigned_to_nat(0u);
v___x_4297_ = lean_box(0);
v___x_4298_ = lean_mk_array(v_nbuckets_4295_, v___x_4297_);
v___x_4299_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg(v_rendering_4291_, v___x_4296_, v_data_4292_, v___x_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg___boxed(lean_object* v_rendering_4300_, lean_object* v_data_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg(v_rendering_4300_, v_data_4301_);
lean_dec_ref(v_rendering_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0(lean_object* v_rendering_4303_, lean_object* v_snd_4304_, lean_object* v_m_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_size_4307_; lean_object* v_buckets_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4356_; 
v_size_4307_ = lean_ctor_get(v_m_4305_, 0);
v_buckets_4308_ = lean_ctor_get(v_m_4305_, 1);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_m_4305_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4310_ = v_m_4305_;
v_isShared_4311_ = v_isSharedCheck_4356_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_buckets_4308_);
lean_inc(v_size_4307_);
lean_dec(v_m_4305_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4356_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; uint64_t v___x_4313_; uint64_t v___x_4314_; uint64_t v___x_4315_; uint64_t v_fold_4316_; uint64_t v___x_4317_; uint64_t v___x_4318_; uint64_t v___x_4319_; size_t v___x_4320_; size_t v___x_4321_; size_t v___x_4322_; size_t v___x_4323_; size_t v___x_4324_; lean_object* v_bkt_4325_; uint8_t v___x_4326_; 
v___x_4312_ = lean_array_get_size(v_buckets_4308_);
v___x_4313_ = l_instHashableSubslice__lean_hash___redArg(v_a_4306_);
v___x_4314_ = 32ULL;
v___x_4315_ = lean_uint64_shift_right(v___x_4313_, v___x_4314_);
v_fold_4316_ = lean_uint64_xor(v___x_4313_, v___x_4315_);
v___x_4317_ = 16ULL;
v___x_4318_ = lean_uint64_shift_right(v_fold_4316_, v___x_4317_);
v___x_4319_ = lean_uint64_xor(v_fold_4316_, v___x_4318_);
v___x_4320_ = lean_uint64_to_usize(v___x_4319_);
v___x_4321_ = lean_usize_of_nat(v___x_4312_);
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_sub(v___x_4321_, v___x_4322_);
v___x_4324_ = lean_usize_land(v___x_4320_, v___x_4323_);
v_bkt_4325_ = lean_array_uget_borrowed(v_buckets_4308_, v___x_4324_);
v___x_4326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(v_a_4306_, v_bkt_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v_size_x27_4328_; lean_object* v___x_4329_; lean_object* v_buckets_x27_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4327_ = lean_unsigned_to_nat(1u);
v_size_x27_4328_ = lean_nat_add(v_size_4307_, v___x_4327_);
lean_dec(v_size_4307_);
lean_inc(v_bkt_4325_);
v___x_4329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4329_, 0, v_a_4306_);
lean_ctor_set(v___x_4329_, 1, v_snd_4304_);
lean_ctor_set(v___x_4329_, 2, v_bkt_4325_);
v_buckets_x27_4330_ = lean_array_uset(v_buckets_4308_, v___x_4324_, v___x_4329_);
v___x_4331_ = lean_unsigned_to_nat(4u);
v___x_4332_ = lean_nat_mul(v_size_x27_4328_, v___x_4331_);
v___x_4333_ = lean_unsigned_to_nat(3u);
v___x_4334_ = lean_nat_div(v___x_4332_, v___x_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_array_get_size(v_buckets_x27_4330_);
v___x_4336_ = lean_nat_dec_le(v___x_4334_, v___x_4335_);
lean_dec(v___x_4334_);
if (v___x_4336_ == 0)
{
lean_object* v_val_4337_; lean_object* v___x_4339_; 
v_val_4337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg(v_rendering_4303_, v_buckets_x27_4330_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v_val_4337_);
lean_ctor_set(v___x_4310_, 0, v_size_x27_4328_);
v___x_4339_ = v___x_4310_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_size_x27_4328_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_val_4337_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
else
{
lean_object* v___x_4342_; 
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v_buckets_x27_4330_);
lean_ctor_set(v___x_4310_, 0, v_size_x27_4328_);
v___x_4342_ = v___x_4310_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_size_x27_4328_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_buckets_x27_4330_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
else
{
lean_object* v___x_4344_; lean_object* v_buckets_x27_4345_; lean_object* v_bkt_x27_4346_; lean_object* v___y_4348_; uint8_t v___x_4353_; 
lean_inc(v_bkt_4325_);
v___x_4344_ = lean_box(0);
v_buckets_x27_4345_ = lean_array_uset(v_buckets_4308_, v___x_4324_, v___x_4344_);
lean_inc_ref(v_a_4306_);
v_bkt_x27_4346_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg(v_snd_4304_, v_a_4306_, v_bkt_4325_);
v___x_4353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(v_a_4306_, v_bkt_x27_4346_);
lean_dec_ref(v_a_4306_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_unsigned_to_nat(1u);
v___x_4355_ = lean_nat_sub(v_size_4307_, v___x_4354_);
lean_dec(v_size_4307_);
v___y_4348_ = v___x_4355_;
goto v___jp_4347_;
}
else
{
v___y_4348_ = v_size_4307_;
goto v___jp_4347_;
}
v___jp_4347_:
{
lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4349_ = lean_array_uset(v_buckets_x27_4345_, v___x_4324_, v_bkt_x27_4346_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v___x_4349_);
lean_ctor_set(v___x_4310_, 0, v___y_4348_);
v___x_4351_ = v___x_4310_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___y_4348_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0___boxed(lean_object* v_rendering_4357_, lean_object* v_snd_4358_, lean_object* v_m_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0(v_rendering_4357_, v_snd_4358_, v_m_4359_, v_a_4360_);
lean_dec_ref(v_rendering_4357_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1(lean_object* v_rendering_4362_, lean_object* v_as_4363_, size_t v_sz_4364_, size_t v_i_4365_, lean_object* v_b_4366_){
_start:
{
uint8_t v___x_4367_; 
v___x_4367_ = lean_usize_dec_lt(v_i_4365_, v_sz_4364_);
if (v___x_4367_ == 0)
{
return v_b_4366_;
}
else
{
lean_object* v_a_4368_; lean_object* v_fst_4369_; lean_object* v_snd_4370_; lean_object* v___x_4371_; size_t v___x_4372_; size_t v___x_4373_; 
v_a_4368_ = lean_array_uget_borrowed(v_as_4363_, v_i_4365_);
v_fst_4369_ = lean_ctor_get(v_a_4368_, 0);
v_snd_4370_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_fst_4369_);
lean_inc(v_snd_4370_);
v___x_4371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0(v_rendering_4362_, v_snd_4370_, v_b_4366_, v_fst_4369_);
v___x_4372_ = ((size_t)1ULL);
v___x_4373_ = lean_usize_add(v_i_4365_, v___x_4372_);
v_i_4365_ = v___x_4373_;
v_b_4366_ = v___x_4371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1___boxed(lean_object* v_rendering_4375_, lean_object* v_as_4376_, lean_object* v_sz_4377_, lean_object* v_i_4378_, lean_object* v_b_4379_){
_start:
{
size_t v_sz_boxed_4380_; size_t v_i_boxed_4381_; lean_object* v_res_4382_; 
v_sz_boxed_4380_ = lean_unbox_usize(v_sz_4377_);
lean_dec(v_sz_4377_);
v_i_boxed_4381_ = lean_unbox_usize(v_i_4378_);
lean_dec(v_i_4378_);
v_res_4382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1(v_rendering_4375_, v_as_4376_, v_sz_boxed_4380_, v_i_boxed_4381_, v_b_4379_);
lean_dec_ref(v_as_4376_);
lean_dec_ref(v_rendering_4375_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2(lean_object* v_rendering_4383_, lean_object* v_syntaxToRendered_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v_as_4387_, size_t v_sz_4388_, size_t v_i_4389_, lean_object* v_b_4390_){
_start:
{
uint8_t v___x_4391_; 
v___x_4391_ = lean_usize_dec_lt(v_i_4389_, v_sz_4388_);
if (v___x_4391_ == 0)
{
lean_dec_ref(v_rendering_4383_);
return v_b_4390_;
}
else
{
lean_object* v_a_4392_; lean_object* v_fst_4393_; lean_object* v_snd_4394_; lean_object* v___x_4395_; size_t v_sz_4396_; size_t v___x_4397_; lean_object* v___x_4398_; size_t v___x_4399_; size_t v___x_4400_; 
v_a_4392_ = lean_array_uget_borrowed(v_as_4387_, v_i_4389_);
v_fst_4393_ = lean_ctor_get(v_a_4392_, 0);
v_snd_4394_ = lean_ctor_get(v_a_4392_, 1);
lean_inc(v_snd_4394_);
lean_inc(v_fst_4393_);
lean_inc_ref(v_rendering_4383_);
v___x_4395_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_determineRenderedCommentRanges(v_rendering_4383_, v_syntaxToRendered_4384_, v___y_4385_, v___y_4386_, v_fst_4393_, v_snd_4394_);
v_sz_4396_ = lean_array_size(v___x_4395_);
v___x_4397_ = ((size_t)0ULL);
v___x_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__1(v_rendering_4383_, v___x_4395_, v_sz_4396_, v___x_4397_, v_b_4390_);
lean_dec_ref(v___x_4395_);
v___x_4399_ = ((size_t)1ULL);
v___x_4400_ = lean_usize_add(v_i_4389_, v___x_4399_);
v_i_4389_ = v___x_4400_;
v_b_4390_ = v___x_4398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2___boxed(lean_object* v_rendering_4402_, lean_object* v_syntaxToRendered_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v_as_4406_, lean_object* v_sz_4407_, lean_object* v_i_4408_, lean_object* v_b_4409_){
_start:
{
size_t v_sz_boxed_4410_; size_t v_i_boxed_4411_; lean_object* v_res_4412_; 
v_sz_boxed_4410_ = lean_unbox_usize(v_sz_4407_);
lean_dec(v_sz_4407_);
v_i_boxed_4411_ = lean_unbox_usize(v_i_4408_);
lean_dec(v_i_4408_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2(v_rendering_4402_, v_syntaxToRendered_4403_, v___y_4404_, v___y_4405_, v_as_4406_, v_sz_boxed_4410_, v_i_boxed_4411_, v_b_4409_);
lean_dec_ref(v_as_4406_);
lean_dec_ref(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec_ref(v_syntaxToRendered_4403_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8(lean_object* v_x_4413_, lean_object* v_x_4414_){
_start:
{
if (lean_obj_tag(v_x_4414_) == 0)
{
return v_x_4413_;
}
else
{
lean_object* v_key_4415_; lean_object* v_value_4416_; lean_object* v_tail_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v_key_4415_ = lean_ctor_get(v_x_4414_, 0);
v_value_4416_ = lean_ctor_get(v_x_4414_, 1);
v_tail_4417_ = lean_ctor_get(v_x_4414_, 2);
lean_inc(v_value_4416_);
lean_inc(v_key_4415_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v_key_4415_);
lean_ctor_set(v___x_4418_, 1, v_value_4416_);
v___x_4419_ = lean_array_push(v_x_4413_, v___x_4418_);
v_x_4413_ = v___x_4419_;
v_x_4414_ = v_tail_4417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8___boxed(lean_object* v_x_4421_, lean_object* v_x_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8(v_x_4421_, v_x_4422_);
lean_dec(v_x_4422_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9(lean_object* v_as_4424_, size_t v_i_4425_, size_t v_stop_4426_, lean_object* v_b_4427_){
_start:
{
uint8_t v___x_4428_; 
v___x_4428_ = lean_usize_dec_eq(v_i_4425_, v_stop_4426_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; size_t v___x_4431_; size_t v___x_4432_; 
v___x_4429_ = lean_array_uget_borrowed(v_as_4424_, v_i_4425_);
v___x_4430_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__8(v_b_4427_, v___x_4429_);
v___x_4431_ = ((size_t)1ULL);
v___x_4432_ = lean_usize_add(v_i_4425_, v___x_4431_);
v_i_4425_ = v___x_4432_;
v_b_4427_ = v___x_4430_;
goto _start;
}
else
{
return v_b_4427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9___boxed(lean_object* v_as_4434_, lean_object* v_i_4435_, lean_object* v_stop_4436_, lean_object* v_b_4437_){
_start:
{
size_t v_i_boxed_4438_; size_t v_stop_boxed_4439_; lean_object* v_res_4440_; 
v_i_boxed_4438_ = lean_unbox_usize(v_i_4435_);
lean_dec(v_i_4435_);
v_stop_boxed_4439_ = lean_unbox_usize(v_stop_4436_);
lean_dec(v_stop_4436_);
v_res_4440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9(v_as_4434_, v_i_boxed_4438_, v_stop_boxed_4439_, v_b_4437_);
lean_dec_ref(v_as_4434_);
return v_res_4440_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = lean_box(0);
v___x_4442_ = lean_unsigned_to_nat(16u);
v___x_4443_ = lean_mk_array(v___x_4442_, v___x_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments(lean_object* v_rendering_4444_, lean_object* v_syntaxToRendered_4445_, lean_object* v_comments_4446_){
_start:
{
lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4547_; lean_object* v_size_4554_; lean_object* v_buckets_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; 
v_size_4554_ = lean_ctor_get(v_syntaxToRendered_4445_, 0);
v_buckets_4555_ = lean_ctor_get(v_syntaxToRendered_4445_, 1);
v___x_4556_ = lean_mk_empty_array_with_capacity(v_size_4554_);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = lean_array_get_size(v_buckets_4555_);
v___x_4559_ = lean_nat_dec_lt(v___x_4557_, v___x_4558_);
if (v___x_4559_ == 0)
{
v___y_4547_ = v___x_4556_;
goto v___jp_4546_;
}
else
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_nat_dec_le(v___x_4558_, v___x_4558_);
if (v___x_4560_ == 0)
{
if (v___x_4559_ == 0)
{
v___y_4547_ = v___x_4556_;
goto v___jp_4546_;
}
else
{
size_t v___x_4561_; size_t v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((size_t)0ULL);
v___x_4562_ = lean_usize_of_nat(v___x_4558_);
v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9(v_buckets_4555_, v___x_4561_, v___x_4562_, v___x_4556_);
v___y_4547_ = v___x_4563_;
goto v___jp_4546_;
}
}
else
{
size_t v___x_4564_; size_t v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = ((size_t)0ULL);
v___x_4565_ = lean_usize_of_nat(v___x_4558_);
v___x_4566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__9(v_buckets_4555_, v___x_4564_, v___x_4565_, v___x_4556_);
v___y_4547_ = v___x_4566_;
goto v___jp_4546_;
}
}
v___jp_4447_:
{
lean_object* v___x_4452_; lean_object* v_r_4453_; size_t v_sz_4454_; size_t v___x_4455_; lean_object* v___x_4456_; 
v___x_4452_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___closed__0);
v_r_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_r_4453_, 0, v___y_4450_);
lean_ctor_set(v_r_4453_, 1, v___x_4452_);
v_sz_4454_ = lean_array_size(v___y_4451_);
v___x_4455_ = ((size_t)0ULL);
v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__2(v_rendering_4444_, v_syntaxToRendered_4445_, v___y_4449_, v___y_4448_, v___y_4451_, v_sz_4454_, v___x_4455_, v_r_4453_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v___y_4448_);
lean_dec_ref(v___y_4449_);
return v___x_4456_;
}
v___jp_4457_:
{
lean_object* v___x_4465_; 
v___x_4465_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(v___y_4460_, v___y_4463_, v___y_4458_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec(v___y_4460_);
v___y_4448_ = v___y_4459_;
v___y_4449_ = v___y_4462_;
v___y_4450_ = v___y_4461_;
v___y_4451_ = v___x_4465_;
goto v___jp_4447_;
}
v___jp_4466_:
{
uint8_t v___x_4474_; 
v___x_4474_ = lean_nat_dec_le(v___y_4473_, v___y_4469_);
if (v___x_4474_ == 0)
{
lean_dec(v___y_4469_);
lean_inc(v___y_4473_);
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4467_;
v___y_4460_ = v___y_4468_;
v___y_4461_ = v___y_4472_;
v___y_4462_ = v___y_4471_;
v___y_4463_ = v___y_4470_;
v___y_4464_ = v___y_4473_;
goto v___jp_4457_;
}
else
{
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4467_;
v___y_4460_ = v___y_4468_;
v___y_4461_ = v___y_4472_;
v___y_4462_ = v___y_4471_;
v___y_4463_ = v___y_4470_;
v___y_4464_ = v___y_4469_;
goto v___jp_4457_;
}
}
v___jp_4475_:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = lean_array_get_size(v___y_4480_);
v___x_4482_ = lean_nat_dec_eq(v___x_4481_, v___y_4479_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4483_ = lean_nat_sub(v___x_4481_, v___y_4477_);
v___x_4484_ = lean_nat_dec_le(v___y_4479_, v___x_4483_);
if (v___x_4484_ == 0)
{
lean_inc(v___x_4483_);
v___y_4467_ = v___y_4476_;
v___y_4468_ = v___x_4481_;
v___y_4469_ = v___x_4483_;
v___y_4470_ = v___y_4480_;
v___y_4471_ = v___y_4478_;
v___y_4472_ = v___y_4479_;
v___y_4473_ = v___x_4483_;
goto v___jp_4466_;
}
else
{
lean_inc(v___y_4479_);
v___y_4467_ = v___y_4476_;
v___y_4468_ = v___x_4481_;
v___y_4469_ = v___x_4483_;
v___y_4470_ = v___y_4480_;
v___y_4471_ = v___y_4478_;
v___y_4472_ = v___y_4479_;
v___y_4473_ = v___y_4479_;
goto v___jp_4466_;
}
}
else
{
v___y_4448_ = v___y_4476_;
v___y_4449_ = v___y_4478_;
v___y_4450_ = v___y_4479_;
v___y_4451_ = v___y_4480_;
goto v___jp_4447_;
}
}
v___jp_4485_:
{
lean_object* v_size_4490_; lean_object* v_buckets_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v_size_4490_ = lean_ctor_get(v_comments_4446_, 0);
v_buckets_4491_ = lean_ctor_get(v_comments_4446_, 1);
v___x_4492_ = lean_mk_empty_array_with_capacity(v_size_4490_);
v___x_4493_ = lean_array_get_size(v_buckets_4491_);
v___x_4494_ = lean_nat_dec_lt(v___y_4487_, v___x_4493_);
if (v___x_4494_ == 0)
{
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4488_;
v___y_4479_ = v___y_4487_;
v___y_4480_ = v___x_4492_;
goto v___jp_4475_;
}
else
{
uint8_t v___x_4495_; 
v___x_4495_ = lean_nat_dec_le(v___x_4493_, v___x_4493_);
if (v___x_4495_ == 0)
{
if (v___x_4494_ == 0)
{
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4488_;
v___y_4479_ = v___y_4487_;
v___y_4480_ = v___x_4492_;
goto v___jp_4475_;
}
else
{
size_t v___x_4496_; size_t v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = ((size_t)0ULL);
v___x_4497_ = lean_usize_of_nat(v___x_4493_);
v___x_4498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5(v_buckets_4491_, v___x_4496_, v___x_4497_, v___x_4492_);
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4488_;
v___y_4479_ = v___y_4487_;
v___y_4480_ = v___x_4498_;
goto v___jp_4475_;
}
}
else
{
size_t v___x_4499_; size_t v___x_4500_; lean_object* v___x_4501_; 
v___x_4499_ = ((size_t)0ULL);
v___x_4500_ = lean_usize_of_nat(v___x_4493_);
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__5(v_buckets_4491_, v___x_4499_, v___x_4500_, v___x_4492_);
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4488_;
v___y_4479_ = v___y_4487_;
v___y_4480_ = v___x_4501_;
goto v___jp_4475_;
}
}
}
v___jp_4502_:
{
lean_object* v___x_4510_; 
v___x_4510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(v___y_4504_, v___y_4508_, v___y_4507_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec(v___y_4504_);
v___y_4486_ = v___y_4503_;
v___y_4487_ = v___y_4506_;
v___y_4488_ = v___y_4505_;
v___y_4489_ = v___x_4510_;
goto v___jp_4485_;
}
v___jp_4511_:
{
uint8_t v___x_4519_; 
v___x_4519_ = lean_nat_dec_le(v___y_4518_, v___y_4517_);
if (v___x_4519_ == 0)
{
lean_dec(v___y_4517_);
lean_inc(v___y_4518_);
v___y_4503_ = v___y_4512_;
v___y_4504_ = v___y_4513_;
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4514_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4516_;
v___y_4509_ = v___y_4518_;
goto v___jp_4502_;
}
else
{
v___y_4503_ = v___y_4512_;
v___y_4504_ = v___y_4513_;
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4514_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4516_;
v___y_4509_ = v___y_4517_;
goto v___jp_4502_;
}
}
v___jp_4520_:
{
uint8_t v___x_4527_; 
v___x_4527_ = lean_nat_dec_eq(v___y_4522_, v___y_4523_);
if (v___x_4527_ == 0)
{
uint8_t v___x_4528_; 
v___x_4528_ = lean_nat_dec_le(v___y_4523_, v___y_4525_);
if (v___x_4528_ == 0)
{
lean_inc(v___y_4525_);
v___y_4512_ = v___y_4521_;
v___y_4513_ = v___y_4522_;
v___y_4514_ = v___y_4523_;
v___y_4515_ = v___y_4526_;
v___y_4516_ = v___y_4524_;
v___y_4517_ = v___y_4525_;
v___y_4518_ = v___y_4525_;
goto v___jp_4511_;
}
else
{
lean_inc(v___y_4523_);
v___y_4512_ = v___y_4521_;
v___y_4513_ = v___y_4522_;
v___y_4514_ = v___y_4523_;
v___y_4515_ = v___y_4526_;
v___y_4516_ = v___y_4524_;
v___y_4517_ = v___y_4525_;
v___y_4518_ = v___y_4523_;
goto v___jp_4511_;
}
}
else
{
lean_dec(v___y_4525_);
lean_dec(v___y_4522_);
v___y_4486_ = v___y_4521_;
v___y_4487_ = v___y_4523_;
v___y_4488_ = v___y_4526_;
v___y_4489_ = v___y_4524_;
goto v___jp_4485_;
}
}
v___jp_4529_:
{
lean_object* v___x_4537_; 
lean_inc_ref(v___y_4534_);
v___x_4537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(v___y_4532_, v___y_4534_, v___y_4531_, v___y_4536_);
lean_dec(v___y_4536_);
v___y_4521_ = v___y_4530_;
v___y_4522_ = v___y_4532_;
v___y_4523_ = v___y_4533_;
v___y_4524_ = v___y_4534_;
v___y_4525_ = v___y_4535_;
v___y_4526_ = v___x_4537_;
goto v___jp_4520_;
}
v___jp_4538_:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_nat_dec_le(v___y_4544_, v___y_4543_);
if (v___x_4545_ == 0)
{
lean_inc(v___y_4544_);
v___y_4530_ = v___y_4539_;
v___y_4531_ = v___y_4544_;
v___y_4532_ = v___y_4540_;
v___y_4533_ = v___y_4541_;
v___y_4534_ = v___y_4542_;
v___y_4535_ = v___y_4543_;
v___y_4536_ = v___y_4544_;
goto v___jp_4529_;
}
else
{
lean_inc(v___y_4543_);
v___y_4530_ = v___y_4539_;
v___y_4531_ = v___y_4544_;
v___y_4532_ = v___y_4540_;
v___y_4533_ = v___y_4541_;
v___y_4534_ = v___y_4542_;
v___y_4535_ = v___y_4543_;
v___y_4536_ = v___y_4543_;
goto v___jp_4529_;
}
}
v___jp_4546_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = lean_array_get_size(v___y_4547_);
v___x_4550_ = lean_unsigned_to_nat(1u);
v___x_4551_ = lean_nat_sub(v___x_4549_, v___x_4550_);
v___x_4552_ = lean_nat_dec_eq(v___x_4549_, v___x_4548_);
if (v___x_4552_ == 0)
{
uint8_t v___x_4553_; 
v___x_4553_ = lean_nat_dec_le(v___x_4548_, v___x_4551_);
if (v___x_4553_ == 0)
{
lean_inc(v___x_4551_);
v___y_4539_ = v___x_4550_;
v___y_4540_ = v___x_4549_;
v___y_4541_ = v___x_4548_;
v___y_4542_ = v___y_4547_;
v___y_4543_ = v___x_4551_;
v___y_4544_ = v___x_4551_;
goto v___jp_4538_;
}
else
{
v___y_4539_ = v___x_4550_;
v___y_4540_ = v___x_4549_;
v___y_4541_ = v___x_4548_;
v___y_4542_ = v___y_4547_;
v___y_4543_ = v___x_4551_;
v___y_4544_ = v___x_4548_;
goto v___jp_4538_;
}
}
else
{
lean_inc_ref(v___y_4547_);
v___y_4521_ = v___x_4550_;
v___y_4522_ = v___x_4549_;
v___y_4523_ = v___x_4548_;
v___y_4524_ = v___y_4547_;
v___y_4525_ = v___x_4551_;
v___y_4526_ = v___y_4547_;
goto v___jp_4520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments___boxed(lean_object* v_rendering_4567_, lean_object* v_syntaxToRendered_4568_, lean_object* v_comments_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments(v_rendering_4567_, v_syntaxToRendered_4568_, v_comments_4569_);
lean_dec_ref(v_comments_4569_);
lean_dec_ref(v_syntaxToRendered_4568_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3(lean_object* v_n_4571_, lean_object* v_as_4572_, lean_object* v_lo_4573_, lean_object* v_hi_4574_, lean_object* v_w_4575_, lean_object* v_hlo_4576_, lean_object* v_hhi_4577_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___redArg(v_n_4571_, v_as_4572_, v_lo_4573_, v_hi_4574_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3___boxed(lean_object* v_n_4579_, lean_object* v_as_4580_, lean_object* v_lo_4581_, lean_object* v_hi_4582_, lean_object* v_w_4583_, lean_object* v_hlo_4584_, lean_object* v_hhi_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3(v_n_4579_, v_as_4580_, v_lo_4581_, v_hi_4582_, v_w_4583_, v_hlo_4584_, v_hhi_4585_);
lean_dec(v_hi_4582_);
lean_dec(v_n_4579_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6(lean_object* v_n_4587_, lean_object* v_as_4588_, lean_object* v_lo_4589_, lean_object* v_hi_4590_, lean_object* v_w_4591_, lean_object* v_hlo_4592_, lean_object* v_hhi_4593_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___redArg(v_n_4587_, v_as_4588_, v_lo_4589_, v_hi_4590_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6___boxed(lean_object* v_n_4595_, lean_object* v_as_4596_, lean_object* v_lo_4597_, lean_object* v_hi_4598_, lean_object* v_w_4599_, lean_object* v_hlo_4600_, lean_object* v_hhi_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6(v_n_4595_, v_as_4596_, v_lo_4597_, v_hi_4598_, v_w_4599_, v_hlo_4600_, v_hhi_4601_);
lean_dec(v_hi_4598_);
lean_dec(v_n_4595_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7(lean_object* v_n_4603_, lean_object* v_as_4604_, lean_object* v_lo_4605_, lean_object* v_hi_4606_, lean_object* v_w_4607_, lean_object* v_hlo_4608_, lean_object* v_hhi_4609_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___redArg(v_n_4603_, v_as_4604_, v_lo_4605_, v_hi_4606_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7___boxed(lean_object* v_n_4611_, lean_object* v_as_4612_, lean_object* v_lo_4613_, lean_object* v_hi_4614_, lean_object* v_w_4615_, lean_object* v_hlo_4616_, lean_object* v_hhi_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7(v_n_4611_, v_as_4612_, v_lo_4613_, v_hi_4614_, v_w_4615_, v_hlo_4616_, v_hhi_4617_);
lean_dec(v_hi_4614_);
lean_dec(v_n_4611_);
return v_res_4618_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0(lean_object* v_rendering_4619_, lean_object* v_00_u03b2_4620_, lean_object* v_a_4621_, lean_object* v_x_4622_){
_start:
{
uint8_t v___x_4623_; 
v___x_4623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___redArg(v_a_4621_, v_x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0___boxed(lean_object* v_rendering_4624_, lean_object* v_00_u03b2_4625_, lean_object* v_a_4626_, lean_object* v_x_4627_){
_start:
{
uint8_t v_res_4628_; lean_object* v_r_4629_; 
v_res_4628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__0(v_rendering_4624_, v_00_u03b2_4625_, v_a_4626_, v_x_4627_);
lean_dec(v_x_4627_);
lean_dec_ref(v_a_4626_);
lean_dec_ref(v_rendering_4624_);
v_r_4629_ = lean_box(v_res_4628_);
return v_r_4629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1(lean_object* v_rendering_4630_, lean_object* v_00_u03b2_4631_, lean_object* v_data_4632_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___redArg(v_rendering_4630_, v_data_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1___boxed(lean_object* v_rendering_4634_, lean_object* v_00_u03b2_4635_, lean_object* v_data_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1(v_rendering_4634_, v_00_u03b2_4635_, v_data_4636_);
lean_dec_ref(v_rendering_4634_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2(lean_object* v_rendering_4638_, lean_object* v_snd_4639_, lean_object* v_a_4640_, lean_object* v_x_4641_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___redArg(v_snd_4639_, v_a_4640_, v_x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2___boxed(lean_object* v_rendering_4643_, lean_object* v_snd_4644_, lean_object* v_a_4645_, lean_object* v_x_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__2(v_rendering_4643_, v_snd_4644_, v_a_4645_, v_x_4646_);
lean_dec_ref(v_rendering_4643_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6(lean_object* v_n_4648_, lean_object* v_lo_4649_, lean_object* v_hi_4650_, lean_object* v_hhi_4651_, lean_object* v_pivot_4652_, lean_object* v_as_4653_, lean_object* v_i_4654_, lean_object* v_k_4655_, lean_object* v_ilo_4656_, lean_object* v_ik_4657_, lean_object* v_w_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___redArg(v_hi_4650_, v_pivot_4652_, v_as_4653_, v_i_4654_, v_k_4655_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6___boxed(lean_object* v_n_4660_, lean_object* v_lo_4661_, lean_object* v_hi_4662_, lean_object* v_hhi_4663_, lean_object* v_pivot_4664_, lean_object* v_as_4665_, lean_object* v_i_4666_, lean_object* v_k_4667_, lean_object* v_ilo_4668_, lean_object* v_ik_4669_, lean_object* v_w_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__3_spec__6(v_n_4660_, v_lo_4661_, v_hi_4662_, v_hhi_4663_, v_pivot_4664_, v_as_4665_, v_i_4666_, v_k_4667_, v_ilo_4668_, v_ik_4669_, v_w_4670_);
lean_dec_ref(v_pivot_4664_);
lean_dec(v_hi_4662_);
lean_dec(v_lo_4661_);
lean_dec(v_n_4660_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10(lean_object* v_n_4672_, lean_object* v_lo_4673_, lean_object* v_hi_4674_, lean_object* v_hhi_4675_, lean_object* v_pivot_4676_, lean_object* v_as_4677_, lean_object* v_i_4678_, lean_object* v_k_4679_, lean_object* v_ilo_4680_, lean_object* v_ik_4681_, lean_object* v_w_4682_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___redArg(v_hi_4674_, v_pivot_4676_, v_as_4677_, v_i_4678_, v_k_4679_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10___boxed(lean_object* v_n_4684_, lean_object* v_lo_4685_, lean_object* v_hi_4686_, lean_object* v_hhi_4687_, lean_object* v_pivot_4688_, lean_object* v_as_4689_, lean_object* v_i_4690_, lean_object* v_k_4691_, lean_object* v_ilo_4692_, lean_object* v_ik_4693_, lean_object* v_w_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__6_spec__10(v_n_4684_, v_lo_4685_, v_hi_4686_, v_hhi_4687_, v_pivot_4688_, v_as_4689_, v_i_4690_, v_k_4691_, v_ilo_4692_, v_ik_4693_, v_w_4694_);
lean_dec_ref(v_pivot_4688_);
lean_dec(v_hi_4686_);
lean_dec(v_lo_4685_);
lean_dec(v_n_4684_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12(lean_object* v_n_4696_, lean_object* v_lo_4697_, lean_object* v_hi_4698_, lean_object* v_hhi_4699_, lean_object* v_pivot_4700_, lean_object* v_as_4701_, lean_object* v_i_4702_, lean_object* v_k_4703_, lean_object* v_ilo_4704_, lean_object* v_ik_4705_, lean_object* v_w_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___redArg(v_hi_4698_, v_pivot_4700_, v_as_4701_, v_i_4702_, v_k_4703_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12___boxed(lean_object* v_n_4708_, lean_object* v_lo_4709_, lean_object* v_hi_4710_, lean_object* v_hhi_4711_, lean_object* v_pivot_4712_, lean_object* v_as_4713_, lean_object* v_i_4714_, lean_object* v_k_4715_, lean_object* v_ilo_4716_, lean_object* v_ik_4717_, lean_object* v_w_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__7_spec__12(v_n_4708_, v_lo_4709_, v_hi_4710_, v_hhi_4711_, v_pivot_4712_, v_as_4713_, v_i_4714_, v_k_4715_, v_ilo_4716_, v_ik_4717_, v_w_4718_);
lean_dec_ref(v_pivot_4712_);
lean_dec(v_hi_4710_);
lean_dec(v_lo_4709_);
lean_dec(v_n_4708_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2(lean_object* v_rendering_4720_, lean_object* v_00_u03b2_4721_, lean_object* v_i_4722_, lean_object* v_source_4723_, lean_object* v_target_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___redArg(v_rendering_4720_, v_i_4722_, v_source_4723_, v_target_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2___boxed(lean_object* v_rendering_4726_, lean_object* v_00_u03b2_4727_, lean_object* v_i_4728_, lean_object* v_source_4729_, lean_object* v_target_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2(v_rendering_4726_, v_00_u03b2_4727_, v_i_4728_, v_source_4729_, v_target_4730_);
lean_dec_ref(v_rendering_4726_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12(lean_object* v_00_u03b2_4732_, lean_object* v_rendering_4733_, lean_object* v_x_4734_, lean_object* v_x_4735_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___redArg(v_x_4734_, v_x_4735_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12___boxed(lean_object* v_00_u03b2_4737_, lean_object* v_rendering_4738_, lean_object* v_x_4739_, lean_object* v_x_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments_spec__0_spec__1_spec__2_spec__12(v_00_u03b2_4737_, v_rendering_4738_, v_x_4739_, v_x_4740_);
lean_dec_ref(v_rendering_4738_);
return v_res_4741_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg(lean_object* v_a_4742_, lean_object* v_b_4743_){
_start:
{
lean_object* v_startInclusive_4744_; lean_object* v_endExclusive_4745_; lean_object* v_startInclusive_4746_; lean_object* v_endExclusive_4747_; uint8_t v___x_4748_; 
v_startInclusive_4744_ = lean_ctor_get(v_a_4742_, 0);
v_endExclusive_4745_ = lean_ctor_get(v_a_4742_, 1);
v_startInclusive_4746_ = lean_ctor_get(v_b_4743_, 0);
v_endExclusive_4747_ = lean_ctor_get(v_b_4743_, 1);
v___x_4748_ = l_instOrdPos__lean_ord___redArg(v_startInclusive_4744_, v_startInclusive_4746_);
if (v___x_4748_ == 1)
{
uint8_t v___x_4749_; 
v___x_4749_ = l_instOrdPos__lean_ord___redArg(v_endExclusive_4747_, v_endExclusive_4745_);
return v___x_4749_;
}
else
{
return v___x_4748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg___boxed(lean_object* v_a_4750_, lean_object* v_b_4751_){
_start:
{
uint8_t v_res_4752_; lean_object* v_r_4753_; 
v_res_4752_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg(v_a_4750_, v_b_4751_);
lean_dec_ref(v_b_4751_);
lean_dec_ref(v_a_4750_);
v_r_4753_ = lean_box(v_res_4752_);
return v_r_4753_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest(lean_object* v_s_4754_, lean_object* v_a_4755_, lean_object* v_b_4756_){
_start:
{
uint8_t v___x_4757_; 
v___x_4757_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg(v_a_4755_, v_b_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___boxed(lean_object* v_s_4758_, lean_object* v_a_4759_, lean_object* v_b_4760_){
_start:
{
uint8_t v_res_4761_; lean_object* v_r_4762_; 
v_res_4761_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest(v_s_4758_, v_a_4759_, v_b_4760_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
lean_dec_ref(v_s_4758_);
v_r_4762_ = lean_box(v_res_4761_);
return v_r_4762_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining_spec__0(lean_object* v_rendering_4763_, lean_object* v_msg_4764_){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4765_ = lean_unsigned_to_nat(0u);
v___x_4766_ = l_Lean_Fmt_instInhabitedLineInfo_default(v_rendering_4763_);
v___x_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = lean_panic_fn_borrowed(v___x_4767_, v_msg_4764_);
lean_dec_ref_known(v___x_4767_, 2);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0(lean_object* v_x_4769_){
_start:
{
lean_object* v_range_4770_; lean_object* v_startInclusive_4771_; 
v_range_4770_ = lean_ctor_get(v_x_4769_, 2);
v_startInclusive_4771_ = lean_ctor_get(v_range_4770_, 0);
lean_inc(v_startInclusive_4771_);
return v_startInclusive_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0___boxed(lean_object* v_x_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___lam__0(v_x_4772_);
lean_dec_ref(v_x_4772_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(lean_object* v_rendering_4775_, lean_object* v_lineInfos_4776_, lean_object* v_pos_4777_){
_start:
{
lean_object* v___f_4778_; lean_object* v___f_4779_; lean_object* v___x_4780_; 
v___f_4778_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___closed__0));
v___f_4779_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryOpenComment___closed__1));
v___x_4780_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4776_, v_pos_4777_, v___f_4778_, v___f_4779_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
v___x_4782_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining_spec__0(v_rendering_4775_, v___x_4781_);
return v___x_4782_;
}
else
{
lean_object* v_val_4783_; 
lean_dec_ref(v_rendering_4775_);
v_val_4783_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_val_4783_);
lean_dec_ref_known(v___x_4780_, 1);
return v_val_4783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining___boxed(lean_object* v_rendering_4784_, lean_object* v_lineInfos_4785_, lean_object* v_pos_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(v_rendering_4784_, v_lineInfos_4785_, v_pos_4786_);
lean_dec_ref(v_lineInfos_4785_);
return v_res_4787_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7(void){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Array_instInhabited(lean_box(0));
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7(lean_object* v_rendering_4796_, lean_object* v_msg_4797_){
_start:
{
lean_object* v___f_4798_; lean_object* v___f_4799_; lean_object* v___f_4800_; lean_object* v___f_4801_; lean_object* v___f_4802_; lean_object* v___f_4803_; lean_object* v___f_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___f_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___f_4798_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__0));
v___f_4799_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__1));
v___f_4800_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__2));
v___f_4801_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__3));
v___f_4802_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__4));
v___f_4803_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__5));
v___f_4804_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__6));
v___x_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___f_4798_);
lean_ctor_set(v___x_4805_, 1, v___f_4799_);
v___x_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
lean_ctor_set(v___x_4806_, 1, v___f_4800_);
lean_ctor_set(v___x_4806_, 2, v___f_4801_);
lean_ctor_set(v___x_4806_, 3, v___f_4802_);
lean_ctor_set(v___x_4806_, 4, v___f_4803_);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
lean_ctor_set(v___x_4807_, 1, v___f_4804_);
v___x_4808_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7, &l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7___closed__7);
lean_inc_ref(v_rendering_4796_);
v___x_4809_ = lean_alloc_closure((void*)(l_String_Slice_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_4809_, 0, v_rendering_4796_);
v___f_4810_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4810_, 0, v___x_4809_);
v___x_4811_ = lean_alloc_closure((void*)(l_instHashablePos__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_4811_, 0, v_rendering_4796_);
v___x_4812_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_4810_, v___x_4811_);
lean_dec_ref(v___x_4811_);
lean_dec_ref(v___f_4810_);
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4808_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
v___x_4814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4808_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
v___x_4816_ = l_instInhabitedOfMonad___redArg(v___x_4807_, v___x_4815_);
v___x_4817_ = lean_panic_fn_borrowed(v___x_4816_, v_msg_4797_);
lean_dec(v___x_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(lean_object* v_x1_4818_, lean_object* v_x2_4819_){
_start:
{
lean_object* v_fst_4820_; lean_object* v_fst_4821_; uint8_t v___x_4822_; 
v_fst_4820_ = lean_ctor_get(v_x1_4818_, 0);
v_fst_4821_ = lean_ctor_get(v_x2_4819_, 0);
v___x_4822_ = lean_nat_dec_lt(v_fst_4820_, v_fst_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0___boxed(lean_object* v_x1_4823_, lean_object* v_x2_4824_){
_start:
{
uint8_t v_res_4825_; lean_object* v_r_4826_; 
v_res_4825_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(v_x1_4823_, v_x2_4824_);
lean_dec_ref(v_x2_4824_);
lean_dec_ref(v_x1_4823_);
v_r_4826_ = lean_box(v_res_4825_);
return v_r_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg(lean_object* v_hi_4827_, lean_object* v_pivot_4828_, lean_object* v_as_4829_, lean_object* v_i_4830_, lean_object* v_k_4831_){
_start:
{
uint8_t v___x_4832_; 
v___x_4832_ = lean_nat_dec_lt(v_k_4831_, v_hi_4827_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
lean_dec(v_k_4831_);
v___x_4833_ = lean_array_fswap(v_as_4829_, v_i_4830_, v_hi_4827_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v_i_4830_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
return v___x_4834_;
}
else
{
lean_object* v___x_4835_; lean_object* v_fst_4836_; lean_object* v_fst_4837_; uint8_t v___x_4838_; 
v___x_4835_ = lean_array_fget_borrowed(v_as_4829_, v_k_4831_);
v_fst_4836_ = lean_ctor_get(v___x_4835_, 0);
v_fst_4837_ = lean_ctor_get(v_pivot_4828_, 0);
v___x_4838_ = lean_nat_dec_lt(v_fst_4836_, v_fst_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = lean_unsigned_to_nat(1u);
v___x_4840_ = lean_nat_add(v_k_4831_, v___x_4839_);
lean_dec(v_k_4831_);
v_k_4831_ = v___x_4840_;
goto _start;
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4842_ = lean_array_fswap(v_as_4829_, v_i_4830_, v_k_4831_);
v___x_4843_ = lean_unsigned_to_nat(1u);
v___x_4844_ = lean_nat_add(v_i_4830_, v___x_4843_);
lean_dec(v_i_4830_);
v___x_4845_ = lean_nat_add(v_k_4831_, v___x_4843_);
lean_dec(v_k_4831_);
v_as_4829_ = v___x_4842_;
v_i_4830_ = v___x_4844_;
v_k_4831_ = v___x_4845_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg___boxed(lean_object* v_hi_4847_, lean_object* v_pivot_4848_, lean_object* v_as_4849_, lean_object* v_i_4850_, lean_object* v_k_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg(v_hi_4847_, v_pivot_4848_, v_as_4849_, v_i_4850_, v_k_4851_);
lean_dec_ref(v_pivot_4848_);
lean_dec(v_hi_4847_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(lean_object* v_rendering_4853_, lean_object* v_n_4854_, lean_object* v_as_4855_, lean_object* v_lo_4856_, lean_object* v_hi_4857_){
_start:
{
lean_object* v___y_4859_; uint8_t v___x_4869_; 
v___x_4869_ = lean_nat_dec_lt(v_lo_4856_, v_hi_4857_);
if (v___x_4869_ == 0)
{
lean_dec(v_lo_4856_);
return v_as_4855_;
}
else
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v_mid_4872_; lean_object* v___y_4874_; lean_object* v___y_4880_; lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4870_ = lean_nat_add(v_lo_4856_, v_hi_4857_);
v___x_4871_ = lean_unsigned_to_nat(1u);
v_mid_4872_ = lean_nat_shiftr(v___x_4870_, v___x_4871_);
lean_dec(v___x_4870_);
v___x_4885_ = lean_array_fget_borrowed(v_as_4855_, v_mid_4872_);
v___x_4886_ = lean_array_fget_borrowed(v_as_4855_, v_lo_4856_);
v___x_4887_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(v___x_4885_, v___x_4886_);
if (v___x_4887_ == 0)
{
v___y_4880_ = v_as_4855_;
goto v___jp_4879_;
}
else
{
lean_object* v___x_4888_; 
v___x_4888_ = lean_array_fswap(v_as_4855_, v_lo_4856_, v_mid_4872_);
v___y_4880_ = v___x_4888_;
goto v___jp_4879_;
}
v___jp_4873_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; uint8_t v___x_4877_; 
v___x_4875_ = lean_array_fget_borrowed(v___y_4874_, v_mid_4872_);
v___x_4876_ = lean_array_fget_borrowed(v___y_4874_, v_hi_4857_);
v___x_4877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(v___x_4875_, v___x_4876_);
if (v___x_4877_ == 0)
{
lean_dec(v_mid_4872_);
v___y_4859_ = v___y_4874_;
goto v___jp_4858_;
}
else
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_array_fswap(v___y_4874_, v_mid_4872_, v_hi_4857_);
lean_dec(v_mid_4872_);
v___y_4859_ = v___x_4878_;
goto v___jp_4858_;
}
}
v___jp_4879_:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4881_ = lean_array_fget_borrowed(v___y_4880_, v_hi_4857_);
v___x_4882_ = lean_array_fget_borrowed(v___y_4880_, v_lo_4856_);
v___x_4883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___lam__0(v___x_4881_, v___x_4882_);
if (v___x_4883_ == 0)
{
v___y_4874_ = v___y_4880_;
goto v___jp_4873_;
}
else
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_array_fswap(v___y_4880_, v_lo_4856_, v_hi_4857_);
v___y_4874_ = v___x_4884_;
goto v___jp_4873_;
}
}
}
v___jp_4858_:
{
lean_object* v_pivot_4860_; lean_object* v___x_4861_; lean_object* v_fst_4862_; lean_object* v_snd_4863_; uint8_t v___x_4864_; 
v_pivot_4860_ = lean_array_fget(v___y_4859_, v_hi_4857_);
lean_inc_n(v_lo_4856_, 2);
v___x_4861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg(v_hi_4857_, v_pivot_4860_, v___y_4859_, v_lo_4856_, v_lo_4856_);
lean_dec(v_pivot_4860_);
v_fst_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_fst_4862_);
v_snd_4863_ = lean_ctor_get(v___x_4861_, 1);
lean_inc(v_snd_4863_);
lean_dec_ref(v___x_4861_);
v___x_4864_ = lean_nat_dec_le(v_hi_4857_, v_fst_4862_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(v_rendering_4853_, v_n_4854_, v_snd_4863_, v_lo_4856_, v_fst_4862_);
v___x_4866_ = lean_unsigned_to_nat(1u);
v___x_4867_ = lean_nat_add(v_fst_4862_, v___x_4866_);
lean_dec(v_fst_4862_);
v_as_4855_ = v___x_4865_;
v_lo_4856_ = v___x_4867_;
goto _start;
}
else
{
lean_dec(v_fst_4862_);
lean_dec(v_lo_4856_);
return v_snd_4863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg___boxed(lean_object* v_rendering_4889_, lean_object* v_n_4890_, lean_object* v_as_4891_, lean_object* v_lo_4892_, lean_object* v_hi_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(v_rendering_4889_, v_n_4890_, v_as_4891_, v_lo_4892_, v_hi_4893_);
lean_dec(v_hi_4893_);
lean_dec(v_n_4890_);
lean_dec_ref(v_rendering_4889_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1(lean_object* v_x_4895_, lean_object* v_x_4896_){
_start:
{
if (lean_obj_tag(v_x_4896_) == 0)
{
return v_x_4895_;
}
else
{
lean_object* v_key_4897_; lean_object* v_value_4898_; lean_object* v_tail_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
v_key_4897_ = lean_ctor_get(v_x_4896_, 0);
v_value_4898_ = lean_ctor_get(v_x_4896_, 1);
v_tail_4899_ = lean_ctor_get(v_x_4896_, 2);
lean_inc(v_value_4898_);
lean_inc(v_key_4897_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v_key_4897_);
lean_ctor_set(v___x_4900_, 1, v_value_4898_);
v___x_4901_ = lean_array_push(v_x_4895_, v___x_4900_);
v_x_4895_ = v___x_4901_;
v_x_4896_ = v_tail_4899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1___boxed(lean_object* v_x_4903_, lean_object* v_x_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1(v_x_4903_, v_x_4904_);
lean_dec(v_x_4904_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2(lean_object* v_as_4906_, size_t v_i_4907_, size_t v_stop_4908_, lean_object* v_b_4909_){
_start:
{
uint8_t v___x_4910_; 
v___x_4910_ = lean_usize_dec_eq(v_i_4907_, v_stop_4908_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; 
v___x_4911_ = lean_array_uget_borrowed(v_as_4906_, v_i_4907_);
v___x_4912_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__1(v_b_4909_, v___x_4911_);
v___x_4913_ = ((size_t)1ULL);
v___x_4914_ = lean_usize_add(v_i_4907_, v___x_4913_);
v_i_4907_ = v___x_4914_;
v_b_4909_ = v___x_4912_;
goto _start;
}
else
{
return v_b_4909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2___boxed(lean_object* v_as_4916_, lean_object* v_i_4917_, lean_object* v_stop_4918_, lean_object* v_b_4919_){
_start:
{
size_t v_i_boxed_4920_; size_t v_stop_boxed_4921_; lean_object* v_res_4922_; 
v_i_boxed_4920_ = lean_unbox_usize(v_i_4917_);
lean_dec(v_i_4917_);
v_stop_boxed_4921_ = lean_unbox_usize(v_stop_4918_);
lean_dec(v_stop_4918_);
v_res_4922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2(v_as_4916_, v_i_boxed_4920_, v_stop_boxed_4921_, v_b_4919_);
lean_dec_ref(v_as_4916_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14(lean_object* v_x_4923_, lean_object* v_x_4924_){
_start:
{
if (lean_obj_tag(v_x_4924_) == 0)
{
return v_x_4923_;
}
else
{
lean_object* v_key_4925_; lean_object* v_value_4926_; lean_object* v_tail_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_key_4925_ = lean_ctor_get(v_x_4924_, 0);
v_value_4926_ = lean_ctor_get(v_x_4924_, 1);
v_tail_4927_ = lean_ctor_get(v_x_4924_, 2);
lean_inc(v_value_4926_);
lean_inc(v_key_4925_);
v___x_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4928_, 0, v_key_4925_);
lean_ctor_set(v___x_4928_, 1, v_value_4926_);
v___x_4929_ = lean_array_push(v_x_4923_, v___x_4928_);
v_x_4923_ = v___x_4929_;
v_x_4924_ = v_tail_4927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14___boxed(lean_object* v_x_4931_, lean_object* v_x_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14(v_x_4931_, v_x_4932_);
lean_dec(v_x_4932_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15(lean_object* v_as_4934_, size_t v_i_4935_, size_t v_stop_4936_, lean_object* v_b_4937_){
_start:
{
uint8_t v___x_4938_; 
v___x_4938_ = lean_usize_dec_eq(v_i_4935_, v_stop_4936_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; size_t v___x_4941_; size_t v___x_4942_; 
v___x_4939_ = lean_array_uget_borrowed(v_as_4934_, v_i_4935_);
v___x_4940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__14(v_b_4937_, v___x_4939_);
v___x_4941_ = ((size_t)1ULL);
v___x_4942_ = lean_usize_add(v_i_4935_, v___x_4941_);
v_i_4935_ = v___x_4942_;
v_b_4937_ = v___x_4940_;
goto _start;
}
else
{
return v_b_4937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15___boxed(lean_object* v_as_4944_, lean_object* v_i_4945_, lean_object* v_stop_4946_, lean_object* v_b_4947_){
_start:
{
size_t v_i_boxed_4948_; size_t v_stop_boxed_4949_; lean_object* v_res_4950_; 
v_i_boxed_4948_ = lean_unbox_usize(v_i_4945_);
lean_dec(v_i_4945_);
v_stop_boxed_4949_ = lean_unbox_usize(v_stop_4946_);
lean_dec(v_stop_4946_);
v_res_4950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15(v_as_4944_, v_i_boxed_4948_, v_stop_boxed_4949_, v_b_4947_);
lean_dec_ref(v_as_4944_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___redArg(lean_object* v_x_4951_, lean_object* v_x_4952_){
_start:
{
if (lean_obj_tag(v_x_4952_) == 0)
{
return v_x_4951_;
}
else
{
lean_object* v_key_4953_; lean_object* v_value_4954_; lean_object* v_tail_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4978_; 
v_key_4953_ = lean_ctor_get(v_x_4952_, 0);
v_value_4954_ = lean_ctor_get(v_x_4952_, 1);
v_tail_4955_ = lean_ctor_get(v_x_4952_, 2);
v_isSharedCheck_4978_ = !lean_is_exclusive(v_x_4952_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4957_ = v_x_4952_;
v_isShared_4958_ = v_isSharedCheck_4978_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_tail_4955_);
lean_inc(v_value_4954_);
lean_inc(v_key_4953_);
lean_dec(v_x_4952_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4978_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; uint64_t v___x_4960_; uint64_t v___x_4961_; uint64_t v___x_4962_; uint64_t v_fold_4963_; uint64_t v___x_4964_; uint64_t v___x_4965_; uint64_t v___x_4966_; size_t v___x_4967_; size_t v___x_4968_; size_t v___x_4969_; size_t v___x_4970_; size_t v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4974_; 
v___x_4959_ = lean_array_get_size(v_x_4951_);
v___x_4960_ = l_instHashablePos__lean_hash___redArg(v_key_4953_);
v___x_4961_ = 32ULL;
v___x_4962_ = lean_uint64_shift_right(v___x_4960_, v___x_4961_);
v_fold_4963_ = lean_uint64_xor(v___x_4960_, v___x_4962_);
v___x_4964_ = 16ULL;
v___x_4965_ = lean_uint64_shift_right(v_fold_4963_, v___x_4964_);
v___x_4966_ = lean_uint64_xor(v_fold_4963_, v___x_4965_);
v___x_4967_ = lean_uint64_to_usize(v___x_4966_);
v___x_4968_ = lean_usize_of_nat(v___x_4959_);
v___x_4969_ = ((size_t)1ULL);
v___x_4970_ = lean_usize_sub(v___x_4968_, v___x_4969_);
v___x_4971_ = lean_usize_land(v___x_4967_, v___x_4970_);
v___x_4972_ = lean_array_uget_borrowed(v_x_4951_, v___x_4971_);
lean_inc(v___x_4972_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 2, v___x_4972_);
v___x_4974_ = v___x_4957_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_key_4953_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v_value_4954_);
lean_ctor_set(v_reuseFailAlloc_4977_, 2, v___x_4972_);
v___x_4974_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
lean_object* v___x_4975_; 
v___x_4975_ = lean_array_uset(v_x_4951_, v___x_4971_, v___x_4974_);
v_x_4951_ = v___x_4975_;
v_x_4952_ = v_tail_4955_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg(lean_object* v_rendering_4979_, lean_object* v_i_4980_, lean_object* v_source_4981_, lean_object* v_target_4982_){
_start:
{
lean_object* v___x_4983_; uint8_t v___x_4984_; 
v___x_4983_ = lean_array_get_size(v_source_4981_);
v___x_4984_ = lean_nat_dec_lt(v_i_4980_, v___x_4983_);
if (v___x_4984_ == 0)
{
lean_dec_ref(v_source_4981_);
lean_dec(v_i_4980_);
return v_target_4982_;
}
else
{
lean_object* v_es_4985_; lean_object* v___x_4986_; lean_object* v_source_4987_; lean_object* v_target_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_es_4985_ = lean_array_fget(v_source_4981_, v_i_4980_);
v___x_4986_ = lean_box(0);
v_source_4987_ = lean_array_fset(v_source_4981_, v_i_4980_, v___x_4986_);
v_target_4988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___redArg(v_target_4982_, v_es_4985_);
v___x_4989_ = lean_unsigned_to_nat(1u);
v___x_4990_ = lean_nat_add(v_i_4980_, v___x_4989_);
lean_dec(v_i_4980_);
v_i_4980_ = v___x_4990_;
v_source_4981_ = v_source_4987_;
v_target_4982_ = v_target_4988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_rendering_4992_, lean_object* v_i_4993_, lean_object* v_source_4994_, lean_object* v_target_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg(v_rendering_4992_, v_i_4993_, v_source_4994_, v_target_4995_);
lean_dec_ref(v_rendering_4992_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(lean_object* v_rendering_4997_, lean_object* v_data_4998_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v_nbuckets_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_4999_ = lean_array_get_size(v_data_4998_);
v___x_5000_ = lean_unsigned_to_nat(2u);
v_nbuckets_5001_ = lean_nat_mul(v___x_4999_, v___x_5000_);
v___x_5002_ = lean_unsigned_to_nat(0u);
v___x_5003_ = lean_box(0);
v___x_5004_ = lean_mk_array(v_nbuckets_5001_, v___x_5003_);
v___x_5005_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg(v_rendering_4997_, v___x_5002_, v_data_4998_, v___x_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg___boxed(lean_object* v_rendering_5006_, lean_object* v_data_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(v_rendering_5006_, v_data_5007_);
lean_dec_ref(v_rendering_5006_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___redArg(lean_object* v_a_5009_, lean_object* v_b_5010_, lean_object* v_x_5011_){
_start:
{
if (lean_obj_tag(v_x_5011_) == 0)
{
lean_dec(v_b_5010_);
lean_dec(v_a_5009_);
return v_x_5011_;
}
else
{
lean_object* v_key_5012_; lean_object* v_value_5013_; lean_object* v_tail_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5026_; 
v_key_5012_ = lean_ctor_get(v_x_5011_, 0);
v_value_5013_ = lean_ctor_get(v_x_5011_, 1);
v_tail_5014_ = lean_ctor_get(v_x_5011_, 2);
v_isSharedCheck_5026_ = !lean_is_exclusive(v_x_5011_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5016_ = v_x_5011_;
v_isShared_5017_ = v_isSharedCheck_5026_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_tail_5014_);
lean_inc(v_value_5013_);
lean_inc(v_key_5012_);
lean_dec(v_x_5011_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5026_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
uint8_t v___x_5018_; 
v___x_5018_ = lean_nat_dec_eq(v_key_5012_, v_a_5009_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___redArg(v_a_5009_, v_b_5010_, v_tail_5014_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 2, v___x_5019_);
v___x_5021_ = v___x_5016_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_key_5012_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_value_5013_);
lean_ctor_set(v_reuseFailAlloc_5022_, 2, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
else
{
lean_object* v___x_5024_; 
lean_dec(v_value_5013_);
lean_dec(v_key_5012_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 1, v_b_5010_);
lean_ctor_set(v___x_5016_, 0, v_a_5009_);
v___x_5024_ = v___x_5016_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5009_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_b_5010_);
lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_tail_5014_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(lean_object* v_a_5027_, lean_object* v_x_5028_){
_start:
{
if (lean_obj_tag(v_x_5028_) == 0)
{
uint8_t v___x_5029_; 
v___x_5029_ = 0;
return v___x_5029_;
}
else
{
lean_object* v_key_5030_; lean_object* v_tail_5031_; uint8_t v___x_5032_; 
v_key_5030_ = lean_ctor_get(v_x_5028_, 0);
v_tail_5031_ = lean_ctor_get(v_x_5028_, 2);
v___x_5032_ = lean_nat_dec_eq(v_key_5030_, v_a_5027_);
if (v___x_5032_ == 0)
{
v_x_5028_ = v_tail_5031_;
goto _start;
}
else
{
return v___x_5032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg___boxed(lean_object* v_a_5034_, lean_object* v_x_5035_){
_start:
{
uint8_t v_res_5036_; lean_object* v_r_5037_; 
v_res_5036_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_5034_, v_x_5035_);
lean_dec(v_x_5035_);
lean_dec(v_a_5034_);
v_r_5037_ = lean_box(v_res_5036_);
return v_r_5037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg(lean_object* v_rendering_5038_, lean_object* v_m_5039_, lean_object* v_a_5040_, lean_object* v_b_5041_){
_start:
{
lean_object* v_size_5042_; lean_object* v_buckets_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5086_; 
v_size_5042_ = lean_ctor_get(v_m_5039_, 0);
v_buckets_5043_ = lean_ctor_get(v_m_5039_, 1);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_m_5039_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5045_ = v_m_5039_;
v_isShared_5046_ = v_isSharedCheck_5086_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_buckets_5043_);
lean_inc(v_size_5042_);
lean_dec(v_m_5039_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5086_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5047_; uint64_t v___x_5048_; uint64_t v___x_5049_; uint64_t v___x_5050_; uint64_t v_fold_5051_; uint64_t v___x_5052_; uint64_t v___x_5053_; uint64_t v___x_5054_; size_t v___x_5055_; size_t v___x_5056_; size_t v___x_5057_; size_t v___x_5058_; size_t v___x_5059_; lean_object* v_bkt_5060_; uint8_t v___x_5061_; 
v___x_5047_ = lean_array_get_size(v_buckets_5043_);
v___x_5048_ = l_instHashablePos__lean_hash___redArg(v_a_5040_);
v___x_5049_ = 32ULL;
v___x_5050_ = lean_uint64_shift_right(v___x_5048_, v___x_5049_);
v_fold_5051_ = lean_uint64_xor(v___x_5048_, v___x_5050_);
v___x_5052_ = 16ULL;
v___x_5053_ = lean_uint64_shift_right(v_fold_5051_, v___x_5052_);
v___x_5054_ = lean_uint64_xor(v_fold_5051_, v___x_5053_);
v___x_5055_ = lean_uint64_to_usize(v___x_5054_);
v___x_5056_ = lean_usize_of_nat(v___x_5047_);
v___x_5057_ = ((size_t)1ULL);
v___x_5058_ = lean_usize_sub(v___x_5056_, v___x_5057_);
v___x_5059_ = lean_usize_land(v___x_5055_, v___x_5058_);
v_bkt_5060_ = lean_array_uget_borrowed(v_buckets_5043_, v___x_5059_);
v___x_5061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_5040_, v_bkt_5060_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; lean_object* v_size_x27_5063_; lean_object* v___x_5064_; lean_object* v_buckets_x27_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5062_ = lean_unsigned_to_nat(1u);
v_size_x27_5063_ = lean_nat_add(v_size_5042_, v___x_5062_);
lean_dec(v_size_5042_);
lean_inc(v_bkt_5060_);
v___x_5064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5064_, 0, v_a_5040_);
lean_ctor_set(v___x_5064_, 1, v_b_5041_);
lean_ctor_set(v___x_5064_, 2, v_bkt_5060_);
v_buckets_x27_5065_ = lean_array_uset(v_buckets_5043_, v___x_5059_, v___x_5064_);
v___x_5066_ = lean_unsigned_to_nat(4u);
v___x_5067_ = lean_nat_mul(v_size_x27_5063_, v___x_5066_);
v___x_5068_ = lean_unsigned_to_nat(3u);
v___x_5069_ = lean_nat_div(v___x_5067_, v___x_5068_);
lean_dec(v___x_5067_);
v___x_5070_ = lean_array_get_size(v_buckets_x27_5065_);
v___x_5071_ = lean_nat_dec_le(v___x_5069_, v___x_5070_);
lean_dec(v___x_5069_);
if (v___x_5071_ == 0)
{
lean_object* v_val_5072_; lean_object* v___x_5074_; 
v_val_5072_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(v_rendering_5038_, v_buckets_x27_5065_);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 1, v_val_5072_);
lean_ctor_set(v___x_5045_, 0, v_size_x27_5063_);
v___x_5074_ = v___x_5045_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_size_x27_5063_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_val_5072_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
else
{
lean_object* v___x_5077_; 
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 1, v_buckets_x27_5065_);
lean_ctor_set(v___x_5045_, 0, v_size_x27_5063_);
v___x_5077_ = v___x_5045_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_size_x27_5063_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v_buckets_x27_5065_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
else
{
lean_object* v___x_5079_; lean_object* v_buckets_x27_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; 
lean_inc(v_bkt_5060_);
v___x_5079_ = lean_box(0);
v_buckets_x27_5080_ = lean_array_uset(v_buckets_5043_, v___x_5059_, v___x_5079_);
v___x_5081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___redArg(v_a_5040_, v_b_5041_, v_bkt_5060_);
v___x_5082_ = lean_array_uset(v_buckets_x27_5080_, v___x_5059_, v___x_5081_);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 1, v___x_5082_);
v___x_5084_ = v___x_5045_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_size_5042_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg___boxed(lean_object* v_rendering_5087_, lean_object* v_m_5088_, lean_object* v_a_5089_, lean_object* v_b_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg(v_rendering_5087_, v_m_5088_, v_a_5089_, v_b_5090_);
lean_dec_ref(v_rendering_5087_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg___lam__0(lean_object* v___x_5092_, lean_object* v_x_5093_){
_start:
{
if (lean_obj_tag(v_x_5093_) == 0)
{
lean_object* v___x_5094_; 
v___x_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5092_);
return v___x_5094_;
}
else
{
lean_object* v_val_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5103_; 
v_val_5095_ = lean_ctor_get(v_x_5093_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_x_5093_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5097_ = v_x_5093_;
v_isShared_5098_ = v_isSharedCheck_5103_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_val_5095_);
lean_dec(v_x_5093_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5103_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5099_ = lean_string_append(v___x_5092_, v_val_5095_);
lean_dec(v_val_5095_);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5099_);
v___x_5101_ = v___x_5097_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg(lean_object* v___x_5104_, lean_object* v_a_5105_, lean_object* v_x_5106_){
_start:
{
if (lean_obj_tag(v_x_5106_) == 0)
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v_val_5109_; lean_object* v___x_5110_; 
v___x_5107_ = lean_box(0);
v___x_5108_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg___lam__0(v___x_5104_, v___x_5107_);
v_val_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_val_5109_);
lean_dec(v___x_5108_);
v___x_5110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5110_, 0, v_a_5105_);
lean_ctor_set(v___x_5110_, 1, v_val_5109_);
lean_ctor_set(v___x_5110_, 2, v_x_5106_);
return v___x_5110_;
}
else
{
lean_object* v_key_5111_; lean_object* v_value_5112_; lean_object* v_tail_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5128_; 
v_key_5111_ = lean_ctor_get(v_x_5106_, 0);
v_value_5112_ = lean_ctor_get(v_x_5106_, 1);
v_tail_5113_ = lean_ctor_get(v_x_5106_, 2);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_x_5106_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5115_ = v_x_5106_;
v_isShared_5116_ = v_isSharedCheck_5128_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_tail_5113_);
lean_inc(v_value_5112_);
lean_inc(v_key_5111_);
lean_dec(v_x_5106_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5128_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
uint8_t v___x_5117_; 
v___x_5117_ = lean_nat_dec_eq(v_key_5111_, v_a_5105_);
if (v___x_5117_ == 0)
{
lean_object* v_tail_5118_; lean_object* v___x_5120_; 
v_tail_5118_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg(v___x_5104_, v_a_5105_, v_tail_5113_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 2, v_tail_5118_);
v___x_5120_ = v___x_5115_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_key_5111_);
lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_value_5112_);
lean_ctor_set(v_reuseFailAlloc_5121_, 2, v_tail_5118_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v_val_5124_; lean_object* v___x_5126_; 
lean_dec(v_key_5111_);
v___x_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5122_, 0, v_value_5112_);
v___x_5123_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg___lam__0(v___x_5104_, v___x_5122_);
v_val_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_val_5124_);
lean_dec(v___x_5123_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 1, v_val_5124_);
lean_ctor_set(v___x_5115_, 0, v_a_5105_);
v___x_5126_ = v___x_5115_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5105_);
lean_ctor_set(v_reuseFailAlloc_5127_, 1, v_val_5124_);
lean_ctor_set(v_reuseFailAlloc_5127_, 2, v_tail_5113_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8(lean_object* v_rendering_5129_, lean_object* v___x_5130_, lean_object* v_m_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v_size_5133_; lean_object* v_buckets_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5182_; 
v_size_5133_ = lean_ctor_get(v_m_5131_, 0);
v_buckets_5134_ = lean_ctor_get(v_m_5131_, 1);
v_isSharedCheck_5182_ = !lean_is_exclusive(v_m_5131_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5136_ = v_m_5131_;
v_isShared_5137_ = v_isSharedCheck_5182_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_buckets_5134_);
lean_inc(v_size_5133_);
lean_dec(v_m_5131_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5182_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; uint64_t v___x_5139_; uint64_t v___x_5140_; uint64_t v___x_5141_; uint64_t v_fold_5142_; uint64_t v___x_5143_; uint64_t v___x_5144_; uint64_t v___x_5145_; size_t v___x_5146_; size_t v___x_5147_; size_t v___x_5148_; size_t v___x_5149_; size_t v___x_5150_; lean_object* v_bkt_5151_; uint8_t v___x_5152_; 
v___x_5138_ = lean_array_get_size(v_buckets_5134_);
v___x_5139_ = l_instHashablePos__lean_hash___redArg(v_a_5132_);
v___x_5140_ = 32ULL;
v___x_5141_ = lean_uint64_shift_right(v___x_5139_, v___x_5140_);
v_fold_5142_ = lean_uint64_xor(v___x_5139_, v___x_5141_);
v___x_5143_ = 16ULL;
v___x_5144_ = lean_uint64_shift_right(v_fold_5142_, v___x_5143_);
v___x_5145_ = lean_uint64_xor(v_fold_5142_, v___x_5144_);
v___x_5146_ = lean_uint64_to_usize(v___x_5145_);
v___x_5147_ = lean_usize_of_nat(v___x_5138_);
v___x_5148_ = ((size_t)1ULL);
v___x_5149_ = lean_usize_sub(v___x_5147_, v___x_5148_);
v___x_5150_ = lean_usize_land(v___x_5146_, v___x_5149_);
v_bkt_5151_ = lean_array_uget_borrowed(v_buckets_5134_, v___x_5150_);
v___x_5152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_5132_, v_bkt_5151_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; lean_object* v_size_x27_5154_; lean_object* v___x_5155_; lean_object* v_buckets_x27_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; 
v___x_5153_ = lean_unsigned_to_nat(1u);
v_size_x27_5154_ = lean_nat_add(v_size_5133_, v___x_5153_);
lean_dec(v_size_5133_);
lean_inc(v_bkt_5151_);
v___x_5155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5155_, 0, v_a_5132_);
lean_ctor_set(v___x_5155_, 1, v___x_5130_);
lean_ctor_set(v___x_5155_, 2, v_bkt_5151_);
v_buckets_x27_5156_ = lean_array_uset(v_buckets_5134_, v___x_5150_, v___x_5155_);
v___x_5157_ = lean_unsigned_to_nat(4u);
v___x_5158_ = lean_nat_mul(v_size_x27_5154_, v___x_5157_);
v___x_5159_ = lean_unsigned_to_nat(3u);
v___x_5160_ = lean_nat_div(v___x_5158_, v___x_5159_);
lean_dec(v___x_5158_);
v___x_5161_ = lean_array_get_size(v_buckets_x27_5156_);
v___x_5162_ = lean_nat_dec_le(v___x_5160_, v___x_5161_);
lean_dec(v___x_5160_);
if (v___x_5162_ == 0)
{
lean_object* v_val_5163_; lean_object* v___x_5165_; 
v_val_5163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(v_rendering_5129_, v_buckets_x27_5156_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 1, v_val_5163_);
lean_ctor_set(v___x_5136_, 0, v_size_x27_5154_);
v___x_5165_ = v___x_5136_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_size_x27_5154_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v_val_5163_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
else
{
lean_object* v___x_5168_; 
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 1, v_buckets_x27_5156_);
lean_ctor_set(v___x_5136_, 0, v_size_x27_5154_);
v___x_5168_ = v___x_5136_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_size_x27_5154_);
lean_ctor_set(v_reuseFailAlloc_5169_, 1, v_buckets_x27_5156_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
else
{
lean_object* v___x_5170_; lean_object* v_buckets_x27_5171_; lean_object* v_bkt_x27_5172_; lean_object* v___y_5174_; uint8_t v___x_5179_; 
lean_inc(v_bkt_5151_);
v___x_5170_ = lean_box(0);
v_buckets_x27_5171_ = lean_array_uset(v_buckets_5134_, v___x_5150_, v___x_5170_);
lean_inc(v_a_5132_);
v_bkt_x27_5172_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg(v___x_5130_, v_a_5132_, v_bkt_5151_);
v___x_5179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_5132_, v_bkt_x27_5172_);
lean_dec(v_a_5132_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5180_ = lean_unsigned_to_nat(1u);
v___x_5181_ = lean_nat_sub(v_size_5133_, v___x_5180_);
lean_dec(v_size_5133_);
v___y_5174_ = v___x_5181_;
goto v___jp_5173_;
}
else
{
v___y_5174_ = v_size_5133_;
goto v___jp_5173_;
}
v___jp_5173_:
{
lean_object* v___x_5175_; lean_object* v___x_5177_; 
v___x_5175_ = lean_array_uset(v_buckets_x27_5171_, v___x_5150_, v_bkt_x27_5172_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 1, v___x_5175_);
lean_ctor_set(v___x_5136_, 0, v___y_5174_);
v___x_5177_ = v___x_5136_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v___y_5174_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v___x_5175_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8___boxed(lean_object* v_rendering_5183_, lean_object* v___x_5184_, lean_object* v_m_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8(v_rendering_5183_, v___x_5184_, v_m_5185_, v_a_5186_);
lean_dec_ref(v_rendering_5183_);
return v_res_5187_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg(lean_object* v_rendering_5188_, lean_object* v_m_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_buckets_5191_; lean_object* v___x_5192_; uint64_t v___x_5193_; uint64_t v___x_5194_; uint64_t v___x_5195_; uint64_t v_fold_5196_; uint64_t v___x_5197_; uint64_t v___x_5198_; uint64_t v___x_5199_; size_t v___x_5200_; size_t v___x_5201_; size_t v___x_5202_; size_t v___x_5203_; size_t v___x_5204_; lean_object* v___x_5205_; uint8_t v___x_5206_; 
v_buckets_5191_ = lean_ctor_get(v_m_5189_, 1);
v___x_5192_ = lean_array_get_size(v_buckets_5191_);
v___x_5193_ = l_instHashablePos__lean_hash___redArg(v_a_5190_);
v___x_5194_ = 32ULL;
v___x_5195_ = lean_uint64_shift_right(v___x_5193_, v___x_5194_);
v_fold_5196_ = lean_uint64_xor(v___x_5193_, v___x_5195_);
v___x_5197_ = 16ULL;
v___x_5198_ = lean_uint64_shift_right(v_fold_5196_, v___x_5197_);
v___x_5199_ = lean_uint64_xor(v_fold_5196_, v___x_5198_);
v___x_5200_ = lean_uint64_to_usize(v___x_5199_);
v___x_5201_ = lean_usize_of_nat(v___x_5192_);
v___x_5202_ = ((size_t)1ULL);
v___x_5203_ = lean_usize_sub(v___x_5201_, v___x_5202_);
v___x_5204_ = lean_usize_land(v___x_5200_, v___x_5203_);
v___x_5205_ = lean_array_uget_borrowed(v_buckets_5191_, v___x_5204_);
v___x_5206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_5190_, v___x_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg___boxed(lean_object* v_rendering_5207_, lean_object* v_m_5208_, lean_object* v_a_5209_){
_start:
{
uint8_t v_res_5210_; lean_object* v_r_5211_; 
v_res_5210_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg(v_rendering_5207_, v_m_5208_, v_a_5209_);
lean_dec(v_a_5209_);
lean_dec_ref(v_m_5208_);
lean_dec_ref(v_rendering_5207_);
v_r_5211_ = lean_box(v_res_5210_);
return v_r_5211_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3(void){
_start:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__2));
v___x_5216_ = lean_unsigned_to_nat(12u);
v___x_5217_ = lean_unsigned_to_nat(661u);
v___x_5218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__1));
v___x_5219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__0));
v___x_5220_ = l_mkPanicMessageWithDecl(v___x_5219_, v___x_5218_, v___x_5217_, v___x_5216_, v___x_5215_);
return v___x_5220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4(void){
_start:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__2));
v___x_5222_ = lean_unsigned_to_nat(12u);
v___x_5223_ = lean_unsigned_to_nat(666u);
v___x_5224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__1));
v___x_5225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__0));
v___x_5226_ = l_mkPanicMessageWithDecl(v___x_5225_, v___x_5224_, v___x_5223_, v___x_5222_, v___x_5221_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11(lean_object* v_rendering_5227_, lean_object* v___x_5228_, lean_object* v_a_5229_, lean_object* v_lineInfos_5230_, lean_object* v_maxColumnWidth_5231_, lean_object* v_as_5232_, size_t v_sz_5233_, size_t v_i_5234_, lean_object* v_b_5235_){
_start:
{
lean_object* v_a_5237_; lean_object* v___y_5242_; lean_object* v_lineLengths_5246_; lean_object* v_containsEndOfLineComments_5247_; lean_object* v_r_5248_; uint8_t v___x_5254_; 
v___x_5254_ = lean_usize_dec_lt(v_i_5234_, v_sz_5233_);
if (v___x_5254_ == 0)
{
lean_dec_ref(v_a_5229_);
lean_dec_ref(v_rendering_5227_);
return v_b_5235_;
}
else
{
lean_object* v_a_5255_; lean_object* v_snd_5256_; lean_object* v_fst_5257_; lean_object* v_snd_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5406_; 
v_a_5255_ = lean_array_uget(v_as_5232_, v_i_5234_);
v_snd_5256_ = lean_ctor_get(v_b_5235_, 1);
lean_inc(v_snd_5256_);
v_fst_5257_ = lean_ctor_get(v_a_5255_, 0);
v_snd_5258_ = lean_ctor_get(v_a_5255_, 1);
v_isSharedCheck_5406_ = !lean_is_exclusive(v_a_5255_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5260_ = v_a_5255_;
v_isShared_5261_ = v_isSharedCheck_5406_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_snd_5258_);
lean_inc(v_fst_5257_);
lean_dec(v_a_5255_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5406_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v_fst_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5404_; 
v_fst_5262_ = lean_ctor_get(v_b_5235_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v_b_5235_);
if (v_isSharedCheck_5404_ == 0)
{
lean_object* v_unused_5405_; 
v_unused_5405_ = lean_ctor_get(v_b_5235_, 1);
lean_dec(v_unused_5405_);
v___x_5264_ = v_b_5235_;
v_isShared_5265_ = v_isSharedCheck_5404_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_fst_5262_);
lean_dec(v_b_5235_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5404_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v_fst_5266_; lean_object* v_snd_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5403_; 
v_fst_5266_ = lean_ctor_get(v_snd_5256_, 0);
v_snd_5267_ = lean_ctor_get(v_snd_5256_, 1);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_snd_5256_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5269_ = v_snd_5256_;
v_isShared_5270_ = v_isSharedCheck_5403_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_snd_5267_);
lean_inc(v_fst_5266_);
lean_dec(v_snd_5256_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5403_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
uint8_t v___y_5272_; uint8_t v_kind_5281_; lean_object* v_rendering_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; uint8_t v___x_5287_; 
v_kind_5281_ = lean_ctor_get_uint8(v_fst_5257_, sizeof(void*)*1);
v_rendering_5282_ = lean_ctor_get(v_fst_5257_, 0);
lean_inc_ref(v_rendering_5282_);
lean_dec(v_fst_5257_);
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = lean_array_get_size(v___x_5228_);
v___x_5285_ = lean_unsigned_to_nat(1u);
v___x_5286_ = lean_nat_sub(v___x_5284_, v___x_5285_);
v___x_5287_ = lean_nat_dec_eq(v_snd_5258_, v___x_5286_);
lean_dec(v___x_5286_);
lean_dec(v_snd_5258_);
switch(v_kind_5281_)
{
case 0:
{
lean_object* v_startInclusive_5288_; lean_object* v___x_5289_; lean_object* v_snd_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5322_; 
lean_del_object(v___x_5269_);
lean_del_object(v___x_5264_);
v_startInclusive_5288_ = lean_ctor_get(v_a_5229_, 0);
lean_inc(v_startInclusive_5288_);
lean_inc_ref(v_rendering_5227_);
v___x_5289_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(v_rendering_5227_, v_lineInfos_5230_, v_startInclusive_5288_);
v_snd_5290_ = lean_ctor_get(v___x_5289_, 1);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5322_ == 0)
{
lean_object* v_unused_5323_; 
v_unused_5323_ = lean_ctor_get(v___x_5289_, 0);
lean_dec(v_unused_5323_);
v___x_5292_ = v___x_5289_;
v_isShared_5293_ = v_isSharedCheck_5322_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_snd_5290_);
lean_dec(v___x_5289_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5322_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v_range_5294_; lean_object* v_indentation_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5320_; 
v_range_5294_ = lean_ctor_get(v_snd_5290_, 2);
v_indentation_5295_ = lean_ctor_get(v_snd_5290_, 1);
v_isSharedCheck_5320_ = !lean_is_exclusive(v_snd_5290_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v_snd_5290_, 0);
lean_dec(v_unused_5321_);
v___x_5297_ = v_snd_5290_;
v_isShared_5298_ = v_isSharedCheck_5320_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_range_5294_);
lean_inc(v_indentation_5295_);
lean_dec(v_snd_5290_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5320_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v_startInclusive_5299_; lean_object* v_rendered_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5306_; 
v_startInclusive_5299_ = lean_ctor_get(v_range_5294_, 0);
lean_inc(v_startInclusive_5299_);
lean_dec_ref(v_range_5294_);
v_rendered_5300_ = lean_ctor_get(v_rendering_5282_, 0);
lean_inc_ref(v_rendered_5300_);
lean_dec_ref(v_rendering_5282_);
v___x_5301_ = l___private_Lean_Fmt_FmtM_Comments_0__String_indent(v_rendered_5300_, v_indentation_5295_);
v___x_5302_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Comments_0__String_indent_spec__1___closed__0));
v___x_5303_ = lean_string_append(v___x_5301_, v___x_5302_);
v___x_5306_ = lean_string_utf8_byte_size(v___x_5303_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5308_; 
lean_inc_ref(v___x_5303_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 2, v___x_5306_);
lean_ctor_set(v___x_5297_, 1, v___x_5283_);
lean_ctor_set(v___x_5297_, 0, v___x_5303_);
v___x_5308_ = v___x_5297_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5303_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v___x_5283_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v___x_5306_);
v___x_5308_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; 
v___x_5309_ = l_String_Slice_positions(v___x_5308_);
v___x_5310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_5308_, v___x_5303_, v___x_5309_, v___x_5283_);
lean_dec_ref(v___x_5308_);
v___x_5311_ = lean_nat_sub(v___x_5310_, v___x_5285_);
lean_dec(v___x_5310_);
v___x_5312_ = lean_nat_dec_lt(v_maxColumnWidth_5231_, v___x_5311_);
lean_dec(v___x_5311_);
if (v___x_5312_ == 0)
{
lean_del_object(v___x_5292_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5304_;
}
else
{
lean_object* v___x_5314_; 
lean_dec_ref(v___x_5303_);
lean_dec(v_startInclusive_5299_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 1, v_snd_5267_);
lean_ctor_set(v___x_5292_, 0, v_fst_5266_);
v___x_5314_ = v___x_5292_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_fst_5266_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_snd_5267_);
v___x_5314_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5316_; 
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 1, v___x_5314_);
lean_ctor_set(v___x_5260_, 0, v_fst_5262_);
v___x_5316_ = v___x_5260_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
v_a_5237_ = v___x_5316_;
goto v___jp_5236_;
}
}
}
}
}
else
{
lean_del_object(v___x_5297_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5304_;
}
v___jp_5304_:
{
lean_object* v___x_5305_; 
v___x_5305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8(v_rendering_5227_, v___x_5303_, v_snd_5267_, v_startInclusive_5299_);
lean_dec_ref(v_rendering_5227_);
v_lineLengths_5246_ = v_fst_5262_;
v_containsEndOfLineComments_5247_ = v_fst_5266_;
v_r_5248_ = v___x_5305_;
goto v___jp_5245_;
}
}
}
}
case 1:
{
lean_object* v_endExclusive_5324_; lean_object* v___x_5325_; lean_object* v_fst_5326_; lean_object* v_snd_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5376_; 
v_endExclusive_5324_ = lean_ctor_get(v_a_5229_, 1);
lean_inc(v_endExclusive_5324_);
lean_inc_ref(v_rendering_5227_);
v___x_5325_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(v_rendering_5227_, v_lineInfos_5230_, v_endExclusive_5324_);
v_fst_5326_ = lean_ctor_get(v___x_5325_, 0);
v_snd_5327_ = lean_ctor_get(v___x_5325_, 1);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5329_ = v___x_5325_;
v_isShared_5330_ = v_isSharedCheck_5376_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_snd_5327_);
lean_inc(v_fst_5326_);
lean_dec(v___x_5325_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5376_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
uint8_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; uint8_t v___x_5334_; 
v___x_5331_ = 0;
v___x_5332_ = lean_box(v___x_5331_);
v___x_5333_ = lean_array_get(v___x_5332_, v_fst_5266_, v_fst_5326_);
lean_dec(v___x_5332_);
v___x_5334_ = lean_unbox(v___x_5333_);
if (v___x_5334_ == 0)
{
lean_object* v_range_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5366_; 
v_range_5335_ = lean_ctor_get(v_snd_5327_, 2);
v_isSharedCheck_5366_ = !lean_is_exclusive(v_snd_5327_);
if (v_isSharedCheck_5366_ == 0)
{
lean_object* v_unused_5367_; lean_object* v_unused_5368_; 
v_unused_5367_ = lean_ctor_get(v_snd_5327_, 1);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_snd_5327_, 0);
lean_dec(v_unused_5368_);
v___x_5337_ = v_snd_5327_;
v_isShared_5338_ = v_isSharedCheck_5366_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_range_5335_);
lean_dec(v_snd_5327_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5366_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v_endExclusive_5339_; uint8_t v___x_5340_; 
v_endExclusive_5339_ = lean_ctor_get(v_range_5335_, 1);
lean_inc(v_endExclusive_5339_);
lean_dec_ref(v_range_5335_);
v___x_5340_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg(v_rendering_5227_, v_snd_5267_, v_endExclusive_5339_);
if (v___x_5340_ == 0)
{
lean_object* v_rendered_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5347_; 
lean_dec(v___x_5333_);
lean_del_object(v___x_5269_);
lean_del_object(v___x_5264_);
v_rendered_5341_ = lean_ctor_get(v_rendering_5282_, 0);
lean_inc_ref(v_rendered_5341_);
lean_dec_ref(v_rendering_5282_);
v___x_5342_ = lean_array_get_borrowed(v___x_5283_, v_fst_5262_, v_fst_5326_);
v___x_5343_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0));
v___x_5344_ = lean_string_append(v___x_5343_, v_rendered_5341_);
lean_dec_ref(v_rendered_5341_);
v___x_5345_ = lean_string_utf8_byte_size(v___x_5344_);
lean_inc_ref(v___x_5344_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 2, v___x_5345_);
lean_ctor_set(v___x_5337_, 1, v___x_5283_);
lean_ctor_set(v___x_5337_, 0, v___x_5344_);
v___x_5347_ = v___x_5337_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v___x_5283_);
lean_ctor_set(v_reuseFailAlloc_5364_, 2, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5348_ = l_String_Slice_positions(v___x_5347_);
v___x_5349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_5347_, v___x_5344_, v___x_5348_, v___x_5283_);
lean_dec_ref(v___x_5347_);
v___x_5350_ = lean_nat_add(v___x_5342_, v___x_5349_);
lean_dec(v___x_5349_);
if (v___x_5287_ == 0)
{
goto v___jp_5356_;
}
else
{
if (v___x_5340_ == 0)
{
lean_del_object(v___x_5329_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5351_;
}
else
{
goto v___jp_5356_;
}
}
v___jp_5351_:
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5352_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg(v_rendering_5227_, v_snd_5267_, v_endExclusive_5339_, v___x_5344_);
lean_dec_ref(v_rendering_5227_);
v___x_5353_ = lean_array_set(v_fst_5262_, v_fst_5326_, v___x_5350_);
v___x_5354_ = lean_box(v___x_5254_);
v___x_5355_ = lean_array_set(v_fst_5266_, v_fst_5326_, v___x_5354_);
lean_dec(v_fst_5326_);
v_lineLengths_5246_ = v___x_5353_;
v_containsEndOfLineComments_5247_ = v___x_5355_;
v_r_5248_ = v___x_5352_;
goto v___jp_5245_;
}
v___jp_5356_:
{
uint8_t v___x_5357_; 
v___x_5357_ = lean_nat_dec_lt(v_maxColumnWidth_5231_, v___x_5350_);
if (v___x_5357_ == 0)
{
lean_del_object(v___x_5329_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5351_;
}
else
{
lean_object* v___x_5359_; 
lean_dec(v___x_5350_);
lean_dec_ref(v___x_5344_);
lean_dec(v_endExclusive_5339_);
lean_dec(v_fst_5326_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 1, v_snd_5267_);
lean_ctor_set(v___x_5329_, 0, v_fst_5266_);
v___x_5359_ = v___x_5329_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_fst_5266_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_snd_5267_);
v___x_5359_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
lean_object* v___x_5361_; 
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 1, v___x_5359_);
lean_ctor_set(v___x_5260_, 0, v_fst_5262_);
v___x_5361_ = v___x_5260_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5362_, 1, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
v_a_5237_ = v___x_5361_;
goto v___jp_5236_;
}
}
}
}
}
}
else
{
lean_dec(v_endExclusive_5339_);
lean_del_object(v___x_5337_);
lean_del_object(v___x_5329_);
lean_dec(v_fst_5326_);
lean_dec_ref(v_rendering_5282_);
lean_del_object(v___x_5260_);
if (v___x_5287_ == 0)
{
lean_dec(v___x_5333_);
v___y_5272_ = v___x_5340_;
goto v___jp_5271_;
}
else
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_unbox(v___x_5333_);
lean_dec(v___x_5333_);
v___y_5272_ = v___x_5365_;
goto v___jp_5271_;
}
}
}
}
else
{
lean_dec(v_snd_5327_);
lean_dec(v_fst_5326_);
lean_dec_ref(v_rendering_5282_);
lean_del_object(v___x_5269_);
lean_del_object(v___x_5264_);
if (v___x_5287_ == 0)
{
uint8_t v___x_5369_; 
v___x_5369_ = lean_unbox(v___x_5333_);
lean_dec(v___x_5333_);
if (v___x_5369_ == 0)
{
lean_del_object(v___x_5329_);
lean_dec(v_snd_5267_);
lean_dec(v_fst_5266_);
lean_dec(v_fst_5262_);
lean_del_object(v___x_5260_);
goto v___jp_5251_;
}
else
{
lean_object* v___x_5371_; 
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 1, v_snd_5267_);
lean_ctor_set(v___x_5329_, 0, v_fst_5266_);
v___x_5371_ = v___x_5329_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_fst_5266_);
lean_ctor_set(v_reuseFailAlloc_5375_, 1, v_snd_5267_);
v___x_5371_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
lean_object* v___x_5373_; 
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 1, v___x_5371_);
lean_ctor_set(v___x_5260_, 0, v_fst_5262_);
v___x_5373_ = v___x_5260_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5374_, 1, v___x_5371_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
v_a_5237_ = v___x_5373_;
goto v___jp_5236_;
}
}
}
}
else
{
lean_dec(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec(v_snd_5267_);
lean_dec(v_fst_5266_);
lean_dec(v_fst_5262_);
lean_del_object(v___x_5260_);
goto v___jp_5251_;
}
}
}
}
default: 
{
lean_object* v_endExclusive_5377_; lean_object* v___x_5378_; lean_object* v_fst_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5401_; 
lean_del_object(v___x_5269_);
lean_del_object(v___x_5264_);
v_endExclusive_5377_ = lean_ctor_get(v_a_5229_, 1);
lean_inc(v_endExclusive_5377_);
lean_inc_ref(v_rendering_5227_);
v___x_5378_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_findLineInfoContaining(v_rendering_5227_, v_lineInfos_5230_, v_endExclusive_5377_);
v_fst_5379_ = lean_ctor_get(v___x_5378_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5401_ == 0)
{
lean_object* v_unused_5402_; 
v_unused_5402_ = lean_ctor_get(v___x_5378_, 1);
lean_dec(v_unused_5402_);
v___x_5381_ = v___x_5378_;
v_isShared_5382_ = v_isSharedCheck_5401_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_fst_5379_);
lean_dec(v___x_5378_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5401_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v_rendered_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5388_; 
v_rendered_5383_ = lean_ctor_get(v_rendering_5282_, 0);
lean_inc_ref(v_rendered_5383_);
lean_dec_ref(v_rendering_5282_);
v___x_5384_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0));
v___x_5385_ = lean_string_append(v___x_5384_, v_rendered_5383_);
lean_dec_ref(v_rendered_5383_);
v___x_5388_ = lean_string_utf8_byte_size(v___x_5385_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; uint8_t v___x_5394_; 
lean_inc_ref(v___x_5385_);
v___x_5389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5385_);
lean_ctor_set(v___x_5389_, 1, v___x_5283_);
lean_ctor_set(v___x_5389_, 2, v___x_5388_);
v___x_5390_ = lean_array_get_borrowed(v___x_5283_, v_fst_5262_, v_fst_5379_);
lean_dec(v_fst_5379_);
v___x_5391_ = l_String_Slice_positions(v___x_5389_);
v___x_5392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_contentColumnOffset_spec__3___redArg(v___x_5389_, v___x_5385_, v___x_5391_, v___x_5283_);
lean_dec_ref_known(v___x_5389_, 3);
v___x_5393_ = lean_nat_add(v___x_5390_, v___x_5392_);
lean_dec(v___x_5392_);
v___x_5394_ = lean_nat_dec_lt(v_maxColumnWidth_5231_, v___x_5393_);
lean_dec(v___x_5393_);
if (v___x_5394_ == 0)
{
lean_inc(v_endExclusive_5377_);
lean_del_object(v___x_5381_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5386_;
}
else
{
lean_object* v___x_5396_; 
lean_dec_ref(v___x_5385_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 1, v_snd_5267_);
lean_ctor_set(v___x_5381_, 0, v_fst_5266_);
v___x_5396_ = v___x_5381_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_fst_5266_);
lean_ctor_set(v_reuseFailAlloc_5400_, 1, v_snd_5267_);
v___x_5396_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5398_; 
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 1, v___x_5396_);
lean_ctor_set(v___x_5260_, 0, v_fst_5262_);
v___x_5398_ = v___x_5260_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
v_a_5237_ = v___x_5398_;
goto v___jp_5236_;
}
}
}
}
else
{
lean_inc(v_endExclusive_5377_);
lean_del_object(v___x_5381_);
lean_dec(v_fst_5379_);
lean_del_object(v___x_5260_);
lean_dec_ref(v_a_5229_);
goto v___jp_5386_;
}
v___jp_5386_:
{
lean_object* v___x_5387_; 
v___x_5387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8(v_rendering_5227_, v___x_5385_, v_snd_5267_, v_endExclusive_5377_);
lean_dec_ref(v_rendering_5227_);
v_lineLengths_5246_ = v_fst_5262_;
v_containsEndOfLineComments_5247_ = v_fst_5266_;
v_r_5248_ = v___x_5387_;
goto v___jp_5245_;
}
}
}
}
v___jp_5271_:
{
if (v___y_5272_ == 0)
{
lean_object* v___x_5273_; lean_object* v___x_5274_; 
lean_del_object(v___x_5269_);
lean_dec(v_snd_5267_);
lean_dec(v_fst_5266_);
lean_del_object(v___x_5264_);
lean_dec(v_fst_5262_);
v___x_5273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__4);
lean_inc_ref(v_rendering_5227_);
v___x_5274_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7(v_rendering_5227_, v___x_5273_);
v___y_5242_ = v___x_5274_;
goto v___jp_5241_;
}
else
{
lean_object* v___x_5276_; 
if (v_isShared_5270_ == 0)
{
v___x_5276_ = v___x_5269_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_fst_5266_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v_snd_5267_);
v___x_5276_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
lean_object* v___x_5278_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 1, v___x_5276_);
v___x_5278_ = v___x_5264_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_fst_5262_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
v_a_5237_ = v___x_5278_;
goto v___jp_5236_;
}
}
}
}
}
}
}
}
v___jp_5236_:
{
size_t v___x_5238_; size_t v___x_5239_; 
v___x_5238_ = ((size_t)1ULL);
v___x_5239_ = lean_usize_add(v_i_5234_, v___x_5238_);
v_i_5234_ = v___x_5239_;
v_b_5235_ = v_a_5237_;
goto _start;
}
v___jp_5241_:
{
if (lean_obj_tag(v___y_5242_) == 0)
{
lean_object* v_a_5243_; 
lean_dec_ref(v_a_5229_);
lean_dec_ref(v_rendering_5227_);
v_a_5243_ = lean_ctor_get(v___y_5242_, 0);
lean_inc(v_a_5243_);
lean_dec_ref_known(v___y_5242_, 1);
return v_a_5243_;
}
else
{
lean_object* v_a_5244_; 
v_a_5244_ = lean_ctor_get(v___y_5242_, 0);
lean_inc(v_a_5244_);
lean_dec_ref_known(v___y_5242_, 1);
v_a_5237_ = v_a_5244_;
goto v___jp_5236_;
}
}
v___jp_5245_:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5249_, 0, v_containsEndOfLineComments_5247_);
lean_ctor_set(v___x_5249_, 1, v_r_5248_);
v___x_5250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5250_, 0, v_lineLengths_5246_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
return v___x_5250_;
}
v___jp_5251_:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___closed__3);
lean_inc_ref(v_rendering_5227_);
v___x_5253_ = l_panic___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__7(v_rendering_5227_, v___x_5252_);
v___y_5242_ = v___x_5253_;
goto v___jp_5241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11___boxed(lean_object* v_rendering_5407_, lean_object* v___x_5408_, lean_object* v_a_5409_, lean_object* v_lineInfos_5410_, lean_object* v_maxColumnWidth_5411_, lean_object* v_as_5412_, lean_object* v_sz_5413_, lean_object* v_i_5414_, lean_object* v_b_5415_){
_start:
{
size_t v_sz_boxed_5416_; size_t v_i_boxed_5417_; lean_object* v_res_5418_; 
v_sz_boxed_5416_ = lean_unbox_usize(v_sz_5413_);
lean_dec(v_sz_5413_);
v_i_boxed_5417_ = lean_unbox_usize(v_i_5414_);
lean_dec(v_i_5414_);
v_res_5418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11(v_rendering_5407_, v___x_5408_, v_a_5409_, v_lineInfos_5410_, v_maxColumnWidth_5411_, v_as_5412_, v_sz_boxed_5416_, v_i_boxed_5417_, v_b_5415_);
lean_dec_ref(v_as_5412_);
lean_dec(v_maxColumnWidth_5411_);
lean_dec_ref(v_lineInfos_5410_);
lean_dec_ref(v___x_5408_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12(lean_object* v_rendering_5419_, lean_object* v_a_5420_, lean_object* v_lineInfos_5421_, lean_object* v_maxColumnWidth_5422_, lean_object* v_as_5423_, size_t v_sz_5424_, size_t v_i_5425_, lean_object* v_b_5426_){
_start:
{
uint8_t v___x_5427_; 
v___x_5427_ = lean_usize_dec_lt(v_i_5425_, v_sz_5424_);
if (v___x_5427_ == 0)
{
lean_dec_ref(v_a_5420_);
lean_dec_ref(v_rendering_5419_);
return v_b_5426_;
}
else
{
lean_object* v_snd_5428_; lean_object* v_fst_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5473_; 
v_snd_5428_ = lean_ctor_get(v_b_5426_, 1);
v_fst_5429_ = lean_ctor_get(v_b_5426_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_b_5426_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5431_ = v_b_5426_;
v_isShared_5432_ = v_isSharedCheck_5473_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_snd_5428_);
lean_inc(v_fst_5429_);
lean_dec(v_b_5426_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5473_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v_fst_5433_; lean_object* v_snd_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5472_; 
v_fst_5433_ = lean_ctor_get(v_snd_5428_, 0);
v_snd_5434_ = lean_ctor_get(v_snd_5428_, 1);
v_isSharedCheck_5472_ = !lean_is_exclusive(v_snd_5428_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5436_ = v_snd_5428_;
v_isShared_5437_ = v_isSharedCheck_5472_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_snd_5434_);
lean_inc(v_fst_5433_);
lean_dec(v_snd_5428_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5472_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v_a_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5443_; 
v_a_5438_ = lean_array_uget_borrowed(v_as_5423_, v_i_5425_);
lean_inc(v_a_5438_);
v___x_5439_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_Comment_renderedPlacements(v_a_5438_);
v___x_5440_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_5439_);
v___x_5441_ = l_Array_zipIdx___redArg(v___x_5439_, v___x_5440_);
if (v_isShared_5437_ == 0)
{
v___x_5443_ = v___x_5436_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_fst_5433_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_snd_5434_);
v___x_5443_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_5445_; 
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 1, v___x_5443_);
v___x_5445_ = v___x_5431_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_fst_5429_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5443_);
v___x_5445_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
size_t v_sz_5446_; size_t v___x_5447_; lean_object* v___x_5448_; lean_object* v_snd_5449_; lean_object* v_fst_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5469_; 
v_sz_5446_ = lean_array_size(v___x_5441_);
v___x_5447_ = ((size_t)0ULL);
lean_inc_ref(v_a_5420_);
lean_inc_ref(v_rendering_5419_);
v___x_5448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__11(v_rendering_5419_, v___x_5439_, v_a_5420_, v_lineInfos_5421_, v_maxColumnWidth_5422_, v___x_5441_, v_sz_5446_, v___x_5447_, v___x_5445_);
lean_dec_ref(v___x_5441_);
lean_dec_ref(v___x_5439_);
v_snd_5449_ = lean_ctor_get(v___x_5448_, 1);
v_fst_5450_ = lean_ctor_get(v___x_5448_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5452_ = v___x_5448_;
v_isShared_5453_ = v_isSharedCheck_5469_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_snd_5449_);
lean_inc(v_fst_5450_);
lean_dec(v___x_5448_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5469_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v_fst_5454_; lean_object* v_snd_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5468_; 
v_fst_5454_ = lean_ctor_get(v_snd_5449_, 0);
v_snd_5455_ = lean_ctor_get(v_snd_5449_, 1);
v_isSharedCheck_5468_ = !lean_is_exclusive(v_snd_5449_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5457_ = v_snd_5449_;
v_isShared_5458_ = v_isSharedCheck_5468_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_snd_5455_);
lean_inc(v_fst_5454_);
lean_dec(v_snd_5449_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5468_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_fst_5454_);
lean_ctor_set(v_reuseFailAlloc_5467_, 1, v_snd_5455_);
v___x_5460_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
lean_object* v___x_5462_; 
if (v_isShared_5453_ == 0)
{
lean_ctor_set(v___x_5452_, 1, v___x_5460_);
v___x_5462_ = v___x_5452_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_fst_5450_);
lean_ctor_set(v_reuseFailAlloc_5466_, 1, v___x_5460_);
v___x_5462_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
size_t v___x_5463_; size_t v___x_5464_; 
v___x_5463_ = ((size_t)1ULL);
v___x_5464_ = lean_usize_add(v_i_5425_, v___x_5463_);
v_i_5425_ = v___x_5464_;
v_b_5426_ = v___x_5462_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12___boxed(lean_object* v_rendering_5474_, lean_object* v_a_5475_, lean_object* v_lineInfos_5476_, lean_object* v_maxColumnWidth_5477_, lean_object* v_as_5478_, lean_object* v_sz_5479_, lean_object* v_i_5480_, lean_object* v_b_5481_){
_start:
{
size_t v_sz_boxed_5482_; size_t v_i_boxed_5483_; lean_object* v_res_5484_; 
v_sz_boxed_5482_ = lean_unbox_usize(v_sz_5479_);
lean_dec(v_sz_5479_);
v_i_boxed_5483_ = lean_unbox_usize(v_i_5480_);
lean_dec(v_i_5480_);
v_res_5484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12(v_rendering_5474_, v_a_5475_, v_lineInfos_5476_, v_maxColumnWidth_5477_, v_as_5478_, v_sz_boxed_5482_, v_i_boxed_5483_, v_b_5481_);
lean_dec_ref(v_as_5478_);
lean_dec(v_maxColumnWidth_5477_);
lean_dec_ref(v_lineInfos_5476_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13(lean_object* v_rendering_5485_, lean_object* v_lineInfos_5486_, lean_object* v_maxColumnWidth_5487_, lean_object* v_init_5488_, lean_object* v_x_5489_){
_start:
{
if (lean_obj_tag(v_x_5489_) == 0)
{
lean_object* v_k_5490_; lean_object* v_v_5491_; lean_object* v_l_5492_; lean_object* v_r_5493_; lean_object* v___x_5494_; lean_object* v_a_5495_; lean_object* v_snd_5496_; lean_object* v_fst_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5535_; 
v_k_5490_ = lean_ctor_get(v_x_5489_, 1);
lean_inc(v_k_5490_);
v_v_5491_ = lean_ctor_get(v_x_5489_, 2);
lean_inc(v_v_5491_);
v_l_5492_ = lean_ctor_get(v_x_5489_, 3);
lean_inc(v_l_5492_);
v_r_5493_ = lean_ctor_get(v_x_5489_, 4);
lean_inc(v_r_5493_);
lean_dec_ref_known(v_x_5489_, 5);
lean_inc_ref(v_rendering_5485_);
v___x_5494_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13(v_rendering_5485_, v_lineInfos_5486_, v_maxColumnWidth_5487_, v_init_5488_, v_l_5492_);
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref(v___x_5494_);
v_snd_5496_ = lean_ctor_get(v_a_5495_, 1);
v_fst_5497_ = lean_ctor_get(v_a_5495_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_a_5495_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5499_ = v_a_5495_;
v_isShared_5500_ = v_isSharedCheck_5535_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_snd_5496_);
lean_inc(v_fst_5497_);
lean_dec(v_a_5495_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5535_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v_fst_5501_; lean_object* v_snd_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5534_; 
v_fst_5501_ = lean_ctor_get(v_snd_5496_, 0);
v_snd_5502_ = lean_ctor_get(v_snd_5496_, 1);
v_isSharedCheck_5534_ = !lean_is_exclusive(v_snd_5496_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5504_ = v_snd_5496_;
v_isShared_5505_ = v_isSharedCheck_5534_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_snd_5502_);
lean_inc(v_fst_5501_);
lean_dec(v_snd_5496_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5534_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_fst_5501_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_snd_5502_);
v___x_5507_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; 
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 1, v___x_5507_);
v___x_5509_ = v___x_5499_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_fst_5497_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
size_t v_sz_5510_; size_t v___x_5511_; lean_object* v___x_5512_; lean_object* v_snd_5513_; lean_object* v_fst_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5531_; 
v_sz_5510_ = lean_array_size(v_v_5491_);
v___x_5511_ = ((size_t)0ULL);
lean_inc_ref(v_rendering_5485_);
v___x_5512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__12(v_rendering_5485_, v_k_5490_, v_lineInfos_5486_, v_maxColumnWidth_5487_, v_v_5491_, v_sz_5510_, v___x_5511_, v___x_5509_);
lean_dec(v_v_5491_);
v_snd_5513_ = lean_ctor_get(v___x_5512_, 1);
v_fst_5514_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5516_ = v___x_5512_;
v_isShared_5517_ = v_isSharedCheck_5531_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_snd_5513_);
lean_inc(v_fst_5514_);
lean_dec(v___x_5512_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5531_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v_fst_5518_; lean_object* v_snd_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5530_; 
v_fst_5518_ = lean_ctor_get(v_snd_5513_, 0);
v_snd_5519_ = lean_ctor_get(v_snd_5513_, 1);
v_isSharedCheck_5530_ = !lean_is_exclusive(v_snd_5513_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5521_ = v_snd_5513_;
v_isShared_5522_ = v_isSharedCheck_5530_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_snd_5519_);
lean_inc(v_fst_5518_);
lean_dec(v_snd_5513_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5530_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5518_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5519_);
v___x_5524_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
lean_object* v___x_5526_; 
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v___x_5524_);
v___x_5526_ = v___x_5516_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v___x_5524_);
v___x_5526_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
v_init_5488_ = v___x_5526_;
v_x_5489_ = v_r_5493_;
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
else
{
lean_object* v___x_5536_; 
lean_dec_ref(v_rendering_5485_);
v___x_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_init_5488_);
return v___x_5536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13___boxed(lean_object* v_rendering_5537_, lean_object* v_lineInfos_5538_, lean_object* v_maxColumnWidth_5539_, lean_object* v_init_5540_, lean_object* v_x_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13(v_rendering_5537_, v_lineInfos_5538_, v_maxColumnWidth_5539_, v_init_5540_, v_x_5541_);
lean_dec(v_maxColumnWidth_5539_);
lean_dec_ref(v_lineInfos_5538_);
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6(size_t v_sz_5543_, size_t v_i_5544_, lean_object* v_bs_5545_){
_start:
{
uint8_t v___x_5546_; 
v___x_5546_ = lean_usize_dec_lt(v_i_5544_, v_sz_5543_);
if (v___x_5546_ == 0)
{
return v_bs_5545_;
}
else
{
lean_object* v_v_5547_; lean_object* v_length_5548_; lean_object* v___x_5549_; lean_object* v_bs_x27_5550_; size_t v___x_5551_; size_t v___x_5552_; lean_object* v___x_5553_; 
v_v_5547_ = lean_array_uget_borrowed(v_bs_5545_, v_i_5544_);
v_length_5548_ = lean_ctor_get(v_v_5547_, 0);
lean_inc(v_length_5548_);
v___x_5549_ = lean_unsigned_to_nat(0u);
v_bs_x27_5550_ = lean_array_uset(v_bs_5545_, v_i_5544_, v___x_5549_);
v___x_5551_ = ((size_t)1ULL);
v___x_5552_ = lean_usize_add(v_i_5544_, v___x_5551_);
v___x_5553_ = lean_array_uset(v_bs_x27_5550_, v_i_5544_, v_length_5548_);
v_i_5544_ = v___x_5552_;
v_bs_5545_ = v___x_5553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6___boxed(lean_object* v_sz_5555_, lean_object* v_i_5556_, lean_object* v_bs_5557_){
_start:
{
size_t v_sz_boxed_5558_; size_t v_i_boxed_5559_; lean_object* v_res_5560_; 
v_sz_boxed_5558_ = lean_unbox_usize(v_sz_5555_);
lean_dec(v_sz_5555_);
v_i_boxed_5559_ = lean_unbox_usize(v_i_5556_);
lean_dec(v_i_5556_);
v_res_5560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6(v_sz_boxed_5558_, v_i_boxed_5559_, v_bs_5557_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(lean_object* v_k_5561_, lean_object* v_v_5562_, lean_object* v_t_5563_){
_start:
{
if (lean_obj_tag(v_t_5563_) == 0)
{
lean_object* v_size_5564_; lean_object* v_k_5565_; lean_object* v_v_5566_; lean_object* v_l_5567_; lean_object* v_r_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5848_; 
v_size_5564_ = lean_ctor_get(v_t_5563_, 0);
v_k_5565_ = lean_ctor_get(v_t_5563_, 1);
v_v_5566_ = lean_ctor_get(v_t_5563_, 2);
v_l_5567_ = lean_ctor_get(v_t_5563_, 3);
v_r_5568_ = lean_ctor_get(v_t_5563_, 4);
v_isSharedCheck_5848_ = !lean_is_exclusive(v_t_5563_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5570_ = v_t_5563_;
v_isShared_5571_ = v_isSharedCheck_5848_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_r_5568_);
lean_inc(v_l_5567_);
lean_inc(v_v_5566_);
lean_inc(v_k_5565_);
lean_inc(v_size_5564_);
lean_dec(v_t_5563_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5848_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
uint8_t v___x_5572_; 
v___x_5572_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_compareSubslicesLargest___redArg(v_k_5565_, v_k_5561_);
switch(v___x_5572_)
{
case 0:
{
lean_object* v_impl_5573_; lean_object* v___x_5574_; 
lean_dec(v_size_5564_);
v_impl_5573_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(v_k_5561_, v_v_5562_, v_l_5567_);
v___x_5574_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5568_) == 0)
{
lean_object* v_size_5575_; lean_object* v_size_5576_; lean_object* v_k_5577_; lean_object* v_v_5578_; lean_object* v_l_5579_; lean_object* v_r_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; uint8_t v___x_5583_; 
v_size_5575_ = lean_ctor_get(v_r_5568_, 0);
v_size_5576_ = lean_ctor_get(v_impl_5573_, 0);
lean_inc(v_size_5576_);
v_k_5577_ = lean_ctor_get(v_impl_5573_, 1);
lean_inc(v_k_5577_);
v_v_5578_ = lean_ctor_get(v_impl_5573_, 2);
lean_inc(v_v_5578_);
v_l_5579_ = lean_ctor_get(v_impl_5573_, 3);
lean_inc(v_l_5579_);
v_r_5580_ = lean_ctor_get(v_impl_5573_, 4);
lean_inc(v_r_5580_);
v___x_5581_ = lean_unsigned_to_nat(3u);
v___x_5582_ = lean_nat_mul(v___x_5581_, v_size_5575_);
v___x_5583_ = lean_nat_dec_lt(v___x_5582_, v_size_5576_);
lean_dec(v___x_5582_);
if (v___x_5583_ == 0)
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
lean_dec(v_r_5580_);
lean_dec(v_l_5579_);
lean_dec(v_v_5578_);
lean_dec(v_k_5577_);
v___x_5584_ = lean_nat_add(v___x_5574_, v_size_5576_);
lean_dec(v_size_5576_);
v___x_5585_ = lean_nat_add(v___x_5584_, v_size_5575_);
lean_dec(v___x_5584_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 3, v_impl_5573_);
lean_ctor_set(v___x_5570_, 0, v___x_5585_);
v___x_5587_ = v___x_5570_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5588_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5588_, 3, v_impl_5573_);
lean_ctor_set(v_reuseFailAlloc_5588_, 4, v_r_5568_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
else
{
lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5654_; 
v_isSharedCheck_5654_ = !lean_is_exclusive(v_impl_5573_);
if (v_isSharedCheck_5654_ == 0)
{
lean_object* v_unused_5655_; lean_object* v_unused_5656_; lean_object* v_unused_5657_; lean_object* v_unused_5658_; lean_object* v_unused_5659_; 
v_unused_5655_ = lean_ctor_get(v_impl_5573_, 4);
lean_dec(v_unused_5655_);
v_unused_5656_ = lean_ctor_get(v_impl_5573_, 3);
lean_dec(v_unused_5656_);
v_unused_5657_ = lean_ctor_get(v_impl_5573_, 2);
lean_dec(v_unused_5657_);
v_unused_5658_ = lean_ctor_get(v_impl_5573_, 1);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_impl_5573_, 0);
lean_dec(v_unused_5659_);
v___x_5590_ = v_impl_5573_;
v_isShared_5591_ = v_isSharedCheck_5654_;
goto v_resetjp_5589_;
}
else
{
lean_dec(v_impl_5573_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5654_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v_size_5592_; lean_object* v_size_5593_; lean_object* v_k_5594_; lean_object* v_v_5595_; lean_object* v_l_5596_; lean_object* v_r_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; uint8_t v___x_5600_; 
v_size_5592_ = lean_ctor_get(v_l_5579_, 0);
v_size_5593_ = lean_ctor_get(v_r_5580_, 0);
v_k_5594_ = lean_ctor_get(v_r_5580_, 1);
v_v_5595_ = lean_ctor_get(v_r_5580_, 2);
v_l_5596_ = lean_ctor_get(v_r_5580_, 3);
v_r_5597_ = lean_ctor_get(v_r_5580_, 4);
v___x_5598_ = lean_unsigned_to_nat(2u);
v___x_5599_ = lean_nat_mul(v___x_5598_, v_size_5592_);
v___x_5600_ = lean_nat_dec_lt(v_size_5593_, v___x_5599_);
lean_dec(v___x_5599_);
if (v___x_5600_ == 0)
{
lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5629_; 
lean_inc(v_r_5597_);
lean_inc(v_l_5596_);
lean_inc(v_v_5595_);
lean_inc(v_k_5594_);
v_isSharedCheck_5629_ = !lean_is_exclusive(v_r_5580_);
if (v_isSharedCheck_5629_ == 0)
{
lean_object* v_unused_5630_; lean_object* v_unused_5631_; lean_object* v_unused_5632_; lean_object* v_unused_5633_; lean_object* v_unused_5634_; 
v_unused_5630_ = lean_ctor_get(v_r_5580_, 4);
lean_dec(v_unused_5630_);
v_unused_5631_ = lean_ctor_get(v_r_5580_, 3);
lean_dec(v_unused_5631_);
v_unused_5632_ = lean_ctor_get(v_r_5580_, 2);
lean_dec(v_unused_5632_);
v_unused_5633_ = lean_ctor_get(v_r_5580_, 1);
lean_dec(v_unused_5633_);
v_unused_5634_ = lean_ctor_get(v_r_5580_, 0);
lean_dec(v_unused_5634_);
v___x_5602_ = v_r_5580_;
v_isShared_5603_ = v_isSharedCheck_5629_;
goto v_resetjp_5601_;
}
else
{
lean_dec(v_r_5580_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5629_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___x_5617_; lean_object* v___y_5619_; 
v___x_5604_ = lean_nat_add(v___x_5574_, v_size_5576_);
lean_dec(v_size_5576_);
v___x_5605_ = lean_nat_add(v___x_5604_, v_size_5575_);
lean_dec(v___x_5604_);
v___x_5617_ = lean_nat_add(v___x_5574_, v_size_5592_);
if (lean_obj_tag(v_l_5596_) == 0)
{
lean_object* v_size_5627_; 
v_size_5627_ = lean_ctor_get(v_l_5596_, 0);
lean_inc(v_size_5627_);
v___y_5619_ = v_size_5627_;
goto v___jp_5618_;
}
else
{
lean_object* v___x_5628_; 
v___x_5628_ = lean_unsigned_to_nat(0u);
v___y_5619_ = v___x_5628_;
goto v___jp_5618_;
}
v___jp_5606_:
{
lean_object* v___x_5610_; lean_object* v___x_5612_; 
v___x_5610_ = lean_nat_add(v___y_5607_, v___y_5609_);
lean_dec(v___y_5609_);
lean_dec(v___y_5607_);
if (v_isShared_5603_ == 0)
{
lean_ctor_set(v___x_5602_, 4, v_r_5568_);
lean_ctor_set(v___x_5602_, 3, v_r_5597_);
lean_ctor_set(v___x_5602_, 2, v_v_5566_);
lean_ctor_set(v___x_5602_, 1, v_k_5565_);
lean_ctor_set(v___x_5602_, 0, v___x_5610_);
v___x_5612_ = v___x_5602_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v___x_5610_);
lean_ctor_set(v_reuseFailAlloc_5616_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5616_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5616_, 3, v_r_5597_);
lean_ctor_set(v_reuseFailAlloc_5616_, 4, v_r_5568_);
v___x_5612_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___x_5614_; 
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 4, v___x_5612_);
lean_ctor_set(v___x_5590_, 3, v___y_5608_);
lean_ctor_set(v___x_5590_, 2, v_v_5595_);
lean_ctor_set(v___x_5590_, 1, v_k_5594_);
lean_ctor_set(v___x_5590_, 0, v___x_5605_);
v___x_5614_ = v___x_5590_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5605_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_k_5594_);
lean_ctor_set(v_reuseFailAlloc_5615_, 2, v_v_5595_);
lean_ctor_set(v_reuseFailAlloc_5615_, 3, v___y_5608_);
lean_ctor_set(v_reuseFailAlloc_5615_, 4, v___x_5612_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
v___jp_5618_:
{
lean_object* v___x_5620_; lean_object* v___x_5622_; 
v___x_5620_ = lean_nat_add(v___x_5617_, v___y_5619_);
lean_dec(v___y_5619_);
lean_dec(v___x_5617_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_l_5596_);
lean_ctor_set(v___x_5570_, 3, v_l_5579_);
lean_ctor_set(v___x_5570_, 2, v_v_5578_);
lean_ctor_set(v___x_5570_, 1, v_k_5577_);
lean_ctor_set(v___x_5570_, 0, v___x_5620_);
v___x_5622_ = v___x_5570_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5620_);
lean_ctor_set(v_reuseFailAlloc_5626_, 1, v_k_5577_);
lean_ctor_set(v_reuseFailAlloc_5626_, 2, v_v_5578_);
lean_ctor_set(v_reuseFailAlloc_5626_, 3, v_l_5579_);
lean_ctor_set(v_reuseFailAlloc_5626_, 4, v_l_5596_);
v___x_5622_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
lean_object* v___x_5623_; 
v___x_5623_ = lean_nat_add(v___x_5574_, v_size_5575_);
if (lean_obj_tag(v_r_5597_) == 0)
{
lean_object* v_size_5624_; 
v_size_5624_ = lean_ctor_get(v_r_5597_, 0);
lean_inc(v_size_5624_);
v___y_5607_ = v___x_5623_;
v___y_5608_ = v___x_5622_;
v___y_5609_ = v_size_5624_;
goto v___jp_5606_;
}
else
{
lean_object* v___x_5625_; 
v___x_5625_ = lean_unsigned_to_nat(0u);
v___y_5607_ = v___x_5623_;
v___y_5608_ = v___x_5622_;
v___y_5609_ = v___x_5625_;
goto v___jp_5606_;
}
}
}
}
}
else
{
lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5640_; 
lean_del_object(v___x_5570_);
v___x_5635_ = lean_nat_add(v___x_5574_, v_size_5576_);
lean_dec(v_size_5576_);
v___x_5636_ = lean_nat_add(v___x_5635_, v_size_5575_);
lean_dec(v___x_5635_);
v___x_5637_ = lean_nat_add(v___x_5574_, v_size_5575_);
v___x_5638_ = lean_nat_add(v___x_5637_, v_size_5593_);
lean_dec(v___x_5637_);
lean_inc_ref(v_r_5568_);
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 4, v_r_5568_);
lean_ctor_set(v___x_5590_, 3, v_r_5580_);
lean_ctor_set(v___x_5590_, 2, v_v_5566_);
lean_ctor_set(v___x_5590_, 1, v_k_5565_);
lean_ctor_set(v___x_5590_, 0, v___x_5638_);
v___x_5640_ = v___x_5590_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5653_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5653_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5653_, 3, v_r_5580_);
lean_ctor_set(v_reuseFailAlloc_5653_, 4, v_r_5568_);
v___x_5640_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
v_isSharedCheck_5647_ = !lean_is_exclusive(v_r_5568_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; lean_object* v_unused_5649_; lean_object* v_unused_5650_; lean_object* v_unused_5651_; lean_object* v_unused_5652_; 
v_unused_5648_ = lean_ctor_get(v_r_5568_, 4);
lean_dec(v_unused_5648_);
v_unused_5649_ = lean_ctor_get(v_r_5568_, 3);
lean_dec(v_unused_5649_);
v_unused_5650_ = lean_ctor_get(v_r_5568_, 2);
lean_dec(v_unused_5650_);
v_unused_5651_ = lean_ctor_get(v_r_5568_, 1);
lean_dec(v_unused_5651_);
v_unused_5652_ = lean_ctor_get(v_r_5568_, 0);
lean_dec(v_unused_5652_);
v___x_5642_ = v_r_5568_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_dec(v_r_5568_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
lean_ctor_set(v___x_5642_, 4, v___x_5640_);
lean_ctor_set(v___x_5642_, 3, v_l_5579_);
lean_ctor_set(v___x_5642_, 2, v_v_5578_);
lean_ctor_set(v___x_5642_, 1, v_k_5577_);
lean_ctor_set(v___x_5642_, 0, v___x_5636_);
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5636_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_k_5577_);
lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_v_5578_);
lean_ctor_set(v_reuseFailAlloc_5646_, 3, v_l_5579_);
lean_ctor_set(v_reuseFailAlloc_5646_, 4, v___x_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5660_; 
v_l_5660_ = lean_ctor_get(v_impl_5573_, 3);
lean_inc(v_l_5660_);
if (lean_obj_tag(v_l_5660_) == 0)
{
lean_object* v_r_5661_; lean_object* v_k_5662_; lean_object* v_v_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5674_; 
v_r_5661_ = lean_ctor_get(v_impl_5573_, 4);
v_k_5662_ = lean_ctor_get(v_impl_5573_, 1);
v_v_5663_ = lean_ctor_get(v_impl_5573_, 2);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_impl_5573_);
if (v_isSharedCheck_5674_ == 0)
{
lean_object* v_unused_5675_; lean_object* v_unused_5676_; 
v_unused_5675_ = lean_ctor_get(v_impl_5573_, 3);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_impl_5573_, 0);
lean_dec(v_unused_5676_);
v___x_5665_ = v_impl_5573_;
v_isShared_5666_ = v_isSharedCheck_5674_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_r_5661_);
lean_inc(v_v_5663_);
lean_inc(v_k_5662_);
lean_dec(v_impl_5573_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5674_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5667_; lean_object* v___x_5669_; 
v___x_5667_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5661_);
if (v_isShared_5666_ == 0)
{
lean_ctor_set(v___x_5665_, 3, v_r_5661_);
lean_ctor_set(v___x_5665_, 2, v_v_5566_);
lean_ctor_set(v___x_5665_, 1, v_k_5565_);
lean_ctor_set(v___x_5665_, 0, v___x_5574_);
v___x_5669_ = v___x_5665_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5673_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5673_, 3, v_r_5661_);
lean_ctor_set(v_reuseFailAlloc_5673_, 4, v_r_5661_);
v___x_5669_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5671_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v___x_5669_);
lean_ctor_set(v___x_5570_, 3, v_l_5660_);
lean_ctor_set(v___x_5570_, 2, v_v_5663_);
lean_ctor_set(v___x_5570_, 1, v_k_5662_);
lean_ctor_set(v___x_5570_, 0, v___x_5667_);
v___x_5671_ = v___x_5570_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5667_);
lean_ctor_set(v_reuseFailAlloc_5672_, 1, v_k_5662_);
lean_ctor_set(v_reuseFailAlloc_5672_, 2, v_v_5663_);
lean_ctor_set(v_reuseFailAlloc_5672_, 3, v_l_5660_);
lean_ctor_set(v_reuseFailAlloc_5672_, 4, v___x_5669_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
else
{
lean_object* v_r_5677_; 
v_r_5677_ = lean_ctor_get(v_impl_5573_, 4);
lean_inc(v_r_5677_);
if (lean_obj_tag(v_r_5677_) == 0)
{
lean_object* v_k_5678_; lean_object* v_v_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5702_; 
v_k_5678_ = lean_ctor_get(v_impl_5573_, 1);
v_v_5679_ = lean_ctor_get(v_impl_5573_, 2);
v_isSharedCheck_5702_ = !lean_is_exclusive(v_impl_5573_);
if (v_isSharedCheck_5702_ == 0)
{
lean_object* v_unused_5703_; lean_object* v_unused_5704_; lean_object* v_unused_5705_; 
v_unused_5703_ = lean_ctor_get(v_impl_5573_, 4);
lean_dec(v_unused_5703_);
v_unused_5704_ = lean_ctor_get(v_impl_5573_, 3);
lean_dec(v_unused_5704_);
v_unused_5705_ = lean_ctor_get(v_impl_5573_, 0);
lean_dec(v_unused_5705_);
v___x_5681_ = v_impl_5573_;
v_isShared_5682_ = v_isSharedCheck_5702_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_v_5679_);
lean_inc(v_k_5678_);
lean_dec(v_impl_5573_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5702_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v_k_5683_; lean_object* v_v_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5698_; 
v_k_5683_ = lean_ctor_get(v_r_5677_, 1);
v_v_5684_ = lean_ctor_get(v_r_5677_, 2);
v_isSharedCheck_5698_ = !lean_is_exclusive(v_r_5677_);
if (v_isSharedCheck_5698_ == 0)
{
lean_object* v_unused_5699_; lean_object* v_unused_5700_; lean_object* v_unused_5701_; 
v_unused_5699_ = lean_ctor_get(v_r_5677_, 4);
lean_dec(v_unused_5699_);
v_unused_5700_ = lean_ctor_get(v_r_5677_, 3);
lean_dec(v_unused_5700_);
v_unused_5701_ = lean_ctor_get(v_r_5677_, 0);
lean_dec(v_unused_5701_);
v___x_5686_ = v_r_5677_;
v_isShared_5687_ = v_isSharedCheck_5698_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_v_5684_);
lean_inc(v_k_5683_);
lean_dec(v_r_5677_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5698_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5688_; lean_object* v___x_5690_; 
v___x_5688_ = lean_unsigned_to_nat(3u);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 4, v_l_5660_);
lean_ctor_set(v___x_5686_, 3, v_l_5660_);
lean_ctor_set(v___x_5686_, 2, v_v_5679_);
lean_ctor_set(v___x_5686_, 1, v_k_5678_);
lean_ctor_set(v___x_5686_, 0, v___x_5574_);
v___x_5690_ = v___x_5686_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5697_, 1, v_k_5678_);
lean_ctor_set(v_reuseFailAlloc_5697_, 2, v_v_5679_);
lean_ctor_set(v_reuseFailAlloc_5697_, 3, v_l_5660_);
lean_ctor_set(v_reuseFailAlloc_5697_, 4, v_l_5660_);
v___x_5690_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5692_; 
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_l_5660_);
lean_ctor_set(v___x_5681_, 2, v_v_5566_);
lean_ctor_set(v___x_5681_, 1, v_k_5565_);
lean_ctor_set(v___x_5681_, 0, v___x_5574_);
v___x_5692_ = v___x_5681_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5696_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5696_, 3, v_l_5660_);
lean_ctor_set(v_reuseFailAlloc_5696_, 4, v_l_5660_);
v___x_5692_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5694_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v___x_5692_);
lean_ctor_set(v___x_5570_, 3, v___x_5690_);
lean_ctor_set(v___x_5570_, 2, v_v_5684_);
lean_ctor_set(v___x_5570_, 1, v_k_5683_);
lean_ctor_set(v___x_5570_, 0, v___x_5688_);
v___x_5694_ = v___x_5570_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5688_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v_k_5683_);
lean_ctor_set(v_reuseFailAlloc_5695_, 2, v_v_5684_);
lean_ctor_set(v_reuseFailAlloc_5695_, 3, v___x_5690_);
lean_ctor_set(v_reuseFailAlloc_5695_, 4, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
}
else
{
lean_object* v___x_5706_; lean_object* v___x_5708_; 
v___x_5706_ = lean_unsigned_to_nat(2u);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_r_5677_);
lean_ctor_set(v___x_5570_, 3, v_impl_5573_);
lean_ctor_set(v___x_5570_, 0, v___x_5706_);
v___x_5708_ = v___x_5570_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5706_);
lean_ctor_set(v_reuseFailAlloc_5709_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5709_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5709_, 3, v_impl_5573_);
lean_ctor_set(v_reuseFailAlloc_5709_, 4, v_r_5677_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
}
}
case 1:
{
lean_object* v___x_5711_; 
lean_dec(v_v_5566_);
lean_dec(v_k_5565_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 2, v_v_5562_);
lean_ctor_set(v___x_5570_, 1, v_k_5561_);
v___x_5711_ = v___x_5570_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_size_5564_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v_k_5561_);
lean_ctor_set(v_reuseFailAlloc_5712_, 2, v_v_5562_);
lean_ctor_set(v_reuseFailAlloc_5712_, 3, v_l_5567_);
lean_ctor_set(v_reuseFailAlloc_5712_, 4, v_r_5568_);
v___x_5711_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
return v___x_5711_;
}
}
default: 
{
lean_object* v_impl_5713_; lean_object* v___x_5714_; 
lean_dec(v_size_5564_);
v_impl_5713_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(v_k_5561_, v_v_5562_, v_r_5568_);
v___x_5714_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5567_) == 0)
{
lean_object* v_size_5715_; lean_object* v_size_5716_; lean_object* v_k_5717_; lean_object* v_v_5718_; lean_object* v_l_5719_; lean_object* v_r_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; uint8_t v___x_5723_; 
v_size_5715_ = lean_ctor_get(v_l_5567_, 0);
v_size_5716_ = lean_ctor_get(v_impl_5713_, 0);
lean_inc(v_size_5716_);
v_k_5717_ = lean_ctor_get(v_impl_5713_, 1);
lean_inc(v_k_5717_);
v_v_5718_ = lean_ctor_get(v_impl_5713_, 2);
lean_inc(v_v_5718_);
v_l_5719_ = lean_ctor_get(v_impl_5713_, 3);
lean_inc(v_l_5719_);
v_r_5720_ = lean_ctor_get(v_impl_5713_, 4);
lean_inc(v_r_5720_);
v___x_5721_ = lean_unsigned_to_nat(3u);
v___x_5722_ = lean_nat_mul(v___x_5721_, v_size_5715_);
v___x_5723_ = lean_nat_dec_lt(v___x_5722_, v_size_5716_);
lean_dec(v___x_5722_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5727_; 
lean_dec(v_r_5720_);
lean_dec(v_l_5719_);
lean_dec(v_v_5718_);
lean_dec(v_k_5717_);
v___x_5724_ = lean_nat_add(v___x_5714_, v_size_5715_);
v___x_5725_ = lean_nat_add(v___x_5724_, v_size_5716_);
lean_dec(v_size_5716_);
lean_dec(v___x_5724_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_impl_5713_);
lean_ctor_set(v___x_5570_, 0, v___x_5725_);
v___x_5727_ = v___x_5570_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5725_);
lean_ctor_set(v_reuseFailAlloc_5728_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5728_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5728_, 3, v_l_5567_);
lean_ctor_set(v_reuseFailAlloc_5728_, 4, v_impl_5713_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
else
{
lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5792_; 
v_isSharedCheck_5792_ = !lean_is_exclusive(v_impl_5713_);
if (v_isSharedCheck_5792_ == 0)
{
lean_object* v_unused_5793_; lean_object* v_unused_5794_; lean_object* v_unused_5795_; lean_object* v_unused_5796_; lean_object* v_unused_5797_; 
v_unused_5793_ = lean_ctor_get(v_impl_5713_, 4);
lean_dec(v_unused_5793_);
v_unused_5794_ = lean_ctor_get(v_impl_5713_, 3);
lean_dec(v_unused_5794_);
v_unused_5795_ = lean_ctor_get(v_impl_5713_, 2);
lean_dec(v_unused_5795_);
v_unused_5796_ = lean_ctor_get(v_impl_5713_, 1);
lean_dec(v_unused_5796_);
v_unused_5797_ = lean_ctor_get(v_impl_5713_, 0);
lean_dec(v_unused_5797_);
v___x_5730_ = v_impl_5713_;
v_isShared_5731_ = v_isSharedCheck_5792_;
goto v_resetjp_5729_;
}
else
{
lean_dec(v_impl_5713_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5792_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v_size_5732_; lean_object* v_k_5733_; lean_object* v_v_5734_; lean_object* v_l_5735_; lean_object* v_r_5736_; lean_object* v_size_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; uint8_t v___x_5740_; 
v_size_5732_ = lean_ctor_get(v_l_5719_, 0);
v_k_5733_ = lean_ctor_get(v_l_5719_, 1);
v_v_5734_ = lean_ctor_get(v_l_5719_, 2);
v_l_5735_ = lean_ctor_get(v_l_5719_, 3);
v_r_5736_ = lean_ctor_get(v_l_5719_, 4);
v_size_5737_ = lean_ctor_get(v_r_5720_, 0);
v___x_5738_ = lean_unsigned_to_nat(2u);
v___x_5739_ = lean_nat_mul(v___x_5738_, v_size_5737_);
v___x_5740_ = lean_nat_dec_lt(v_size_5732_, v___x_5739_);
lean_dec(v___x_5739_);
if (v___x_5740_ == 0)
{
lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5768_; 
lean_inc(v_r_5736_);
lean_inc(v_l_5735_);
lean_inc(v_v_5734_);
lean_inc(v_k_5733_);
v_isSharedCheck_5768_ = !lean_is_exclusive(v_l_5719_);
if (v_isSharedCheck_5768_ == 0)
{
lean_object* v_unused_5769_; lean_object* v_unused_5770_; lean_object* v_unused_5771_; lean_object* v_unused_5772_; lean_object* v_unused_5773_; 
v_unused_5769_ = lean_ctor_get(v_l_5719_, 4);
lean_dec(v_unused_5769_);
v_unused_5770_ = lean_ctor_get(v_l_5719_, 3);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_l_5719_, 2);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_l_5719_, 1);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_l_5719_, 0);
lean_dec(v_unused_5773_);
v___x_5742_ = v_l_5719_;
v_isShared_5743_ = v_isSharedCheck_5768_;
goto v_resetjp_5741_;
}
else
{
lean_dec(v_l_5719_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5768_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5758_; 
v___x_5744_ = lean_nat_add(v___x_5714_, v_size_5715_);
v___x_5745_ = lean_nat_add(v___x_5744_, v_size_5716_);
lean_dec(v_size_5716_);
if (lean_obj_tag(v_l_5735_) == 0)
{
lean_object* v_size_5766_; 
v_size_5766_ = lean_ctor_get(v_l_5735_, 0);
lean_inc(v_size_5766_);
v___y_5758_ = v_size_5766_;
goto v___jp_5757_;
}
else
{
lean_object* v___x_5767_; 
v___x_5767_ = lean_unsigned_to_nat(0u);
v___y_5758_ = v___x_5767_;
goto v___jp_5757_;
}
v___jp_5746_:
{
lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5750_ = lean_nat_add(v___y_5748_, v___y_5749_);
lean_dec(v___y_5749_);
lean_dec(v___y_5748_);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 4, v_r_5720_);
lean_ctor_set(v___x_5742_, 3, v_r_5736_);
lean_ctor_set(v___x_5742_, 2, v_v_5718_);
lean_ctor_set(v___x_5742_, 1, v_k_5717_);
lean_ctor_set(v___x_5742_, 0, v___x_5750_);
v___x_5752_ = v___x_5742_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v_k_5717_);
lean_ctor_set(v_reuseFailAlloc_5756_, 2, v_v_5718_);
lean_ctor_set(v_reuseFailAlloc_5756_, 3, v_r_5736_);
lean_ctor_set(v_reuseFailAlloc_5756_, 4, v_r_5720_);
v___x_5752_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
lean_object* v___x_5754_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 4, v___x_5752_);
lean_ctor_set(v___x_5730_, 3, v___y_5747_);
lean_ctor_set(v___x_5730_, 2, v_v_5734_);
lean_ctor_set(v___x_5730_, 1, v_k_5733_);
lean_ctor_set(v___x_5730_, 0, v___x_5745_);
v___x_5754_ = v___x_5730_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5745_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v_k_5733_);
lean_ctor_set(v_reuseFailAlloc_5755_, 2, v_v_5734_);
lean_ctor_set(v_reuseFailAlloc_5755_, 3, v___y_5747_);
lean_ctor_set(v_reuseFailAlloc_5755_, 4, v___x_5752_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
v___jp_5757_:
{
lean_object* v___x_5759_; lean_object* v___x_5761_; 
v___x_5759_ = lean_nat_add(v___x_5744_, v___y_5758_);
lean_dec(v___y_5758_);
lean_dec(v___x_5744_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_l_5735_);
lean_ctor_set(v___x_5570_, 0, v___x_5759_);
v___x_5761_ = v___x_5570_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5759_);
lean_ctor_set(v_reuseFailAlloc_5765_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5765_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5765_, 3, v_l_5567_);
lean_ctor_set(v_reuseFailAlloc_5765_, 4, v_l_5735_);
v___x_5761_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
lean_object* v___x_5762_; 
v___x_5762_ = lean_nat_add(v___x_5714_, v_size_5737_);
if (lean_obj_tag(v_r_5736_) == 0)
{
lean_object* v_size_5763_; 
v_size_5763_ = lean_ctor_get(v_r_5736_, 0);
lean_inc(v_size_5763_);
v___y_5747_ = v___x_5761_;
v___y_5748_ = v___x_5762_;
v___y_5749_ = v_size_5763_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_5764_; 
v___x_5764_ = lean_unsigned_to_nat(0u);
v___y_5747_ = v___x_5761_;
v___y_5748_ = v___x_5762_;
v___y_5749_ = v___x_5764_;
goto v___jp_5746_;
}
}
}
}
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5778_; 
lean_del_object(v___x_5570_);
v___x_5774_ = lean_nat_add(v___x_5714_, v_size_5715_);
v___x_5775_ = lean_nat_add(v___x_5774_, v_size_5716_);
lean_dec(v_size_5716_);
v___x_5776_ = lean_nat_add(v___x_5774_, v_size_5732_);
lean_dec(v___x_5774_);
lean_inc_ref(v_l_5567_);
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 4, v_l_5719_);
lean_ctor_set(v___x_5730_, 3, v_l_5567_);
lean_ctor_set(v___x_5730_, 2, v_v_5566_);
lean_ctor_set(v___x_5730_, 1, v_k_5565_);
lean_ctor_set(v___x_5730_, 0, v___x_5776_);
v___x_5778_ = v___x_5730_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5791_, 3, v_l_5567_);
lean_ctor_set(v_reuseFailAlloc_5791_, 4, v_l_5719_);
v___x_5778_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
v_isSharedCheck_5785_ = !lean_is_exclusive(v_l_5567_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; lean_object* v_unused_5787_; lean_object* v_unused_5788_; lean_object* v_unused_5789_; lean_object* v_unused_5790_; 
v_unused_5786_ = lean_ctor_get(v_l_5567_, 4);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_l_5567_, 3);
lean_dec(v_unused_5787_);
v_unused_5788_ = lean_ctor_get(v_l_5567_, 2);
lean_dec(v_unused_5788_);
v_unused_5789_ = lean_ctor_get(v_l_5567_, 1);
lean_dec(v_unused_5789_);
v_unused_5790_ = lean_ctor_get(v_l_5567_, 0);
lean_dec(v_unused_5790_);
v___x_5780_ = v_l_5567_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_dec(v_l_5567_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
lean_ctor_set(v___x_5780_, 4, v_r_5720_);
lean_ctor_set(v___x_5780_, 3, v___x_5778_);
lean_ctor_set(v___x_5780_, 2, v_v_5718_);
lean_ctor_set(v___x_5780_, 1, v_k_5717_);
lean_ctor_set(v___x_5780_, 0, v___x_5775_);
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_k_5717_);
lean_ctor_set(v_reuseFailAlloc_5784_, 2, v_v_5718_);
lean_ctor_set(v_reuseFailAlloc_5784_, 3, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5784_, 4, v_r_5720_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5798_; 
v_l_5798_ = lean_ctor_get(v_impl_5713_, 3);
lean_inc(v_l_5798_);
if (lean_obj_tag(v_l_5798_) == 0)
{
lean_object* v_r_5799_; lean_object* v_k_5800_; lean_object* v_v_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5824_; 
v_r_5799_ = lean_ctor_get(v_impl_5713_, 4);
v_k_5800_ = lean_ctor_get(v_impl_5713_, 1);
v_v_5801_ = lean_ctor_get(v_impl_5713_, 2);
v_isSharedCheck_5824_ = !lean_is_exclusive(v_impl_5713_);
if (v_isSharedCheck_5824_ == 0)
{
lean_object* v_unused_5825_; lean_object* v_unused_5826_; 
v_unused_5825_ = lean_ctor_get(v_impl_5713_, 3);
lean_dec(v_unused_5825_);
v_unused_5826_ = lean_ctor_get(v_impl_5713_, 0);
lean_dec(v_unused_5826_);
v___x_5803_ = v_impl_5713_;
v_isShared_5804_ = v_isSharedCheck_5824_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_r_5799_);
lean_inc(v_v_5801_);
lean_inc(v_k_5800_);
lean_dec(v_impl_5713_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5824_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v_k_5805_; lean_object* v_v_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5820_; 
v_k_5805_ = lean_ctor_get(v_l_5798_, 1);
v_v_5806_ = lean_ctor_get(v_l_5798_, 2);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_l_5798_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; lean_object* v_unused_5822_; lean_object* v_unused_5823_; 
v_unused_5821_ = lean_ctor_get(v_l_5798_, 4);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_l_5798_, 3);
lean_dec(v_unused_5822_);
v_unused_5823_ = lean_ctor_get(v_l_5798_, 0);
lean_dec(v_unused_5823_);
v___x_5808_ = v_l_5798_;
v_isShared_5809_ = v_isSharedCheck_5820_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_v_5806_);
lean_inc(v_k_5805_);
lean_dec(v_l_5798_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5820_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v___x_5810_; lean_object* v___x_5812_; 
v___x_5810_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5799_, 2);
if (v_isShared_5809_ == 0)
{
lean_ctor_set(v___x_5808_, 4, v_r_5799_);
lean_ctor_set(v___x_5808_, 3, v_r_5799_);
lean_ctor_set(v___x_5808_, 2, v_v_5566_);
lean_ctor_set(v___x_5808_, 1, v_k_5565_);
lean_ctor_set(v___x_5808_, 0, v___x_5714_);
v___x_5812_ = v___x_5808_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5819_, 3, v_r_5799_);
lean_ctor_set(v_reuseFailAlloc_5819_, 4, v_r_5799_);
v___x_5812_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
lean_object* v___x_5814_; 
lean_inc(v_r_5799_);
if (v_isShared_5804_ == 0)
{
lean_ctor_set(v___x_5803_, 3, v_r_5799_);
lean_ctor_set(v___x_5803_, 0, v___x_5714_);
v___x_5814_ = v___x_5803_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_k_5800_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_v_5801_);
lean_ctor_set(v_reuseFailAlloc_5818_, 3, v_r_5799_);
lean_ctor_set(v_reuseFailAlloc_5818_, 4, v_r_5799_);
v___x_5814_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5816_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v___x_5814_);
lean_ctor_set(v___x_5570_, 3, v___x_5812_);
lean_ctor_set(v___x_5570_, 2, v_v_5806_);
lean_ctor_set(v___x_5570_, 1, v_k_5805_);
lean_ctor_set(v___x_5570_, 0, v___x_5810_);
v___x_5816_ = v___x_5570_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5810_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v_k_5805_);
lean_ctor_set(v_reuseFailAlloc_5817_, 2, v_v_5806_);
lean_ctor_set(v_reuseFailAlloc_5817_, 3, v___x_5812_);
lean_ctor_set(v_reuseFailAlloc_5817_, 4, v___x_5814_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
}
}
}
else
{
lean_object* v_r_5827_; 
v_r_5827_ = lean_ctor_get(v_impl_5713_, 4);
lean_inc(v_r_5827_);
if (lean_obj_tag(v_r_5827_) == 0)
{
lean_object* v_k_5828_; lean_object* v_v_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5840_; 
v_k_5828_ = lean_ctor_get(v_impl_5713_, 1);
v_v_5829_ = lean_ctor_get(v_impl_5713_, 2);
v_isSharedCheck_5840_ = !lean_is_exclusive(v_impl_5713_);
if (v_isSharedCheck_5840_ == 0)
{
lean_object* v_unused_5841_; lean_object* v_unused_5842_; lean_object* v_unused_5843_; 
v_unused_5841_ = lean_ctor_get(v_impl_5713_, 4);
lean_dec(v_unused_5841_);
v_unused_5842_ = lean_ctor_get(v_impl_5713_, 3);
lean_dec(v_unused_5842_);
v_unused_5843_ = lean_ctor_get(v_impl_5713_, 0);
lean_dec(v_unused_5843_);
v___x_5831_ = v_impl_5713_;
v_isShared_5832_ = v_isSharedCheck_5840_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_v_5829_);
lean_inc(v_k_5828_);
lean_dec(v_impl_5713_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5840_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5833_; lean_object* v___x_5835_; 
v___x_5833_ = lean_unsigned_to_nat(3u);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 4, v_l_5798_);
lean_ctor_set(v___x_5831_, 2, v_v_5566_);
lean_ctor_set(v___x_5831_, 1, v_k_5565_);
lean_ctor_set(v___x_5831_, 0, v___x_5714_);
v___x_5835_ = v___x_5831_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5839_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5839_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5839_, 3, v_l_5798_);
lean_ctor_set(v_reuseFailAlloc_5839_, 4, v_l_5798_);
v___x_5835_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
lean_object* v___x_5837_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_r_5827_);
lean_ctor_set(v___x_5570_, 3, v___x_5835_);
lean_ctor_set(v___x_5570_, 2, v_v_5829_);
lean_ctor_set(v___x_5570_, 1, v_k_5828_);
lean_ctor_set(v___x_5570_, 0, v___x_5833_);
v___x_5837_ = v___x_5570_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5833_);
lean_ctor_set(v_reuseFailAlloc_5838_, 1, v_k_5828_);
lean_ctor_set(v_reuseFailAlloc_5838_, 2, v_v_5829_);
lean_ctor_set(v_reuseFailAlloc_5838_, 3, v___x_5835_);
lean_ctor_set(v_reuseFailAlloc_5838_, 4, v_r_5827_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
}
else
{
lean_object* v___x_5844_; lean_object* v___x_5846_; 
v___x_5844_ = lean_unsigned_to_nat(2u);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 4, v_impl_5713_);
lean_ctor_set(v___x_5570_, 3, v_r_5827_);
lean_ctor_set(v___x_5570_, 0, v___x_5844_);
v___x_5846_ = v___x_5570_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5844_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v_k_5565_);
lean_ctor_set(v_reuseFailAlloc_5847_, 2, v_v_5566_);
lean_ctor_set(v_reuseFailAlloc_5847_, 3, v_r_5827_);
lean_ctor_set(v_reuseFailAlloc_5847_, 4, v_impl_5713_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
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
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = lean_unsigned_to_nat(1u);
v___x_5850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5850_, 0, v___x_5849_);
lean_ctor_set(v___x_5850_, 1, v_k_5561_);
lean_ctor_set(v___x_5850_, 2, v_v_5562_);
lean_ctor_set(v___x_5850_, 3, v_t_5563_);
lean_ctor_set(v___x_5850_, 4, v_t_5563_);
return v___x_5850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5(lean_object* v_rendering_5851_, lean_object* v_as_5852_, size_t v_sz_5853_, size_t v_i_5854_, lean_object* v_b_5855_){
_start:
{
uint8_t v___x_5856_; 
v___x_5856_ = lean_usize_dec_lt(v_i_5854_, v_sz_5853_);
if (v___x_5856_ == 0)
{
return v_b_5855_;
}
else
{
lean_object* v_a_5857_; lean_object* v_fst_5858_; lean_object* v_snd_5859_; lean_object* v_r_5860_; size_t v___x_5861_; size_t v___x_5862_; 
v_a_5857_ = lean_array_uget_borrowed(v_as_5852_, v_i_5854_);
v_fst_5858_ = lean_ctor_get(v_a_5857_, 0);
v_snd_5859_ = lean_ctor_get(v_a_5857_, 1);
lean_inc(v_snd_5859_);
lean_inc(v_fst_5858_);
v_r_5860_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(v_fst_5858_, v_snd_5859_, v_b_5855_);
v___x_5861_ = ((size_t)1ULL);
v___x_5862_ = lean_usize_add(v_i_5854_, v___x_5861_);
v_i_5854_ = v___x_5862_;
v_b_5855_ = v_r_5860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5___boxed(lean_object* v_rendering_5864_, lean_object* v_as_5865_, lean_object* v_sz_5866_, lean_object* v_i_5867_, lean_object* v_b_5868_){
_start:
{
size_t v_sz_boxed_5869_; size_t v_i_boxed_5870_; lean_object* v_res_5871_; 
v_sz_boxed_5869_ = lean_unbox_usize(v_sz_5866_);
lean_dec(v_sz_5866_);
v_i_boxed_5870_ = lean_unbox_usize(v_i_5867_);
lean_dec(v_i_5867_);
v_res_5871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5(v_rendering_5864_, v_as_5865_, v_sz_boxed_5869_, v_i_boxed_5870_, v_b_5868_);
lean_dec_ref(v_as_5865_);
lean_dec_ref(v_rendering_5864_);
return v_res_5871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3(size_t v_sz_5872_, size_t v_i_5873_, lean_object* v_bs_5874_){
_start:
{
uint8_t v___x_5875_; 
v___x_5875_ = lean_usize_dec_lt(v_i_5873_, v_sz_5872_);
if (v___x_5875_ == 0)
{
return v_bs_5874_;
}
else
{
lean_object* v_v_5876_; lean_object* v_fst_5877_; lean_object* v_snd_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5892_; 
v_v_5876_ = lean_array_uget(v_bs_5874_, v_i_5873_);
v_fst_5877_ = lean_ctor_get(v_v_5876_, 0);
v_snd_5878_ = lean_ctor_get(v_v_5876_, 1);
v_isSharedCheck_5892_ = !lean_is_exclusive(v_v_5876_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5880_ = v_v_5876_;
v_isShared_5881_ = v_isSharedCheck_5892_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_snd_5878_);
lean_inc(v_fst_5877_);
lean_dec(v_v_5876_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5892_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5882_; lean_object* v_bs_x27_5883_; lean_object* v___x_5884_; lean_object* v___x_5886_; 
v___x_5882_ = lean_unsigned_to_nat(0u);
v_bs_x27_5883_ = lean_array_uset(v_bs_5874_, v_i_5873_, v___x_5882_);
v___x_5884_ = l_Array_reverse___redArg(v_snd_5878_);
if (v_isShared_5881_ == 0)
{
lean_ctor_set(v___x_5880_, 1, v___x_5884_);
v___x_5886_ = v___x_5880_;
goto v_reusejp_5885_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_fst_5877_);
lean_ctor_set(v_reuseFailAlloc_5891_, 1, v___x_5884_);
v___x_5886_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5885_;
}
v_reusejp_5885_:
{
size_t v___x_5887_; size_t v___x_5888_; lean_object* v___x_5889_; 
v___x_5887_ = ((size_t)1ULL);
v___x_5888_ = lean_usize_add(v_i_5873_, v___x_5887_);
v___x_5889_ = lean_array_uset(v_bs_x27_5883_, v_i_5873_, v___x_5886_);
v_i_5873_ = v___x_5888_;
v_bs_5874_ = v___x_5889_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3___boxed(lean_object* v_sz_5893_, lean_object* v_i_5894_, lean_object* v_bs_5895_){
_start:
{
size_t v_sz_boxed_5896_; size_t v_i_boxed_5897_; lean_object* v_res_5898_; 
v_sz_boxed_5896_ = lean_unbox_usize(v_sz_5893_);
lean_dec(v_sz_5893_);
v_i_boxed_5897_ = lean_unbox_usize(v_i_5894_);
lean_dec(v_i_5894_);
v_res_5898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3(v_sz_boxed_5896_, v_i_boxed_5897_, v_bs_5895_);
return v_res_5898_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0(void){
_start:
{
lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; 
v___x_5899_ = lean_box(0);
v___x_5900_ = lean_unsigned_to_nat(16u);
v___x_5901_ = lean_mk_array(v___x_5900_, v___x_5899_);
return v___x_5901_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v_r_5904_; 
v___x_5902_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__0);
v___x_5903_ = lean_unsigned_to_nat(0u);
v_r_5904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_r_5904_, 0, v___x_5903_);
lean_ctor_set(v_r_5904_, 1, v___x_5902_);
return v_r_5904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions(lean_object* v_rendering_5905_, lean_object* v_maxColumnWidth_5906_, lean_object* v_comments_5907_){
_start:
{
lean_object* v___y_5909_; lean_object* v___y_5910_; lean_object* v___y_5911_; lean_object* v___y_5912_; lean_object* v___y_5917_; lean_object* v___y_5925_; lean_object* v_size_5941_; lean_object* v_buckets_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5979_; 
v_size_5941_ = lean_ctor_get(v_comments_5907_, 0);
v_buckets_5942_ = lean_ctor_get(v_comments_5907_, 1);
v_isSharedCheck_5979_ = !lean_is_exclusive(v_comments_5907_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5944_ = v_comments_5907_;
v_isShared_5945_ = v_isSharedCheck_5979_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_buckets_5942_);
lean_inc(v_size_5941_);
lean_dec(v_comments_5907_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5979_;
goto v_resetjp_5943_;
}
v___jp_5908_:
{
uint8_t v___x_5913_; 
v___x_5913_ = lean_nat_dec_le(v___y_5912_, v___y_5911_);
if (v___x_5913_ == 0)
{
lean_object* v___x_5914_; 
lean_dec(v___y_5911_);
lean_inc(v___y_5912_);
v___x_5914_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(v_rendering_5905_, v___y_5910_, v___y_5909_, v___y_5912_, v___y_5912_);
lean_dec(v___y_5912_);
lean_dec(v___y_5910_);
lean_dec_ref(v_rendering_5905_);
return v___x_5914_;
}
else
{
lean_object* v___x_5915_; 
v___x_5915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(v_rendering_5905_, v___y_5910_, v___y_5909_, v___y_5912_, v___y_5911_);
lean_dec(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec_ref(v_rendering_5905_);
return v___x_5915_;
}
}
v___jp_5916_:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; uint8_t v___x_5920_; 
v___x_5918_ = lean_array_get_size(v___y_5917_);
v___x_5919_ = lean_unsigned_to_nat(0u);
v___x_5920_ = lean_nat_dec_eq(v___x_5918_, v___x_5919_);
if (v___x_5920_ == 0)
{
lean_object* v___x_5921_; lean_object* v___x_5922_; uint8_t v___x_5923_; 
v___x_5921_ = lean_unsigned_to_nat(1u);
v___x_5922_ = lean_nat_sub(v___x_5918_, v___x_5921_);
v___x_5923_ = lean_nat_dec_le(v___x_5919_, v___x_5922_);
if (v___x_5923_ == 0)
{
lean_inc(v___x_5922_);
v___y_5909_ = v___y_5917_;
v___y_5910_ = v___x_5918_;
v___y_5911_ = v___x_5922_;
v___y_5912_ = v___x_5922_;
goto v___jp_5908_;
}
else
{
v___y_5909_ = v___y_5917_;
v___y_5910_ = v___x_5918_;
v___y_5911_ = v___x_5922_;
v___y_5912_ = v___x_5919_;
goto v___jp_5908_;
}
}
else
{
lean_dec_ref(v_rendering_5905_);
return v___y_5917_;
}
}
v___jp_5924_:
{
lean_object* v_snd_5926_; lean_object* v_snd_5927_; lean_object* v_size_5928_; lean_object* v_buckets_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; uint8_t v___x_5933_; 
v_snd_5926_ = lean_ctor_get(v___y_5925_, 1);
lean_inc(v_snd_5926_);
lean_dec_ref(v___y_5925_);
v_snd_5927_ = lean_ctor_get(v_snd_5926_, 1);
lean_inc(v_snd_5927_);
lean_dec(v_snd_5926_);
v_size_5928_ = lean_ctor_get(v_snd_5927_, 0);
lean_inc(v_size_5928_);
v_buckets_5929_ = lean_ctor_get(v_snd_5927_, 1);
lean_inc_ref(v_buckets_5929_);
lean_dec(v_snd_5927_);
v___x_5930_ = lean_mk_empty_array_with_capacity(v_size_5928_);
lean_dec(v_size_5928_);
v___x_5931_ = lean_unsigned_to_nat(0u);
v___x_5932_ = lean_array_get_size(v_buckets_5929_);
v___x_5933_ = lean_nat_dec_lt(v___x_5931_, v___x_5932_);
if (v___x_5933_ == 0)
{
lean_dec_ref(v_buckets_5929_);
v___y_5917_ = v___x_5930_;
goto v___jp_5916_;
}
else
{
uint8_t v___x_5934_; 
v___x_5934_ = lean_nat_dec_le(v___x_5932_, v___x_5932_);
if (v___x_5934_ == 0)
{
if (v___x_5933_ == 0)
{
lean_dec_ref(v_buckets_5929_);
v___y_5917_ = v___x_5930_;
goto v___jp_5916_;
}
else
{
size_t v___x_5935_; size_t v___x_5936_; lean_object* v___x_5937_; 
v___x_5935_ = ((size_t)0ULL);
v___x_5936_ = lean_usize_of_nat(v___x_5932_);
v___x_5937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2(v_buckets_5929_, v___x_5935_, v___x_5936_, v___x_5930_);
lean_dec_ref(v_buckets_5929_);
v___y_5917_ = v___x_5937_;
goto v___jp_5916_;
}
}
else
{
size_t v___x_5938_; size_t v___x_5939_; lean_object* v___x_5940_; 
v___x_5938_ = ((size_t)0ULL);
v___x_5939_ = lean_usize_of_nat(v___x_5932_);
v___x_5940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__2(v_buckets_5929_, v___x_5938_, v___x_5939_, v___x_5930_);
lean_dec_ref(v_buckets_5929_);
v___y_5917_ = v___x_5940_;
goto v___jp_5916_;
}
}
}
v_resetjp_5943_:
{
lean_object* v_lineInfos_5946_; lean_object* v___y_5948_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; uint8_t v___x_5971_; 
v_lineInfos_5946_ = l_Lean_Fmt_collectLineInfos(v_rendering_5905_);
v___x_5968_ = lean_mk_empty_array_with_capacity(v_size_5941_);
lean_dec(v_size_5941_);
v___x_5969_ = lean_unsigned_to_nat(0u);
v___x_5970_ = lean_array_get_size(v_buckets_5942_);
v___x_5971_ = lean_nat_dec_lt(v___x_5969_, v___x_5970_);
if (v___x_5971_ == 0)
{
lean_dec_ref(v_buckets_5942_);
v___y_5948_ = v___x_5968_;
goto v___jp_5947_;
}
else
{
uint8_t v___x_5972_; 
v___x_5972_ = lean_nat_dec_le(v___x_5970_, v___x_5970_);
if (v___x_5972_ == 0)
{
if (v___x_5971_ == 0)
{
lean_dec_ref(v_buckets_5942_);
v___y_5948_ = v___x_5968_;
goto v___jp_5947_;
}
else
{
size_t v___x_5973_; size_t v___x_5974_; lean_object* v___x_5975_; 
v___x_5973_ = ((size_t)0ULL);
v___x_5974_ = lean_usize_of_nat(v___x_5970_);
v___x_5975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15(v_buckets_5942_, v___x_5973_, v___x_5974_, v___x_5968_);
lean_dec_ref(v_buckets_5942_);
v___y_5948_ = v___x_5975_;
goto v___jp_5947_;
}
}
else
{
size_t v___x_5976_; size_t v___x_5977_; lean_object* v___x_5978_; 
v___x_5976_ = ((size_t)0ULL);
v___x_5977_ = lean_usize_of_nat(v___x_5970_);
v___x_5978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__15(v_buckets_5942_, v___x_5976_, v___x_5977_, v___x_5968_);
lean_dec_ref(v_buckets_5942_);
v___y_5948_ = v___x_5978_;
goto v___jp_5947_;
}
}
v___jp_5947_:
{
size_t v_sz_5949_; size_t v___x_5950_; lean_object* v_comments_5951_; lean_object* v_r_5952_; size_t v_sz_5953_; lean_object* v___x_5954_; size_t v_sz_5955_; lean_object* v_lineLengths_5956_; lean_object* v___x_5957_; uint8_t v___x_5958_; lean_object* v___x_5959_; lean_object* v_containsEndOfLineComments_5960_; lean_object* v_r_5961_; lean_object* v___x_5963_; 
v_sz_5949_ = lean_array_size(v___y_5948_);
v___x_5950_ = ((size_t)0ULL);
v_comments_5951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__3(v_sz_5949_, v___x_5950_, v___y_5948_);
v_r_5952_ = lean_box(1);
v_sz_5953_ = lean_array_size(v_comments_5951_);
v___x_5954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__5(v_rendering_5905_, v_comments_5951_, v_sz_5953_, v___x_5950_, v_r_5952_);
lean_dec_ref(v_comments_5951_);
v_sz_5955_ = lean_array_size(v_lineInfos_5946_);
lean_inc_ref(v_lineInfos_5946_);
v_lineLengths_5956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__6(v_sz_5955_, v___x_5950_, v_lineInfos_5946_);
v___x_5957_ = lean_array_get_size(v_lineInfos_5946_);
v___x_5958_ = 0;
v___x_5959_ = lean_box(v___x_5958_);
v_containsEndOfLineComments_5960_ = lean_mk_array(v___x_5957_, v___x_5959_);
v_r_5961_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___closed__1);
if (v_isShared_5945_ == 0)
{
lean_ctor_set(v___x_5944_, 1, v_r_5961_);
lean_ctor_set(v___x_5944_, 0, v_containsEndOfLineComments_5960_);
v___x_5963_ = v___x_5944_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v_containsEndOfLineComments_5960_);
lean_ctor_set(v_reuseFailAlloc_5967_, 1, v_r_5961_);
v___x_5963_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v_a_5966_; 
v___x_5964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5964_, 0, v_lineLengths_5956_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
lean_inc_ref(v_rendering_5905_);
v___x_5965_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__13(v_rendering_5905_, v_lineInfos_5946_, v_maxColumnWidth_5906_, v___x_5964_, v___x_5954_);
lean_dec_ref(v_lineInfos_5946_);
v_a_5966_ = lean_ctor_get(v___x_5965_, 0);
lean_inc(v_a_5966_);
lean_dec_ref(v___x_5965_);
v___y_5925_ = v_a_5966_;
goto v___jp_5924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions___boxed(lean_object* v_rendering_5980_, lean_object* v_maxColumnWidth_5981_, lean_object* v_comments_5982_){
_start:
{
lean_object* v_res_5983_; 
v_res_5983_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions(v_rendering_5980_, v_maxColumnWidth_5981_, v_comments_5982_);
lean_dec(v_maxColumnWidth_5981_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0(lean_object* v_rendering_5984_, lean_object* v_n_5985_, lean_object* v_as_5986_, lean_object* v_lo_5987_, lean_object* v_hi_5988_, lean_object* v_w_5989_, lean_object* v_hlo_5990_, lean_object* v_hhi_5991_){
_start:
{
lean_object* v___x_5992_; 
v___x_5992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___redArg(v_rendering_5984_, v_n_5985_, v_as_5986_, v_lo_5987_, v_hi_5988_);
return v___x_5992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0___boxed(lean_object* v_rendering_5993_, lean_object* v_n_5994_, lean_object* v_as_5995_, lean_object* v_lo_5996_, lean_object* v_hi_5997_, lean_object* v_w_5998_, lean_object* v_hlo_5999_, lean_object* v_hhi_6000_){
_start:
{
lean_object* v_res_6001_; 
v_res_6001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0(v_rendering_5993_, v_n_5994_, v_as_5995_, v_lo_5996_, v_hi_5997_, v_w_5998_, v_hlo_5999_, v_hhi_6000_);
lean_dec(v_hi_5997_);
lean_dec(v_n_5994_);
lean_dec_ref(v_rendering_5993_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4(lean_object* v_rendering_6002_, lean_object* v_00_u03b2_6003_, lean_object* v_k_6004_, lean_object* v_v_6005_, lean_object* v_t_6006_, lean_object* v_hl_6007_){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___redArg(v_k_6004_, v_v_6005_, v_t_6006_);
return v___x_6008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4___boxed(lean_object* v_rendering_6009_, lean_object* v_00_u03b2_6010_, lean_object* v_k_6011_, lean_object* v_v_6012_, lean_object* v_t_6013_, lean_object* v_hl_6014_){
_start:
{
lean_object* v_res_6015_; 
v_res_6015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__4(v_rendering_6009_, v_00_u03b2_6010_, v_k_6011_, v_v_6012_, v_t_6013_, v_hl_6014_);
lean_dec_ref(v_rendering_6009_);
return v_res_6015_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9(lean_object* v_rendering_6016_, lean_object* v_00_u03b2_6017_, lean_object* v_m_6018_, lean_object* v_a_6019_){
_start:
{
uint8_t v___x_6020_; 
v___x_6020_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___redArg(v_rendering_6016_, v_m_6018_, v_a_6019_);
return v___x_6020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9___boxed(lean_object* v_rendering_6021_, lean_object* v_00_u03b2_6022_, lean_object* v_m_6023_, lean_object* v_a_6024_){
_start:
{
uint8_t v_res_6025_; lean_object* v_r_6026_; 
v_res_6025_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__9(v_rendering_6021_, v_00_u03b2_6022_, v_m_6023_, v_a_6024_);
lean_dec(v_a_6024_);
lean_dec_ref(v_m_6023_);
lean_dec_ref(v_rendering_6021_);
v_r_6026_ = lean_box(v_res_6025_);
return v_r_6026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10(lean_object* v_rendering_6027_, lean_object* v_00_u03b2_6028_, lean_object* v_m_6029_, lean_object* v_a_6030_, lean_object* v_b_6031_){
_start:
{
lean_object* v___x_6032_; 
v___x_6032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___redArg(v_rendering_6027_, v_m_6029_, v_a_6030_, v_b_6031_);
return v___x_6032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10___boxed(lean_object* v_rendering_6033_, lean_object* v_00_u03b2_6034_, lean_object* v_m_6035_, lean_object* v_a_6036_, lean_object* v_b_6037_){
_start:
{
lean_object* v_res_6038_; 
v_res_6038_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10(v_rendering_6033_, v_00_u03b2_6034_, v_m_6035_, v_a_6036_, v_b_6037_);
lean_dec_ref(v_rendering_6033_);
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0(lean_object* v_rendering_6039_, lean_object* v_n_6040_, lean_object* v_lo_6041_, lean_object* v_hi_6042_, lean_object* v_hhi_6043_, lean_object* v_pivot_6044_, lean_object* v_as_6045_, lean_object* v_i_6046_, lean_object* v_k_6047_, lean_object* v_ilo_6048_, lean_object* v_ik_6049_, lean_object* v_w_6050_){
_start:
{
lean_object* v___x_6051_; 
v___x_6051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___redArg(v_hi_6042_, v_pivot_6044_, v_as_6045_, v_i_6046_, v_k_6047_);
return v___x_6051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0___boxed(lean_object* v_rendering_6052_, lean_object* v_n_6053_, lean_object* v_lo_6054_, lean_object* v_hi_6055_, lean_object* v_hhi_6056_, lean_object* v_pivot_6057_, lean_object* v_as_6058_, lean_object* v_i_6059_, lean_object* v_k_6060_, lean_object* v_ilo_6061_, lean_object* v_ik_6062_, lean_object* v_w_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__0_spec__0(v_rendering_6052_, v_n_6053_, v_lo_6054_, v_hi_6055_, v_hhi_6056_, v_pivot_6057_, v_as_6058_, v_i_6059_, v_k_6060_, v_ilo_6061_, v_ik_6062_, v_w_6063_);
lean_dec_ref(v_pivot_6057_);
lean_dec(v_hi_6055_);
lean_dec(v_lo_6054_);
lean_dec(v_n_6053_);
lean_dec_ref(v_rendering_6052_);
return v_res_6064_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9(lean_object* v_rendering_6065_, lean_object* v_00_u03b2_6066_, lean_object* v_a_6067_, lean_object* v_x_6068_){
_start:
{
uint8_t v___x_6069_; 
v___x_6069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___redArg(v_a_6067_, v_x_6068_);
return v___x_6069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9___boxed(lean_object* v_rendering_6070_, lean_object* v_00_u03b2_6071_, lean_object* v_a_6072_, lean_object* v_x_6073_){
_start:
{
uint8_t v_res_6074_; lean_object* v_r_6075_; 
v_res_6074_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__9(v_rendering_6070_, v_00_u03b2_6071_, v_a_6072_, v_x_6073_);
lean_dec(v_x_6073_);
lean_dec(v_a_6072_);
lean_dec_ref(v_rendering_6070_);
v_r_6075_ = lean_box(v_res_6074_);
return v_r_6075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10(lean_object* v_rendering_6076_, lean_object* v_00_u03b2_6077_, lean_object* v_data_6078_){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___redArg(v_rendering_6076_, v_data_6078_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10___boxed(lean_object* v_rendering_6080_, lean_object* v_00_u03b2_6081_, lean_object* v_data_6082_){
_start:
{
lean_object* v_res_6083_; 
v_res_6083_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10(v_rendering_6080_, v_00_u03b2_6081_, v_data_6082_);
lean_dec_ref(v_rendering_6080_);
return v_res_6083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11(lean_object* v_rendering_6084_, lean_object* v___x_6085_, lean_object* v_a_6086_, lean_object* v_x_6087_){
_start:
{
lean_object* v___x_6088_; 
v___x_6088_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___redArg(v___x_6085_, v_a_6086_, v_x_6087_);
return v___x_6088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11___boxed(lean_object* v_rendering_6089_, lean_object* v___x_6090_, lean_object* v_a_6091_, lean_object* v_x_6092_){
_start:
{
lean_object* v_res_6093_; 
v_res_6093_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__11(v_rendering_6089_, v___x_6090_, v_a_6091_, v_x_6092_);
lean_dec_ref(v_rendering_6089_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14(lean_object* v_rendering_6094_, lean_object* v_00_u03b2_6095_, lean_object* v_a_6096_, lean_object* v_b_6097_, lean_object* v_x_6098_){
_start:
{
lean_object* v___x_6099_; 
v___x_6099_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___redArg(v_a_6096_, v_b_6097_, v_x_6098_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14___boxed(lean_object* v_rendering_6100_, lean_object* v_00_u03b2_6101_, lean_object* v_a_6102_, lean_object* v_b_6103_, lean_object* v_x_6104_){
_start:
{
lean_object* v_res_6105_; 
v_res_6105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__10_spec__14(v_rendering_6100_, v_00_u03b2_6101_, v_a_6102_, v_b_6103_, v_x_6104_);
lean_dec_ref(v_rendering_6100_);
return v_res_6105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11(lean_object* v_rendering_6106_, lean_object* v_00_u03b2_6107_, lean_object* v_i_6108_, lean_object* v_source_6109_, lean_object* v_target_6110_){
_start:
{
lean_object* v___x_6111_; 
v___x_6111_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___redArg(v_rendering_6106_, v_i_6108_, v_source_6109_, v_target_6110_);
return v___x_6111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11___boxed(lean_object* v_rendering_6112_, lean_object* v_00_u03b2_6113_, lean_object* v_i_6114_, lean_object* v_source_6115_, lean_object* v_target_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11(v_rendering_6112_, v_00_u03b2_6113_, v_i_6114_, v_source_6115_, v_target_6116_);
lean_dec_ref(v_rendering_6112_);
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19(lean_object* v_00_u03b2_6118_, lean_object* v_rendering_6119_, lean_object* v_x_6120_, lean_object* v_x_6121_){
_start:
{
lean_object* v___x_6122_; 
v___x_6122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___redArg(v_x_6120_, v_x_6121_);
return v___x_6122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19___boxed(lean_object* v_00_u03b2_6123_, lean_object* v_rendering_6124_, lean_object* v_x_6125_, lean_object* v_x_6126_){
_start:
{
lean_object* v_res_6127_; 
v_res_6127_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions_spec__8_spec__10_spec__11_spec__19(v_00_u03b2_6123_, v_rendering_6124_, v_x_6125_, v_x_6126_);
lean_dec_ref(v_rendering_6124_);
return v_res_6127_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1(void){
_start:
{
uint32_t v___x_6128_; lean_object* v___x_6129_; 
v___x_6128_ = 65;
v___x_6129_ = lean_box_uint32(v___x_6128_);
return v___x_6129_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00Lean_Fmt_insertComments_spec__1(lean_object* v_msg_6130_){
_start:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; uint32_t v___x_6133_; 
v___x_6131_ = l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1;
v___x_6132_ = lean_panic_fn_borrowed(v___x_6131_, v_msg_6130_);
v___x_6133_ = lean_unbox_uint32(v___x_6132_);
lean_dec(v___x_6132_);
return v___x_6133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed(lean_object* v_msg_6134_){
_start:
{
uint32_t v_res_6135_; lean_object* v_r_6136_; 
v_res_6135_ = l_panic___at___00Lean_Fmt_insertComments_spec__1(v_msg_6134_);
v_r_6136_ = lean_box_uint32(v_res_6135_);
return v_r_6136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg(lean_object* v___x_6137_, lean_object* v_snd_6138_, lean_object* v_a_6139_, lean_object* v_b_6140_){
_start:
{
lean_object* v___x_6141_; uint8_t v___x_6142_; 
v___x_6141_ = lean_unsigned_to_nat(0u);
v___x_6142_ = lean_nat_dec_eq(v_a_6139_, v___x_6141_);
if (v___x_6142_ == 0)
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v_prevPos_6145_; uint32_t v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6143_ = lean_unsigned_to_nat(1u);
v___x_6144_ = lean_nat_sub(v_a_6139_, v___x_6143_);
v_prevPos_6145_ = l_String_Slice_posLE(v___x_6137_, v___x_6144_);
v___x_6146_ = lean_string_utf8_get_fast(v_snd_6138_, v_prevPos_6145_);
lean_dec(v_prevPos_6145_);
v___x_6147_ = lean_box_uint32(v___x_6146_);
v___x_6148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
return v___x_6148_;
}
else
{
lean_inc(v_b_6140_);
return v_b_6140_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg___boxed(lean_object* v___x_6149_, lean_object* v_snd_6150_, lean_object* v_a_6151_, lean_object* v_b_6152_){
_start:
{
lean_object* v_res_6153_; 
v_res_6153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg(v___x_6149_, v_snd_6150_, v_a_6151_, v_b_6152_);
lean_dec(v_b_6152_);
lean_dec(v_a_6151_);
lean_dec_ref(v_snd_6150_);
lean_dec_ref(v___x_6149_);
return v_res_6153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2(lean_object* v_rendering_6154_, lean_object* v_as_6155_, size_t v_sz_6156_, size_t v_i_6157_, lean_object* v_b_6158_){
_start:
{
uint8_t v___x_6159_; 
v___x_6159_ = lean_usize_dec_lt(v_i_6157_, v_sz_6156_);
if (v___x_6159_ == 0)
{
lean_dec_ref(v_rendering_6154_);
return v_b_6158_;
}
else
{
lean_object* v_a_6160_; lean_object* v_fst_6161_; lean_object* v_snd_6162_; lean_object* v___x_6164_; uint8_t v_isShared_6165_; uint8_t v_isSharedCheck_6234_; 
v_a_6160_ = lean_array_uget(v_as_6155_, v_i_6157_);
v_fst_6161_ = lean_ctor_get(v_a_6160_, 0);
v_snd_6162_ = lean_ctor_get(v_a_6160_, 1);
v_isSharedCheck_6234_ = !lean_is_exclusive(v_a_6160_);
if (v_isSharedCheck_6234_ == 0)
{
v___x_6164_ = v_a_6160_;
v_isShared_6165_ = v_isSharedCheck_6234_;
goto v_resetjp_6163_;
}
else
{
lean_inc(v_snd_6162_);
lean_inc(v_fst_6161_);
lean_dec(v_a_6160_);
v___x_6164_ = lean_box(0);
v_isShared_6165_ = v_isSharedCheck_6234_;
goto v_resetjp_6163_;
}
v_resetjp_6163_:
{
lean_object* v_r_6167_; lean_object* v_fst_6174_; lean_object* v_snd_6175_; lean_object* v___x_6176_; lean_object* v_str_6177_; lean_object* v_startInclusive_6178_; lean_object* v_endExclusive_6179_; lean_object* v___x_6181_; uint8_t v_isShared_6182_; uint8_t v_isSharedCheck_6233_; 
v_fst_6174_ = lean_ctor_get(v_b_6158_, 0);
lean_inc(v_fst_6174_);
v_snd_6175_ = lean_ctor_get(v_b_6158_, 1);
lean_inc(v_snd_6175_);
lean_dec_ref(v_b_6158_);
lean_inc_ref(v_rendering_6154_);
v___x_6176_ = l_String_Slice_slice_x21(v_rendering_6154_, v_snd_6175_, v_fst_6161_);
lean_dec(v_snd_6175_);
v_str_6177_ = lean_ctor_get(v___x_6176_, 0);
v_startInclusive_6178_ = lean_ctor_get(v___x_6176_, 1);
v_endExclusive_6179_ = lean_ctor_get(v___x_6176_, 2);
v_isSharedCheck_6233_ = !lean_is_exclusive(v___x_6176_);
if (v_isSharedCheck_6233_ == 0)
{
v___x_6181_ = v___x_6176_;
v_isShared_6182_ = v_isSharedCheck_6233_;
goto v_resetjp_6180_;
}
else
{
lean_inc(v_endExclusive_6179_);
lean_inc(v_startInclusive_6178_);
lean_inc(v_str_6177_);
lean_dec(v___x_6176_);
v___x_6181_ = lean_box(0);
v_isShared_6182_ = v_isSharedCheck_6233_;
goto v_resetjp_6180_;
}
v___jp_6166_:
{
lean_object* v___x_6169_; 
if (v_isShared_6165_ == 0)
{
lean_ctor_set(v___x_6164_, 1, v_fst_6161_);
lean_ctor_set(v___x_6164_, 0, v_r_6167_);
v___x_6169_ = v___x_6164_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6173_; 
v_reuseFailAlloc_6173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6173_, 0, v_r_6167_);
lean_ctor_set(v_reuseFailAlloc_6173_, 1, v_fst_6161_);
v___x_6169_ = v_reuseFailAlloc_6173_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
size_t v___x_6170_; size_t v___x_6171_; 
v___x_6170_ = ((size_t)1ULL);
v___x_6171_ = lean_usize_add(v_i_6157_, v___x_6170_);
v_i_6157_ = v___x_6171_;
v_b_6158_ = v___x_6169_;
goto _start;
}
}
v_resetjp_6180_:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; uint8_t v___y_6187_; lean_object* v___x_6190_; 
v___x_6183_ = lean_string_utf8_extract_fast(v_str_6177_, v_startInclusive_6178_, v_endExclusive_6179_);
lean_dec(v_endExclusive_6179_);
lean_dec(v_startInclusive_6178_);
lean_dec_ref(v_str_6177_);
v___x_6184_ = lean_string_append(v_fst_6174_, v___x_6183_);
lean_dec_ref(v___x_6183_);
v___x_6185_ = lean_string_append(v___x_6184_, v_snd_6162_);
v___x_6190_ = l_String_Slice_Pos_get_x3f(v_rendering_6154_, v_fst_6161_);
if (lean_obj_tag(v___x_6190_) == 1)
{
lean_object* v_val_6191_; uint8_t v___y_6193_; uint8_t v___y_6201_; uint32_t v___y_6209_; uint8_t v___y_6210_; uint32_t v___y_6216_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6224_; 
v_val_6191_ = lean_ctor_get(v___x_6190_, 0);
lean_inc(v_val_6191_);
lean_dec_ref_known(v___x_6190_, 1);
v___x_6221_ = lean_unsigned_to_nat(0u);
v___x_6222_ = lean_string_utf8_byte_size(v_snd_6162_);
lean_inc(v_snd_6162_);
if (v_isShared_6182_ == 0)
{
lean_ctor_set(v___x_6181_, 2, v___x_6222_);
lean_ctor_set(v___x_6181_, 1, v___x_6221_);
lean_ctor_set(v___x_6181_, 0, v_snd_6162_);
v___x_6224_ = v___x_6181_;
goto v_reusejp_6223_;
}
else
{
lean_object* v_reuseFailAlloc_6232_; 
v_reuseFailAlloc_6232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_snd_6162_);
lean_ctor_set(v_reuseFailAlloc_6232_, 1, v___x_6221_);
lean_ctor_set(v_reuseFailAlloc_6232_, 2, v___x_6222_);
v___x_6224_ = v_reuseFailAlloc_6232_;
goto v_reusejp_6223_;
}
v___jp_6192_:
{
if (v___y_6193_ == 0)
{
uint32_t v___x_6194_; uint32_t v___x_6195_; uint8_t v___x_6196_; 
v___x_6194_ = 13;
v___x_6195_ = lean_unbox_uint32(v_val_6191_);
v___x_6196_ = lean_uint32_dec_eq(v___x_6195_, v___x_6194_);
if (v___x_6196_ == 0)
{
uint32_t v___x_6197_; uint32_t v___x_6198_; uint8_t v___x_6199_; 
v___x_6197_ = 10;
v___x_6198_ = lean_unbox_uint32(v_val_6191_);
lean_dec(v_val_6191_);
v___x_6199_ = lean_uint32_dec_eq(v___x_6198_, v___x_6197_);
v___y_6187_ = v___x_6199_;
goto v___jp_6186_;
}
else
{
lean_dec(v_val_6191_);
v___y_6187_ = v___x_6196_;
goto v___jp_6186_;
}
}
else
{
lean_dec(v_val_6191_);
v_r_6167_ = v___x_6185_;
goto v___jp_6166_;
}
}
v___jp_6200_:
{
if (v___y_6201_ == 0)
{
uint32_t v___x_6202_; uint32_t v___x_6203_; uint8_t v___x_6204_; 
v___x_6202_ = 32;
v___x_6203_ = lean_unbox_uint32(v_val_6191_);
v___x_6204_ = lean_uint32_dec_eq(v___x_6203_, v___x_6202_);
if (v___x_6204_ == 0)
{
uint32_t v___x_6205_; uint32_t v___x_6206_; uint8_t v___x_6207_; 
v___x_6205_ = 9;
v___x_6206_ = lean_unbox_uint32(v_val_6191_);
v___x_6207_ = lean_uint32_dec_eq(v___x_6206_, v___x_6205_);
v___y_6193_ = v___x_6207_;
goto v___jp_6192_;
}
else
{
v___y_6193_ = v___x_6204_;
goto v___jp_6192_;
}
}
else
{
lean_dec(v_val_6191_);
v_r_6167_ = v___x_6185_;
goto v___jp_6166_;
}
}
v___jp_6208_:
{
if (v___y_6210_ == 0)
{
uint32_t v___x_6211_; uint8_t v___x_6212_; 
v___x_6211_ = 13;
v___x_6212_ = lean_uint32_dec_eq(v___y_6209_, v___x_6211_);
if (v___x_6212_ == 0)
{
uint32_t v___x_6213_; uint8_t v___x_6214_; 
v___x_6213_ = 10;
v___x_6214_ = lean_uint32_dec_eq(v___y_6209_, v___x_6213_);
v___y_6201_ = v___x_6214_;
goto v___jp_6200_;
}
else
{
v___y_6201_ = v___x_6212_;
goto v___jp_6200_;
}
}
else
{
lean_dec(v_val_6191_);
v_r_6167_ = v___x_6185_;
goto v___jp_6166_;
}
}
v___jp_6215_:
{
uint32_t v___x_6217_; uint8_t v___x_6218_; 
v___x_6217_ = 32;
v___x_6218_ = lean_uint32_dec_eq(v___y_6216_, v___x_6217_);
if (v___x_6218_ == 0)
{
uint32_t v___x_6219_; uint8_t v___x_6220_; 
v___x_6219_ = 9;
v___x_6220_ = lean_uint32_dec_eq(v___y_6216_, v___x_6219_);
v___y_6209_ = v___y_6216_;
v___y_6210_ = v___x_6220_;
goto v___jp_6208_;
}
else
{
v___y_6209_ = v___y_6216_;
v___y_6210_ = v___x_6218_;
goto v___jp_6208_;
}
}
v_reusejp_6223_:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6225_ = l_String_Slice_revPositions(v___x_6224_);
v___x_6226_ = lean_box(0);
v___x_6227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg(v___x_6224_, v_snd_6162_, v___x_6225_, v___x_6226_);
lean_dec(v___x_6225_);
lean_dec(v_snd_6162_);
lean_dec_ref(v___x_6224_);
if (lean_obj_tag(v___x_6227_) == 0)
{
lean_object* v___x_6228_; uint32_t v___x_6229_; 
v___x_6228_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3, &l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_parseComments_tryCloseComment___closed__3);
v___x_6229_ = l_panic___at___00Lean_Fmt_insertComments_spec__1(v___x_6228_);
v___y_6216_ = v___x_6229_;
goto v___jp_6215_;
}
else
{
lean_object* v_val_6230_; uint32_t v___x_6231_; 
v_val_6230_ = lean_ctor_get(v___x_6227_, 0);
lean_inc(v_val_6230_);
lean_dec_ref_known(v___x_6227_, 1);
v___x_6231_ = lean_unbox_uint32(v_val_6230_);
lean_dec(v_val_6230_);
v___y_6216_ = v___x_6231_;
goto v___jp_6215_;
}
}
}
else
{
lean_dec(v___x_6190_);
lean_del_object(v___x_6181_);
lean_dec(v_snd_6162_);
v_r_6167_ = v___x_6185_;
goto v___jp_6166_;
}
v___jp_6186_:
{
if (v___y_6187_ == 0)
{
lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00__private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_PendingComment_finalize_normalizeContent_spec__0___closed__0));
v___x_6189_ = lean_string_append(v___x_6185_, v___x_6188_);
v_r_6167_ = v___x_6189_;
goto v___jp_6166_;
}
else
{
v_r_6167_ = v___x_6185_;
goto v___jp_6166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2___boxed(lean_object* v_rendering_6235_, lean_object* v_as_6236_, lean_object* v_sz_6237_, lean_object* v_i_6238_, lean_object* v_b_6239_){
_start:
{
size_t v_sz_boxed_6240_; size_t v_i_boxed_6241_; lean_object* v_res_6242_; 
v_sz_boxed_6240_ = lean_unbox_usize(v_sz_6237_);
lean_dec(v_sz_6237_);
v_i_boxed_6241_ = lean_unbox_usize(v_i_6238_);
lean_dec(v_i_6238_);
v_res_6242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2(v_rendering_6235_, v_as_6236_, v_sz_boxed_6240_, v_i_boxed_6241_, v_b_6239_);
lean_dec_ref(v_as_6236_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_insertComments(lean_object* v_maxColumnWidth_6246_, lean_object* v_rendering_6247_, lean_object* v_syntaxToRendered_6248_, lean_object* v_comments_6249_){
_start:
{
lean_object* v_comments_6250_; lean_object* v_insertions_6251_; lean_object* v___x_6252_; size_t v_sz_6253_; size_t v___x_6254_; lean_object* v___x_6255_; lean_object* v_fst_6256_; lean_object* v_snd_6257_; lean_object* v_startInclusive_6258_; lean_object* v_endExclusive_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v_str_6262_; lean_object* v_startInclusive_6263_; lean_object* v_endExclusive_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
lean_inc_ref_n(v_rendering_6247_, 3);
v_comments_6250_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_reassociateComments(v_rendering_6247_, v_syntaxToRendered_6248_, v_comments_6249_);
v_insertions_6251_ = l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_determineCommentInsertions(v_rendering_6247_, v_maxColumnWidth_6246_, v_comments_6250_);
v___x_6252_ = ((lean_object*)(l_Lean_Fmt_insertComments___closed__0));
v_sz_6253_ = lean_array_size(v_insertions_6251_);
v___x_6254_ = ((size_t)0ULL);
v___x_6255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_insertComments_spec__2(v_rendering_6247_, v_insertions_6251_, v_sz_6253_, v___x_6254_, v___x_6252_);
lean_dec_ref(v_insertions_6251_);
v_fst_6256_ = lean_ctor_get(v___x_6255_, 0);
lean_inc(v_fst_6256_);
v_snd_6257_ = lean_ctor_get(v___x_6255_, 1);
lean_inc(v_snd_6257_);
lean_dec_ref(v___x_6255_);
v_startInclusive_6258_ = lean_ctor_get(v_rendering_6247_, 1);
v_endExclusive_6259_ = lean_ctor_get(v_rendering_6247_, 2);
v___x_6260_ = lean_nat_sub(v_endExclusive_6259_, v_startInclusive_6258_);
v___x_6261_ = l_String_Slice_slice_x21(v_rendering_6247_, v_snd_6257_, v___x_6260_);
lean_dec(v___x_6260_);
lean_dec(v_snd_6257_);
v_str_6262_ = lean_ctor_get(v___x_6261_, 0);
lean_inc_ref(v_str_6262_);
v_startInclusive_6263_ = lean_ctor_get(v___x_6261_, 1);
lean_inc(v_startInclusive_6263_);
v_endExclusive_6264_ = lean_ctor_get(v___x_6261_, 2);
lean_inc(v_endExclusive_6264_);
lean_dec_ref(v___x_6261_);
v___x_6265_ = lean_string_utf8_extract_fast(v_str_6262_, v_startInclusive_6263_, v_endExclusive_6264_);
lean_dec(v_endExclusive_6264_);
lean_dec(v_startInclusive_6263_);
lean_dec_ref(v_str_6262_);
v___x_6266_ = lean_string_append(v_fst_6256_, v___x_6265_);
lean_dec_ref(v___x_6265_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_insertComments___boxed(lean_object* v_maxColumnWidth_6267_, lean_object* v_rendering_6268_, lean_object* v_syntaxToRendered_6269_, lean_object* v_comments_6270_){
_start:
{
lean_object* v_res_6271_; 
v_res_6271_ = l_Lean_Fmt_insertComments(v_maxColumnWidth_6267_, v_rendering_6268_, v_syntaxToRendered_6269_, v_comments_6270_);
lean_dec_ref(v_comments_6270_);
lean_dec_ref(v_syntaxToRendered_6269_);
lean_dec(v_maxColumnWidth_6267_);
return v_res_6271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0(lean_object* v___x_6272_, lean_object* v_snd_6273_, lean_object* v_inst_6274_, lean_object* v_R_6275_, lean_object* v_a_6276_, lean_object* v_b_6277_, lean_object* v_c_6278_){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___redArg(v___x_6272_, v_snd_6273_, v_a_6276_, v_b_6277_);
return v___x_6279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0___boxed(lean_object* v___x_6280_, lean_object* v_snd_6281_, lean_object* v_inst_6282_, lean_object* v_R_6283_, lean_object* v_a_6284_, lean_object* v_b_6285_, lean_object* v_c_6286_){
_start:
{
lean_object* v_res_6287_; 
v_res_6287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_insertComments_spec__0(v___x_6280_, v_snd_6281_, v_inst_6282_, v_R_6283_, v_a_6284_, v_b_6285_, v_c_6286_);
lean_dec(v_b_6285_);
lean_dec(v_a_6284_);
lean_dec_ref(v_snd_6281_);
lean_dec_ref(v___x_6280_);
return v_res_6287_;
}
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_Comment_instInhabitedWhitespace_default = _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default();
l_Lean_Fmt_Comment_instInhabitedWhitespace = _init_l_Lean_Fmt_Comment_instInhabitedWhitespace();
l_Lean_Fmt_Comment_instInhabitedPlacement_default = _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default();
l_Lean_Fmt_Comment_instInhabitedPlacement = _init_l_Lean_Fmt_Comment_instInhabitedPlacement();
l_Lean_Fmt_Comment_instInhabitedKind_default = _init_l_Lean_Fmt_Comment_instInhabitedKind_default();
l_Lean_Fmt_Comment_instInhabitedKind = _init_l_Lean_Fmt_Comment_instInhabitedKind();
l_Lean_Fmt_instInhabitedComment_default = _init_l_Lean_Fmt_instInhabitedComment_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedComment_default);
l_Lean_Fmt_instInhabitedComment = _init_l_Lean_Fmt_instInhabitedComment();
lean_mark_persistent(l_Lean_Fmt_instInhabitedComment);
l_Lean_Fmt_instInhabitedPendingComment_default = _init_l_Lean_Fmt_instInhabitedPendingComment_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedPendingComment_default);
l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instInhabitedPendingComment = _init_l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instInhabitedPendingComment();
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Comments_0__Lean_Fmt_instInhabitedPendingComment);
l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1 = _init_l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1();
lean_mark_persistent(l_panic___at___00Lean_Fmt_insertComments_spec__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Control_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Comments(builtin);
}
#ifdef __cplusplus
}
#endif

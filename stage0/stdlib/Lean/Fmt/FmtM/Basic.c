// Lean compiler output
// Module: Lean.Fmt.FmtM.Basic
// Imports: public import Lean.Fmt.FmtM.Layouts import Lean.Fmt.Util.RangeTree import Lean.Fmt.Util.Basic import Lean.Fmt.FmtM.Comments import Init.Data import Lean.Language.Lean.Util
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_failure;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Fmt_getFmtProviders(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedError_default;
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Substring_Raw_splitOn(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object*);
lean_object* l_Lean_Syntax_getLeading_x3f(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
extern lean_object* l_instInhabitedRaw__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedComment_default;
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
uint64_t lean_uint64_of_nat(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Comment_render(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object*);
lean_object* l_Lean_Fmt_parseComments(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_quantifierFmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_space;
lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_break;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Lean_Fmt_instBEqDefaultCost_beq___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedState_default;
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_quantified(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object*, lean_object*, uint8_t);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_Fmt_conditionalFmtAttribute;
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_conditional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_getStxArg_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "A formatter for is partial and does not handle the full syntax of the kind it was registered for."};
static const lean_object* l_Lean_Fmt_getStxArg_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_getStxArg_x21___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_getStxArg_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_getStxArg_x21___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_getStxArg_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_getStxArg_x21___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.FmtM.Basic"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__0 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__0_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.getLineInfo!"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__1 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__1_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: lineInfo.startPos <= pos && pos <= lineInfo.endPos\n  "};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__2 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfo_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfo_x21___closed__3;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_getLineInfo_x21___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__4 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__4_value;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__5 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__5_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__6 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__6_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__7 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__7_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__8 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__8_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfo_x21___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfo_x21___closed__9;
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_getLineInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__0 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__0_value;
static const lean_string_object l_Lean_Fmt_getLineInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.getLineInfos"};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__1 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__1_value;
static const lean_string_object l_Lean_Fmt_getLineInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: ! lineInfos.isEmpty\n  "};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__2 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfos___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfos___closed__3;
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 191, 134, 190, 206, 60, 55, 123)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__12 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 7, 95, 84, 115, 124, 250)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 198, 251, 95, 67, 81, 118, 246)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 147, 100, 44, 136, 108, 159, 66)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colEq"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 155, 248, 3, 115, 223, 12, 139)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lineEq"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(11, 222, 52, 211, 142, 186, 26, 103)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppHardSpace"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 168, 190, 83, 177, 86, 113, 221)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ppAllowUngrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 209, 55, 154, 125, 240, 2)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ppHardLineUnlessUngrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value),LEAN_SCALAR_PTR_LITERAL(68, 165, 69, 201, 179, 176, 38, 97)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(36, 202, 249, 244, 227, 198, 135, 34)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppRealGroup"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value),LEAN_SCALAR_PTR_LITERAL(86, 184, 190, 137, 27, 87, 63, 174)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ppRealFill"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value),LEAN_SCALAR_PTR_LITERAL(21, 219, 143, 167, 248, 5, 230, 49)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ppDedentIfGrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value),LEAN_SCALAR_PTR_LITERAL(195, 164, 225, 181, 149, 187, 81, 113)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1 = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedQuantifierChain = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "_private.Lean.Fmt.FmtM.Basic.0.Lean.Fmt.quantifierChain"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid syntax position"};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "Input syntax to the formatter is malformed: invalid syntax position."};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtRawAsInSource___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_fmtRawAsInSource___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__3;
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "A choice node was not disambiguated by the elaborator:\n"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtInfixOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtInfixOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInfixOperator___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInfixOperator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtInfixOperator___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInfixOperator___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtChoiceNode"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 97, 186, 28, 58, 175, 99, 37)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "antiquot_splice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtAtomic"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 89, 152, 45, 219, 206, 174, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtInfixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 84, 102, 146, 118, 206, 223, 209)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtPostfixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 119, 87, 59, 92, 236, 3, 41)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtPrefixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 164, 120, 136, 13, 122, 50, 33)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtConditional___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtQuantifier___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "substring is invalid and cannot be converted to a slice"};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "Input syntax to the formatter is malformed: substring is invalid and cannot be converted to a slice."};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "missing token range"};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Input syntax to the formatter is malformed: missing token range."};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedTrailingGroup(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_fmtArrayLit___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtArrayLit___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Fmt.FmtM.Basic.0.Lean.Fmt.fmtSeq.applyPseudoDedented"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_fmtSeq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSeq___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(lean_object* v_as_1_, lean_object* v_i_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_i_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
lean_object* v___x_5_; 
lean_dec(v_i_2_);
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_i_2_, v_one_6_);
lean_dec(v_i_2_);
v___x_8_ = lean_array_fget_borrowed(v_as_1_, v_n_7_);
lean_inc(v___x_8_);
v___x_9_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v___x_8_);
if (lean_obj_tag(v___x_9_) == 0)
{
v_i_2_ = v_n_7_;
goto _start;
}
else
{
lean_dec(v_n_7_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(lean_object* v_stx_11_){
_start:
{
switch(lean_obj_tag(v_stx_11_))
{
case 0:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
case 1:
{
lean_object* v_args_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_args_13_ = lean_ctor_get(v_stx_11_, 2);
lean_inc_ref(v_args_13_);
lean_dec_ref_known(v_stx_11_, 3);
v___x_14_ = lean_array_get_size(v_args_13_);
v___x_15_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_args_13_, v___x_14_);
lean_dec_ref(v_args_13_);
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_stx_11_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg___boxed(lean_object* v_as_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_17_, v_i_18_);
lean_dec_ref(v_as_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(lean_object* v_as_20_, lean_object* v_i_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_20_, v_i_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___boxed(lean_object* v_as_24_, lean_object* v_i_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(v_as_24_, v_i_25_, v_a_26_);
lean_dec_ref(v_as_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(lean_object* v_stx_31_){
_start:
{
switch(lean_obj_tag(v_stx_31_))
{
case 0:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
case 1:
{
lean_object* v_args_33_; lean_object* v___x_34_; lean_object* v___x_35_; size_t v_sz_36_; size_t v___x_37_; lean_object* v___x_38_; lean_object* v_fst_39_; 
v_args_33_ = lean_ctor_get(v_stx_31_, 2);
lean_inc_ref(v_args_33_);
lean_dec_ref_known(v_stx_31_, 3);
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v_sz_36_ = lean_array_size(v_args_33_);
v___x_37_ = ((size_t)0ULL);
v___x_38_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_args_33_, v_sz_36_, v___x_37_, v___x_35_);
lean_dec_ref(v_args_33_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
lean_dec_ref(v___x_38_);
if (lean_obj_tag(v_fst_39_) == 0)
{
return v___x_34_;
}
else
{
lean_object* v_val_40_; 
v_val_40_ = lean_ctor_get(v_fst_39_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v_fst_39_, 1);
return v_val_40_;
}
}
default: 
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_stx_31_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(lean_object* v_as_42_, size_t v_sz_43_, size_t v_i_44_, lean_object* v_b_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_usize_dec_lt(v_i_44_, v_sz_43_);
if (v___x_46_ == 0)
{
lean_inc_ref(v_b_45_);
return v_b_45_;
}
else
{
lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
v_a_48_ = lean_array_uget_borrowed(v_as_42_, v_i_44_);
lean_inc(v_a_48_);
v___x_49_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_a_48_);
if (lean_obj_tag(v___x_49_) == 1)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_47_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; size_t v___x_53_; size_t v___x_54_; 
lean_dec(v___x_49_);
v___x_52_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_44_, v___x_53_);
v_i_44_ = v___x_54_;
v_b_45_ = v___x_52_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___boxed(lean_object* v_as_56_, lean_object* v_sz_57_, lean_object* v_i_58_, lean_object* v_b_59_){
_start:
{
size_t v_sz_boxed_60_; size_t v_i_boxed_61_; lean_object* v_res_62_; 
v_sz_boxed_60_ = lean_unbox_usize(v_sz_57_);
lean_dec(v_sz_57_);
v_i_boxed_61_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_as_56_, v_sz_boxed_60_, v_i_boxed_61_, v_b_59_);
lean_dec_ref(v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(lean_object* v_a_63_){
_start:
{
lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_105_; 
v_fst_64_ = lean_ctor_get(v_a_63_, 0);
v_snd_65_ = lean_ctor_get(v_a_63_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_105_ == 0)
{
v___x_67_ = v_a_63_;
v_isShared_68_ = v_isSharedCheck_105_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_snd_65_);
lean_inc(v_fst_64_);
lean_dec(v_a_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_105_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint32_t v___y_70_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_lt(v___x_98_, v_snd_65_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_del_object(v___x_67_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_fst_64_);
lean_ctor_set(v___x_100_, 1, v_snd_65_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = l_String_Slice_Pos_get_x3f(v_fst_64_, v___x_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
uint32_t v___x_102_; 
v___x_102_ = 65;
v___y_70_ = v___x_102_;
goto v___jp_69_;
}
else
{
lean_object* v_val_103_; uint32_t v___x_104_; 
v_val_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_101_, 1);
v___x_104_ = lean_unbox_uint32(v_val_103_);
lean_dec(v_val_103_);
v___y_70_ = v___x_104_;
goto v___jp_69_;
}
}
v___jp_69_:
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 32;
v___x_72_ = lean_uint32_dec_eq(v___y_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_74_; 
if (v_isShared_68_ == 0)
{
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_snd_65_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v_str_76_; lean_object* v_startInclusive_77_; lean_object* v_endExclusive_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_94_; 
v_str_76_ = lean_ctor_get(v_fst_64_, 0);
lean_inc_ref(v_str_76_);
v_startInclusive_77_ = lean_ctor_get(v_fst_64_, 1);
lean_inc(v_startInclusive_77_);
v_endExclusive_78_ = lean_ctor_get(v_fst_64_, 2);
lean_inc(v_endExclusive_78_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_String_Slice_Pos_nextn(v_fst_64_, v___x_80_, v___x_79_);
v_isSharedCheck_94_ = !lean_is_exclusive(v_fst_64_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; 
v_unused_95_ = lean_ctor_get(v_fst_64_, 2);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_fst_64_, 1);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_fst_64_, 0);
lean_dec(v_unused_97_);
v___x_83_ = v_fst_64_;
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_fst_64_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_nat_add(v_startInclusive_77_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v_startInclusive_77_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___x_85_);
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_str_76_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_endExclusive_78_);
v___x_87_ = v_reuseFailAlloc_93_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_nat_sub(v_snd_65_, v___x_79_);
lean_dec(v_snd_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_88_);
lean_ctor_set(v___x_67_, 0, v___x_87_);
v___x_90_ = v___x_67_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
v_a_63_ = v___x_90_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(lean_object* v_line_106_, lean_object* v_numSpaces_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_fst_110_; 
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_line_106_);
lean_ctor_set(v___x_108_, 1, v_numSpaces_107_);
v___x_109_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v___x_108_);
v_fst_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_fst_110_);
lean_dec_ref(v___x_109_);
return v_fst_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0(lean_object* v_inst_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v_a_112_);
return v___x_113_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0));
v___x_116_ = lean_string_utf8_byte_size(v___x_115_);
return v___x_116_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1);
v___x_119_ = lean_nat_dec_eq(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__1);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0));
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3);
v___x_125_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__4);
v___x_128_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__3);
v___x_129_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
lean_ctor_set(v___x_129_, 3, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__5);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object* v_s_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__2);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__6);
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__8));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object* v_s_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v_s_142_);
lean_dec_ref(v_s_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object* v_numSpaces_144_, lean_object* v_s_145_, lean_object* v___x_146_, lean_object* v___x_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v_it_151_; lean_object* v_startInclusive_152_; lean_object* v_endExclusive_153_; 
if (lean_obj_tag(v_a_148_) == 0)
{
lean_object* v_currPos_159_; lean_object* v_searcher_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_264_; 
v_currPos_159_ = lean_ctor_get(v_a_148_, 0);
v_searcher_160_ = lean_ctor_get(v_a_148_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_a_148_);
if (v_isSharedCheck_264_ == 0)
{
v___x_162_ = v_a_148_;
v_isShared_163_ = v_isSharedCheck_264_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_searcher_160_);
lean_inc(v_currPos_159_);
lean_dec(v_a_148_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_264_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_it_165_; lean_object* v_it_171_; lean_object* v_startPos_172_; lean_object* v_endPos_173_; 
switch(lean_obj_tag(v_searcher_160_))
{
case 0:
{
lean_object* v_pos_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_198_; 
lean_del_object(v___x_162_);
v_pos_186_ = lean_ctor_get(v_searcher_160_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v_searcher_160_);
if (v_isSharedCheck_198_ == 0)
{
v___x_188_ = v_searcher_160_;
v_isShared_189_ = v_isSharedCheck_198_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_pos_186_);
lean_dec(v_searcher_160_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_198_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_startInclusive_190_; lean_object* v_endExclusive_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_startInclusive_190_ = lean_ctor_get(v___x_146_, 1);
v_endExclusive_191_ = lean_ctor_get(v___x_146_, 2);
v___x_192_ = lean_nat_sub(v_endExclusive_191_, v_startInclusive_190_);
v___x_193_ = lean_nat_dec_eq(v_pos_186_, v___x_192_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; 
lean_inc(v_pos_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
v___x_195_ = v___x_188_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_pos_186_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_inc(v_pos_186_);
v_it_171_ = v___x_195_;
v_startPos_172_ = v_pos_186_;
v_endPos_173_ = v_pos_186_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_197_; 
lean_del_object(v___x_188_);
v___x_197_ = lean_box(3);
lean_inc(v_pos_186_);
v_it_171_ = v___x_197_;
v_startPos_172_ = v_pos_186_;
v_endPos_173_ = v_pos_186_;
goto v___jp_170_;
}
}
}
case 1:
{
lean_object* v_pos_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_pos_199_ = lean_ctor_get(v_searcher_160_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_searcher_160_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v_searcher_160_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_pos_199_);
lean_dec(v_searcher_160_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_string_utf8_next_fast(v_s_145_, v_pos_199_);
lean_dec(v_pos_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 0);
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v_it_165_ = v___x_205_;
goto v___jp_164_;
}
}
}
case 2:
{
lean_object* v_needle_208_; lean_object* v_table_209_; lean_object* v_stackPos_210_; lean_object* v_needlePos_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_263_; 
v_needle_208_ = lean_ctor_get(v_searcher_160_, 0);
v_table_209_ = lean_ctor_get(v_searcher_160_, 1);
v_stackPos_210_ = lean_ctor_get(v_searcher_160_, 2);
v_needlePos_211_ = lean_ctor_get(v_searcher_160_, 3);
v_isSharedCheck_263_ = !lean_is_exclusive(v_searcher_160_);
if (v_isSharedCheck_263_ == 0)
{
v___x_213_ = v_searcher_160_;
v_isShared_214_ = v_isSharedCheck_263_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_needlePos_211_);
lean_inc(v_stackPos_210_);
lean_inc(v_table_209_);
lean_inc(v_needle_208_);
lean_dec(v_searcher_160_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_263_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_str_215_; lean_object* v_startInclusive_216_; lean_object* v_endExclusive_217_; lean_object* v_basePos_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_str_215_ = lean_ctor_get(v_needle_208_, 0);
v_startInclusive_216_ = lean_ctor_get(v_needle_208_, 1);
v_endExclusive_217_ = lean_ctor_get(v_needle_208_, 2);
v_basePos_218_ = lean_nat_sub(v_stackPos_210_, v_needlePos_211_);
v___x_219_ = lean_nat_sub(v_endExclusive_217_, v_startInclusive_216_);
v___x_220_ = lean_nat_add(v_basePos_218_, v___x_219_);
v___x_221_ = lean_nat_dec_le(v___x_220_, v___x_147_);
lean_dec(v___x_220_);
if (v___x_221_ == 0)
{
uint8_t v___x_222_; 
lean_dec(v___x_219_);
lean_del_object(v___x_213_);
lean_dec(v_needlePos_211_);
lean_dec(v_stackPos_210_);
lean_dec_ref(v_table_209_);
lean_dec_ref(v_needle_208_);
v___x_222_ = lean_nat_dec_lt(v_basePos_218_, v___x_147_);
lean_dec(v_basePos_218_);
if (v___x_222_ == 0)
{
lean_del_object(v___x_162_);
goto v___jp_184_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(3);
v_it_165_ = v___x_223_;
goto v___jp_164_;
}
}
else
{
uint8_t v_stackByte_224_; lean_object* v___x_225_; uint8_t v_patByte_226_; uint8_t v___x_227_; 
lean_dec(v_basePos_218_);
lean_inc(v_stackPos_210_);
v_stackByte_224_ = lean_string_get_byte_fast(v_s_145_, v_stackPos_210_);
v___x_225_ = lean_nat_add(v_startInclusive_216_, v_needlePos_211_);
v_patByte_226_ = lean_string_get_byte_fast(v_str_215_, v___x_225_);
v___x_227_ = lean_uint8_dec_eq(v_stackByte_224_, v_patByte_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; uint8_t v___x_229_; 
lean_dec(v___x_219_);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_nat_dec_eq(v_needlePos_211_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_newNeedlePos_232_; uint8_t v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_sub(v_needlePos_211_, v___x_230_);
lean_dec(v_needlePos_211_);
v_newNeedlePos_232_ = lean_array_fget_borrowed(v_table_209_, v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = lean_nat_dec_eq(v_newNeedlePos_232_, v___x_228_);
if (v___x_233_ == 0)
{
lean_object* v___x_235_; 
lean_inc(v_newNeedlePos_232_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v_newNeedlePos_232_);
v___x_235_ = v___x_213_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_needle_208_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_table_209_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_stackPos_210_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_newNeedlePos_232_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v_it_165_ = v___x_235_;
goto v___jp_164_;
}
}
else
{
lean_object* v_nextStackPos_237_; lean_object* v___x_239_; 
v_nextStackPos_237_ = l_String_Slice_posGE___redArg(v___x_146_, v_stackPos_210_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v___x_228_);
lean_ctor_set(v___x_213_, 2, v_nextStackPos_237_);
v___x_239_ = v___x_213_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_needle_208_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_table_209_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_nextStackPos_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v___x_228_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v_it_165_ = v___x_239_;
goto v___jp_164_;
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_nextStackPos_243_; lean_object* v___x_245_; 
lean_dec(v_needlePos_211_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_stackPos_210_, v___x_241_);
lean_dec(v_stackPos_210_);
v_nextStackPos_243_ = l_String_Slice_posGE___redArg(v___x_146_, v___x_242_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v___x_228_);
lean_ctor_set(v___x_213_, 2, v_nextStackPos_243_);
v___x_245_ = v___x_213_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_needle_208_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_table_209_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_nextStackPos_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v___x_228_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v_it_165_ = v___x_245_;
goto v___jp_164_;
}
}
}
else
{
lean_object* v___x_247_; lean_object* v_nextStackPos_248_; lean_object* v_nextNeedlePos_249_; uint8_t v___x_250_; 
lean_del_object(v___x_162_);
v___x_247_ = lean_unsigned_to_nat(1u);
v_nextStackPos_248_ = lean_nat_add(v_stackPos_210_, v___x_247_);
lean_dec(v_stackPos_210_);
v_nextNeedlePos_249_ = lean_nat_add(v_needlePos_211_, v___x_247_);
lean_dec(v_needlePos_211_);
v___x_250_ = lean_nat_dec_eq(v_nextNeedlePos_249_, v___x_219_);
lean_dec(v___x_219_);
if (v___x_250_ == 0)
{
lean_object* v___x_252_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v_nextNeedlePos_249_);
lean_ctor_set(v___x_213_, 2, v_nextStackPos_248_);
v___x_252_ = v___x_213_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_needle_208_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_table_209_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_nextStackPos_248_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_nextNeedlePos_249_);
v___x_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_currPos_159_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v_a_148_ = v___x_253_;
goto _start;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_256_ = lean_nat_sub(v_nextStackPos_248_, v_nextNeedlePos_249_);
lean_dec(v_nextNeedlePos_249_);
v___x_257_ = l_String_Slice_pos_x21(v___x_146_, v___x_256_);
lean_dec(v___x_256_);
v___x_258_ = l_String_Slice_pos_x21(v___x_146_, v_nextStackPos_248_);
v___x_259_ = lean_unsigned_to_nat(0u);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v___x_259_);
lean_ctor_set(v___x_213_, 2, v_nextStackPos_248_);
v___x_261_ = v___x_213_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_needle_208_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_table_209_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_nextStackPos_248_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
v_it_171_ = v___x_261_;
v_startPos_172_ = v___x_257_;
v_endPos_173_ = v___x_258_;
goto v___jp_170_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_162_);
goto v___jp_184_;
}
}
v___jp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v_it_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_currPos_159_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_it_165_);
v___x_167_ = v_reuseFailAlloc_169_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_a_148_ = v___x_167_;
goto _start;
}
}
v___jp_170_:
{
lean_object* v_slice_174_; lean_object* v_startInclusive_175_; lean_object* v_endExclusive_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_slice_174_ = l_String_Slice_subslice_x21(v___x_146_, v_currPos_159_, v_startPos_172_);
v_startInclusive_175_ = lean_ctor_get(v_slice_174_, 0);
v_endExclusive_176_ = lean_ctor_get(v_slice_174_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_slice_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v_slice_174_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_endExclusive_176_);
lean_inc(v_startInclusive_175_);
lean_dec(v_slice_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_nextIt_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_it_171_);
lean_ctor_set(v___x_178_, 0, v_endPos_173_);
v_nextIt_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_endPos_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_it_171_);
v_nextIt_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_it_151_ = v_nextIt_181_;
v_startInclusive_152_ = v_startInclusive_175_;
v_endExclusive_153_ = v_endExclusive_176_;
goto v___jp_150_;
}
}
}
v___jp_184_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(1);
lean_inc(v___x_147_);
v_it_151_ = v___x_185_;
v_startInclusive_152_ = v_currPos_159_;
v_endExclusive_153_ = v___x_147_;
goto v___jp_150_;
}
}
}
else
{
lean_dec(v___x_147_);
lean_dec_ref(v_s_145_);
lean_dec(v_numSpaces_144_);
return v_b_149_;
}
v___jp_150_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc_ref(v_s_145_);
v___x_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_154_, 0, v_s_145_);
lean_ctor_set(v___x_154_, 1, v_startInclusive_152_);
lean_ctor_set(v___x_154_, 2, v_endExclusive_153_);
lean_inc(v_numSpaces_144_);
v___x_155_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(v___x_154_, v_numSpaces_144_);
v___x_156_ = l_String_Slice_toString(v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = lean_array_push(v_b_149_, v___x_156_);
v_a_148_ = v_it_151_;
v_b_149_ = v___x_157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object* v_numSpaces_265_, lean_object* v_s_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_265_, v_s_266_, v___x_267_, v___x_268_, v_a_269_, v_b_270_);
lean_dec_ref(v___x_267_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object* v_s_274_, lean_object* v_numSpaces_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_276_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0));
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_string_utf8_byte_size(v_s_274_);
lean_inc_ref(v_s_274_);
v___x_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_279_, 0, v_s_274_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
lean_ctor_set(v___x_279_, 2, v___x_278_);
v___x_280_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v___x_279_);
v___x_281_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0));
v___x_282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_275_, v_s_274_, v___x_279_, v___x_278_, v___x_280_, v___x_281_);
lean_dec_ref_known(v___x_279_, 3);
v___x_283_ = lean_array_to_list(v___x_282_);
v___x_284_ = l_String_intercalate(v___x_276_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object* v_numSpaces_285_, lean_object* v_s_286_, lean_object* v___x_287_, lean_object* v___x_288_, lean_object* v_inst_289_, lean_object* v_R_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_285_, v_s_286_, v___x_287_, v___x_288_, v_a_291_, v_b_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object* v_numSpaces_294_, lean_object* v_s_295_, lean_object* v___x_296_, lean_object* v___x_297_, lean_object* v_inst_298_, lean_object* v_R_299_, lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(v_numSpaces_294_, v_s_295_, v___x_296_, v___x_297_, v_inst_298_, v_R_299_, v_a_300_, v_b_301_);
lean_dec_ref(v___x_296_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object* v_value_303_, lean_object* v_s_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_s_304_);
lean_ctor_set(v___x_305_, 1, v_value_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object* v_00_u03b1_306_, lean_object* v_value_307_, lean_object* v_s_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_s_308_);
lean_ctor_set(v___x_309_, 1, v_value_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_unsigned_to_nat(16u);
v___x_312_ = lean_mk_array(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__0, &l_Lean_FmtM_run___redArg___closed__0_once, _init_l_Lean_FmtM_run___redArg___closed__0);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l_Lean_ShareCommon_objectFactory;
v___x_317_ = l_ShareCommon_mkStateImpl(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__2, &l_Lean_FmtM_run___redArg___closed__2_once, _init_l_Lean_FmtM_run___redArg___closed__2);
v___x_320_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__1, &l_Lean_FmtM_run___redArg___closed__1_once, _init_l_Lean_FmtM_run___redArg___closed__1);
v___x_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_318_);
lean_ctor_set(v___x_321_, 3, v___x_320_);
lean_ctor_set(v___x_321_, 4, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object* v_ctx_322_, lean_object* v_act_323_){
_start:
{
lean_object* v___x_324_; lean_object* v_r_325_; 
v___x_324_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__3, &l_Lean_FmtM_run___redArg___closed__3_once, _init_l_Lean_FmtM_run___redArg___closed__3);
v_r_325_ = lean_apply_2(v_act_323_, v_ctx_322_, v___x_324_);
if (lean_obj_tag(v_r_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_326_ = lean_ctor_get(v_r_325_, 0);
v_a_327_ = lean_ctor_get(v_r_325_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_r_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v_r_325_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_inc(v_a_326_);
lean_dec(v_r_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_a_326_);
lean_ctor_set(v___x_329_, 0, v_a_327_);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_327_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_326_);
v___x_332_ = v_reuseFailAlloc_334_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v_r_325_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v_r_325_, 2);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_a_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object* v_00_u03b1_338_, lean_object* v_ctx_339_, lean_object* v_act_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_FmtM_run___redArg(v_ctx_339_, v_act_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object* v_00_u03b1_342_, lean_object* v_v_343_, lean_object* v_x_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_toBacktrackableState_346_; lean_object* v_shareCommonState_347_; lean_object* v_freshTagId_348_; lean_object* v_missingFormatters_349_; lean_object* v_partialFormatters_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_368_; 
v_toBacktrackableState_346_ = lean_ctor_get(v___y_345_, 0);
v_shareCommonState_347_ = lean_ctor_get(v___y_345_, 1);
v_freshTagId_348_ = lean_ctor_get(v___y_345_, 2);
v_missingFormatters_349_ = lean_ctor_get(v___y_345_, 3);
v_partialFormatters_350_ = lean_ctor_get(v___y_345_, 4);
v_isSharedCheck_368_ = !lean_is_exclusive(v___y_345_);
if (v_isSharedCheck_368_ == 0)
{
v___x_352_ = v___y_345_;
v_isShared_353_ = v_isSharedCheck_368_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_partialFormatters_350_);
lean_inc(v_missingFormatters_349_);
lean_inc(v_freshTagId_348_);
lean_inc(v_shareCommonState_347_);
lean_inc(v_toBacktrackableState_346_);
lean_dec(v___y_345_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_368_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v___x_354_ = l_Lean_ShareCommon_objectFactory;
v___x_355_ = lean_state_sharecommon(v___x_354_, v_shareCommonState_347_, v_v_343_);
v_fst_356_ = lean_ctor_get(v___x_355_, 0);
v_snd_357_ = lean_ctor_get(v___x_355_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v___x_355_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_inc(v_fst_356_);
lean_dec(v___x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_snd_357_);
v___x_362_ = v___x_352_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_toBacktrackableState_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_snd_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_freshTagId_348_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_missingFormatters_349_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_partialFormatters_350_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_362_);
v___x_364_ = v___x_359_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_356_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_362_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object* v_00_u03b1_369_, lean_object* v_v_370_, lean_object* v_x_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(v_00_u03b1_369_, v_v_370_, v_x_371_, v___y_372_);
lean_dec_ref(v_x_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object* v_t1_376_, lean_object* v_t2_377_){
_start:
{
lean_object* v_formattedLeadingRanges_378_; lean_object* v_formattedTrailingRanges_379_; lean_object* v_formattedLeadingRanges_380_; lean_object* v_formattedTrailingRanges_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_formattedLeadingRanges_378_ = lean_ctor_get(v_t1_376_, 0);
lean_inc_ref(v_formattedLeadingRanges_378_);
v_formattedTrailingRanges_379_ = lean_ctor_get(v_t1_376_, 1);
lean_inc_ref(v_formattedTrailingRanges_379_);
lean_dec_ref(v_t1_376_);
v_formattedLeadingRanges_380_ = lean_ctor_get(v_t2_377_, 0);
v_formattedTrailingRanges_381_ = lean_ctor_get(v_t2_377_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_t2_377_);
if (v_isSharedCheck_390_ == 0)
{
v___x_383_ = v_t2_377_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_formattedTrailingRanges_381_);
lean_inc(v_formattedLeadingRanges_380_);
lean_dec(v_t2_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = l_Array_append___redArg(v_formattedLeadingRanges_378_, v_formattedLeadingRanges_380_);
lean_dec_ref(v_formattedLeadingRanges_380_);
v___x_386_ = l_Array_append___redArg(v_formattedTrailingRanges_379_, v_formattedTrailingRanges_381_);
lean_dec_ref(v_formattedTrailingRanges_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_386_);
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object* v_stx_394_, lean_object* v_i_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_arg_397_; uint8_t v___x_398_; 
v_arg_397_ = l_Lean_Syntax_getArg(v_stx_394_, v_i_395_);
v___x_398_ = l_Lean_Syntax_isMissing(v_arg_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_arg_397_);
lean_ctor_set(v___x_399_, 1, v_a_396_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v_arg_397_);
v___x_400_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_a_396_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object* v_stx_402_, lean_object* v_i_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_402_, v_i_403_, v_a_404_);
lean_dec(v_i_403_);
lean_dec(v_stx_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object* v_stx_406_, lean_object* v_i_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_406_, v_i_407_, v_a_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object* v_stx_411_, lean_object* v_i_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Fmt_getStxArg_x21(v_stx_411_, v_i_412_, v_a_413_, v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_i_412_);
lean_dec(v_stx_411_);
return v_res_415_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0(void){
_start:
{
lean_object* v___x_416_; lean_object* v___f_417_; 
v___x_416_ = l_Lean_Fmt_instInhabitedError_default;
v___f_417_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_417_, 0, v___x_416_);
return v___f_417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___x_744__overap_423_; lean_object* v___x_424_; 
v___f_421_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_422_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_422_, 0, v___f_421_);
v___x_744__overap_423_ = lean_panic_fn_borrowed(v___f_422_, v_msg_418_);
lean_dec_ref(v___f_422_);
lean_inc_ref(v___y_419_);
v___x_424_ = lean_apply_2(v___x_744__overap_423_, v___y_419_, v___y_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v_msg_425_, v___y_426_, v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_428_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object* v_msg_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0);
v___x_434_ = lean_panic_fn_borrowed(v___x_433_, v_msg_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object* v_x_435_){
_start:
{
lean_object* v_startPos_436_; 
v_startPos_436_ = lean_ctor_get(v_x_435_, 4);
lean_inc(v_startPos_436_);
return v_startPos_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Fmt_getLineInfo_x21___lam__0(v_x_437_);
lean_dec_ref(v_x_437_);
return v_res_438_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_442_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__2));
v___x_443_ = lean_unsigned_to_nat(2u);
v___x_444_ = lean_unsigned_to_nat(92u);
v___x_445_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__1));
v___x_446_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_447_ = l_mkPanicMessageWithDecl(v___x_446_, v___x_445_, v___x_444_, v___x_443_, v___x_442_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__9(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__8));
v___x_454_ = lean_unsigned_to_nat(14u);
v___x_455_ = lean_unsigned_to_nat(22u);
v___x_456_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__7));
v___x_457_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__6));
v___x_458_ = l_mkPanicMessageWithDecl(v___x_457_, v___x_456_, v___x_455_, v___x_454_, v___x_453_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object* v_pos_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_469_; lean_object* v_lineInfos_475_; lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v_lineInfos_475_ = lean_ctor_get(v_a_460_, 4);
v___f_476_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_477_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
lean_inc(v_pos_459_);
v___x_478_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_475_, v_pos_459_, v___f_476_, v___f_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_480_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_479_);
v___y_469_ = v___x_480_;
goto v___jp_468_;
}
else
{
lean_object* v_val_481_; 
v_val_481_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_478_, 1);
v___y_469_ = v_val_481_;
goto v___jp_468_;
}
v___jp_462_:
{
if (v___y_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v___y_463_);
v___x_465_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__3, &l_Lean_Fmt_getLineInfo_x21___closed__3_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__3);
v___x_466_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v___x_465_, v_a_460_, v_a_461_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___y_463_);
lean_ctor_set(v___x_467_, 1, v_a_461_);
return v___x_467_;
}
}
v___jp_468_:
{
lean_object* v_snd_470_; lean_object* v_startPos_471_; lean_object* v_endPos_472_; uint8_t v___x_473_; 
v_snd_470_ = lean_ctor_get(v___y_469_, 1);
lean_inc(v_snd_470_);
lean_dec_ref(v___y_469_);
v_startPos_471_ = lean_ctor_get(v_snd_470_, 4);
v_endPos_472_ = lean_ctor_get(v_snd_470_, 5);
v___x_473_ = lean_nat_dec_le(v_startPos_471_, v_pos_459_);
if (v___x_473_ == 0)
{
lean_dec(v_pos_459_);
v___y_463_ = v_snd_470_;
v___y_464_ = v___x_473_;
goto v___jp_462_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_le(v_pos_459_, v_endPos_472_);
lean_dec(v_pos_459_);
v___y_463_ = v_snd_470_;
v___y_464_ = v___x_474_;
goto v___jp_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object* v_pos_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Fmt_getLineInfo_x21(v_pos_482_, v_a_483_, v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_1308__overap_491_; lean_object* v___x_492_; 
v___f_489_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_490_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_490_, 0, v___f_489_);
v___x_1308__overap_491_ = lean_panic_fn_borrowed(v___f_490_, v_msg_486_);
lean_dec_ref(v___f_490_);
lean_inc_ref(v___y_487_);
v___x_492_ = lean_apply_2(v___x_1308__overap_491_, v___y_487_, v___y_488_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object* v_msg_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v_msg_493_, v___y_494_, v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object* v_a_497_, lean_object* v_b_498_){
_start:
{
lean_object* v_array_499_; lean_object* v_start_500_; lean_object* v_stop_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_514_; 
v_array_499_ = lean_ctor_get(v_a_497_, 0);
v_start_500_ = lean_ctor_get(v_a_497_, 1);
v_stop_501_ = lean_ctor_get(v_a_497_, 2);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_514_ == 0)
{
v___x_503_ = v_a_497_;
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_stop_501_);
lean_inc(v_start_500_);
lean_inc(v_array_499_);
lean_dec(v_a_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; 
v___x_505_ = lean_nat_dec_lt(v_start_500_, v_stop_501_);
if (v___x_505_ == 0)
{
lean_del_object(v___x_503_);
lean_dec(v_stop_501_);
lean_dec(v_start_500_);
lean_dec_ref(v_array_499_);
return v_b_498_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_start_500_, v___x_506_);
lean_inc_ref(v_array_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_array_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_stop_501_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_array_fget(v_array_499_, v_start_500_);
lean_dec(v_start_500_);
lean_dec_ref(v_array_499_);
v___x_511_ = lean_array_push(v_b_498_, v___x_510_);
v_a_497_ = v___x_509_;
v_b_498_ = v___x_511_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfos___closed__3(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_519_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__2));
v___x_520_ = lean_unsigned_to_nat(2u);
v___x_521_ = lean_unsigned_to_nat(100u);
v___x_522_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__1));
v___x_523_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_524_ = l_mkPanicMessageWithDecl(v___x_523_, v___x_522_, v___x_521_, v___x_520_, v___x_519_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object* v_pos_525_, lean_object* v_tailPos_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_lineInfos_529_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___y_555_; lean_object* v___x_561_; 
v_lineInfos_529_ = lean_ctor_get(v_a_527_, 4);
v___f_552_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_553_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_561_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_529_, v_pos_525_, v___f_552_, v___f_553_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_563_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_562_);
v___y_555_ = v___x_563_;
goto v___jp_554_;
}
else
{
lean_object* v_val_564_; 
v_val_564_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___x_561_, 1);
v___y_555_ = v_val_564_;
goto v___jp_554_;
}
v___jp_530_:
{
lean_object* v_fst_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_550_; 
v_fst_533_ = lean_ctor_get(v___y_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___y_532_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___y_532_, 1);
lean_dec(v_unused_551_);
v___x_535_ = v___y_532_;
v_isShared_536_ = v_isSharedCheck_550_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_fst_533_);
lean_dec(v___y_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_550_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_fst_533_, v___x_537_);
lean_dec(v_fst_533_);
lean_inc_ref(v_lineInfos_529_);
v___x_539_ = l_Array_toSubarray___redArg(v_lineInfos_529_, v___y_531_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_542_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_539_, v___x_541_);
v___x_543_ = lean_array_get_size(v___x_542_);
v___x_544_ = lean_nat_dec_eq(v___x_543_, v___x_540_);
if (v___x_544_ == 0)
{
lean_object* v___x_546_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v_a_528_);
lean_ctor_set(v___x_535_, 0, v___x_542_);
v___x_546_ = v___x_535_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_528_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v___x_542_);
lean_del_object(v___x_535_);
v___x_548_ = lean_obj_once(&l_Lean_Fmt_getLineInfos___closed__3, &l_Lean_Fmt_getLineInfos___closed__3_once, _init_l_Lean_Fmt_getLineInfos___closed__3);
v___x_549_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v___x_548_, v_a_527_, v_a_528_);
return v___x_549_;
}
}
}
v___jp_554_:
{
lean_object* v_fst_556_; lean_object* v___x_557_; 
v_fst_556_ = lean_ctor_get(v___y_555_, 0);
lean_inc(v_fst_556_);
lean_dec_ref(v___y_555_);
v___x_557_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_529_, v_tailPos_526_, v___f_552_, v___f_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_559_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_558_);
v___y_531_ = v_fst_556_;
v___y_532_ = v___x_559_;
goto v___jp_530_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_557_, 1);
v___y_531_ = v_fst_556_;
v___y_532_ = v_val_560_;
goto v___jp_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object* v_pos_565_, lean_object* v_tailPos_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Fmt_getLineInfos(v_pos_565_, v_tailPos_566_, v_a_567_, v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object* v_inst_570_, lean_object* v_R_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v_a_572_, v_b_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object* v_pos_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_lineInfos_578_; lean_object* v___y_580_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
v_lineInfos_578_ = lean_ctor_get(v_a_576_, 4);
v___f_600_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_601_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_602_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_578_, v_pos_575_, v___f_600_, v___f_601_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_604_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_603_);
v___y_580_ = v___x_604_;
goto v___jp_579_;
}
else
{
lean_object* v_val_605_; 
v_val_605_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_602_, 1);
v___y_580_ = v_val_605_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v_fst_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_fst_581_ = lean_ctor_get(v___y_580_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___y_580_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___y_580_, 1);
lean_dec(v_unused_599_);
v___x_583_ = v___y_580_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_fst_581_);
lean_dec(v___y_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_fst_581_, v___x_585_);
lean_dec(v_fst_581_);
v___x_587_ = lean_array_get_size(v_lineInfos_578_);
v___x_588_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_a_577_);
lean_ctor_set(v___x_583_, 0, v___x_589_);
v___x_591_ = v___x_583_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_577_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_593_ = lean_array_fget_borrowed(v_lineInfos_578_, v___x_586_);
lean_dec(v___x_586_);
lean_inc(v___x_593_);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_a_577_);
lean_ctor_set(v___x_583_, 0, v___x_594_);
v___x_596_ = v___x_583_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_a_577_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object* v_pos_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Fmt_getNextLineInfo_x3f(v_pos_606_, v_a_607_, v_a_608_);
lean_dec_ref(v_a_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___x_614_; 
v___x_614_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_bs_612_);
lean_ctor_set(v___x_615_, 1, v___y_613_);
return v___x_615_;
}
else
{
lean_object* v_v_616_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_619_; lean_object* v_bs_x27_620_; lean_object* v_a_622_; lean_object* v_a_623_; 
v_v_616_ = lean_array_uget_borrowed(v_bs_612_, v_i_611_);
v_fst_617_ = lean_ctor_get(v_v_616_, 0);
lean_inc(v_fst_617_);
v_snd_618_ = lean_ctor_get(v_v_616_, 1);
lean_inc(v_snd_618_);
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_619_);
if (lean_obj_tag(v_snd_618_) == 0)
{
v_a_622_ = v_fst_617_;
v_a_623_ = v___y_613_;
goto v___jp_621_;
}
else
{
lean_object* v_val_628_; lean_object* v_doc_629_; lean_object* v_metaData_630_; lean_object* v___x_631_; 
v_val_628_ = lean_ctor_get(v_snd_618_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v_snd_618_, 1);
v_doc_629_ = lean_ctor_get(v_fst_617_, 0);
lean_inc(v_doc_629_);
v_metaData_630_ = lean_ctor_get(v_fst_617_, 1);
lean_inc(v_metaData_630_);
lean_dec(v_fst_617_);
v___x_631_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_629_, v_val_628_, v___y_613_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v_a_633_; lean_object* v_doc_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
v_a_633_ = lean_ctor_get(v___x_631_, 1);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_631_, 2);
v_doc_634_ = lean_ctor_get(v_a_632_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_a_632_, 1);
lean_dec(v_unused_642_);
v___x_636_ = v_a_632_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_doc_634_);
lean_dec(v_a_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_metaData_630_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_doc_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_metaData_630_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v_a_622_ = v___x_639_;
v_a_623_ = v_a_633_;
goto v___jp_621_;
}
}
}
else
{
lean_dec(v_metaData_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_643_; lean_object* v_a_644_; 
v_a_643_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_643_);
v_a_644_ = lean_ctor_get(v___x_631_, 1);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_631_, 2);
v_a_622_ = v_a_643_;
v_a_623_ = v_a_644_;
goto v___jp_621_;
}
else
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_bs_x27_620_);
v_a_645_ = lean_ctor_get(v___x_631_, 0);
v_a_646_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_631_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_inc(v_a_645_);
lean_dec(v___x_631_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
v___jp_621_:
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_611_, v___x_624_);
v___x_626_ = lean_array_uset(v_bs_x27_620_, v_i_611_, v_a_622_);
v_i_611_ = v___x_625_;
v_bs_612_ = v___x_626_;
v___y_613_ = v_a_623_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_bs_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_659_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_boxed_658_, v_i_boxed_659_, v_bs_656_, v___y_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object* v_stx_661_, lean_object* v_fmtLeading_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_stx_661_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_667_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_Syntax_getLeading_x3f(v_val_666_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_669_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
lean_inc_ref(v_a_663_);
v___x_669_ = lean_apply_4(v_fmtLeading_662_, v_val_666_, v_val_668_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_a_671_; size_t v_sz_672_; size_t v___x_673_; lean_object* v___x_674_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
v_a_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_669_, 2);
v_sz_672_ = lean_array_size(v_a_670_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_672_, v___x_673_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_a_676_ = lean_ctor_get(v___x_674_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v___x_674_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_Fmt_TaggedDoc_join(v_a_675_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_a_676_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_685_ = lean_ctor_get(v___x_674_, 0);
v_a_686_ = lean_ctor_get(v___x_674_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_674_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_inc(v_a_685_);
lean_dec(v___x_674_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_685_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_694_ = lean_ctor_get(v___x_669_, 0);
v_a_695_ = lean_ctor_get(v___x_669_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_669_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_inc(v_a_694_);
lean_dec(v___x_669_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v___x_667_);
lean_dec(v_val_666_);
lean_dec_ref(v_fmtLeading_662_);
v___x_703_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_a_664_);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v___x_665_);
lean_dec_ref(v_fmtLeading_662_);
v___x_705_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_a_664_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object* v_stx_707_, lean_object* v_fmtLeading_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_707_, v_fmtLeading_708_, v_a_709_, v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t v_sz_712_, size_t v_i_713_, lean_object* v_bs_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_712_, v_i_713_, v_bs_714_, v___y_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_724_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(v_sz_boxed_723_, v_i_boxed_724_, v_bs_720_, v___y_721_, v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object* v_stx_726_, lean_object* v_fmtTrailing_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v_stx_726_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_732_; 
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Syntax_getTrailing_x3f(v_val_731_);
if (lean_obj_tag(v___x_732_) == 1)
{
lean_object* v_val_733_; lean_object* v___x_734_; 
v_val_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v___x_732_, 1);
lean_inc_ref(v_a_728_);
v___x_734_ = lean_apply_4(v_fmtTrailing_727_, v_val_731_, v_val_733_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v_a_736_; size_t v_sz_737_; size_t v___x_738_; lean_object* v___x_739_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
v_a_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_734_, 2);
v_sz_737_ = lean_array_size(v_a_735_);
v___x_738_ = ((size_t)0ULL);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_737_, v___x_738_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_a_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = l_Lean_Fmt_TaggedDoc_join(v_a_740_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_a_741_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_750_ = lean_ctor_get(v___x_739_, 0);
v_a_751_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_739_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_inc(v_a_750_);
lean_dec(v___x_739_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_759_ = lean_ctor_get(v___x_734_, 0);
v_a_760_ = lean_ctor_get(v___x_734_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_734_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_734_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v___x_732_);
lean_dec(v_val_731_);
lean_dec_ref(v_fmtTrailing_727_);
v___x_768_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_a_729_);
return v___x_769_;
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v___x_730_);
lean_dec_ref(v_fmtTrailing_727_);
v___x_770_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_a_729_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object* v_stx_772_, lean_object* v_fmtTrailing_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_772_, v_fmtTrailing_773_, v_a_774_, v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object* v_env_777_, lean_object* v_opts_778_, lean_object* v_kind_779_){
_start:
{
uint8_t v___x_780_; lean_object* v___x_781_; 
v___x_780_ = 1;
v___x_781_ = l_Lean_Environment_evalConst___redArg(v_env_777_, v_opts_778_, v_kind_779_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; 
lean_dec_ref_known(v___x_781_, 1);
v___x_782_ = lean_box(0);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_781_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_781_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object* v_env_791_, lean_object* v_opts_792_, lean_object* v_kind_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(v_env_791_, v_opts_792_, v_kind_793_);
lean_dec(v_kind_793_);
lean_dec_ref(v_opts_792_);
lean_dec_ref(v_env_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object* v_env_823_, lean_object* v_opts_824_, lean_object* v_kind_825_){
_start:
{
lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_847_; uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_883_ = 0;
lean_inc(v_kind_825_);
lean_inc_ref(v_env_823_);
v___x_884_ = l_Lean_Environment_find_x3f(v_env_823_, v_kind_825_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_885_; 
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
v___x_885_ = lean_box(0);
return v___x_885_;
}
else
{
lean_object* v_val_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_val_886_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v___x_884_, 1);
v___x_887_ = l_Lean_ConstantInfo_type(v_val_886_);
lean_dec(v_val_886_);
v___x_888_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11));
v___x_889_ = l_Lean_Expr_isConstOf(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13));
v___x_891_ = l_Lean_Expr_isConstOf(v___x_887_, v___x_890_);
lean_dec_ref(v___x_887_);
v___y_847_ = v___x_891_;
goto v___jp_846_;
}
else
{
lean_dec_ref(v___x_887_);
v___y_847_ = v___x_889_;
goto v___jp_846_;
}
}
v___jp_826_:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v___y_829_, v___x_830_);
lean_dec(v___y_829_);
v___x_832_ = lean_nat_dec_eq(v___x_831_, v___y_827_);
lean_dec(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v___y_828_);
lean_dec(v___y_827_);
v___x_833_ = lean_box(0);
return v___x_833_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_eq(v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec(v___y_827_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
return v___x_836_;
}
}
}
v___jp_837_:
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_eq(v___y_840_, v___y_839_);
if (v___x_841_ == 0)
{
v___y_827_ = v___y_838_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_840_;
goto v___jp_826_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v___y_839_, v___x_842_);
v___x_844_ = lean_nat_dec_eq(v___y_838_, v___x_843_);
lean_dec(v___x_843_);
if (v___x_844_ == 0)
{
v___y_827_ = v___y_838_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_840_;
goto v___jp_826_;
}
else
{
lean_object* v___x_845_; 
lean_dec(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_838_);
v___x_845_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4));
return v___x_845_;
}
}
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
v___x_848_ = lean_box(0);
return v___x_848_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Environment_evalConst___redArg(v_env_823_, v_opts_824_, v_kind_825_, v___y_847_);
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v___x_850_; 
lean_dec_ref_known(v___x_849_, 1);
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_849_, 1);
if (lean_obj_tag(v_a_851_) == 4)
{
lean_object* v_p_852_; 
v_p_852_ = lean_ctor_get(v_a_851_, 3);
lean_inc_ref(v_p_852_);
if (lean_obj_tag(v_p_852_) == 2)
{
lean_object* v_name_853_; 
v_name_853_ = lean_ctor_get(v_p_852_, 0);
lean_inc(v_name_853_);
if (lean_obj_tag(v_name_853_) == 1)
{
lean_object* v_pre_854_; 
v_pre_854_ = lean_ctor_get(v_name_853_, 0);
if (lean_obj_tag(v_pre_854_) == 0)
{
lean_object* v_prec_855_; lean_object* v_lhsPrec_856_; lean_object* v_p_u2081_857_; lean_object* v_p_u2082_858_; lean_object* v_str_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_prec_855_ = lean_ctor_get(v_a_851_, 1);
lean_inc(v_prec_855_);
v_lhsPrec_856_ = lean_ctor_get(v_a_851_, 2);
lean_inc(v_lhsPrec_856_);
lean_dec_ref_known(v_a_851_, 4);
v_p_u2081_857_ = lean_ctor_get(v_p_852_, 1);
lean_inc_ref(v_p_u2081_857_);
v_p_u2082_858_ = lean_ctor_get(v_p_852_, 2);
lean_inc_ref(v_p_u2082_858_);
lean_dec_ref_known(v_p_852_, 3);
v_str_859_ = lean_ctor_get(v_name_853_, 1);
lean_inc_ref(v_str_859_);
lean_dec_ref_known(v_name_853_, 2);
v___x_860_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5));
v___x_861_ = lean_string_dec_eq(v_str_859_, v___x_860_);
lean_dec_ref(v_str_859_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_p_u2082_858_);
lean_dec_ref(v_p_u2081_857_);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_862_ = lean_box(0);
return v___x_862_;
}
else
{
if (lean_obj_tag(v_p_u2081_857_) == 5)
{
lean_dec_ref_known(v_p_u2081_857_, 1);
if (lean_obj_tag(v_p_u2082_858_) == 7)
{
lean_object* v_catName_863_; 
v_catName_863_ = lean_ctor_get(v_p_u2082_858_, 0);
lean_inc(v_catName_863_);
if (lean_obj_tag(v_catName_863_) == 1)
{
lean_object* v_pre_864_; 
v_pre_864_ = lean_ctor_get(v_catName_863_, 0);
if (lean_obj_tag(v_pre_864_) == 0)
{
lean_object* v_rbp_865_; lean_object* v_str_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_rbp_865_ = lean_ctor_get(v_p_u2082_858_, 1);
lean_inc(v_rbp_865_);
lean_dec_ref_known(v_p_u2082_858_, 2);
v_str_866_ = lean_ctor_get(v_catName_863_, 1);
lean_inc_ref(v_str_866_);
lean_dec_ref_known(v_catName_863_, 2);
v___x_867_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_868_ = lean_string_dec_eq(v_str_866_, v___x_867_);
lean_dec_ref(v_str_866_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_rbp_865_);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_869_ = lean_box(0);
return v___x_869_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = lean_nat_dec_eq(v_prec_855_, v_lhsPrec_856_);
if (v___x_870_ == 0)
{
v___y_838_ = v_lhsPrec_856_;
v___y_839_ = v_rbp_865_;
v___y_840_ = v_prec_855_;
goto v___jp_837_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_lhsPrec_856_, v___x_871_);
v___x_873_ = lean_nat_dec_eq(v___x_872_, v_rbp_865_);
lean_dec(v___x_872_);
if (v___x_873_ == 0)
{
v___y_838_ = v_lhsPrec_856_;
v___y_839_ = v_rbp_865_;
v___y_840_ = v_prec_855_;
goto v___jp_837_;
}
else
{
lean_object* v___x_874_; 
lean_dec(v_rbp_865_);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_874_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_875_; 
lean_dec_ref_known(v_catName_863_, 2);
lean_dec_ref_known(v_p_u2082_858_, 2);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_875_ = lean_box(0);
return v___x_875_;
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v_catName_863_);
lean_dec_ref_known(v_p_u2082_858_, 2);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_876_ = lean_box(0);
return v___x_876_;
}
}
else
{
lean_object* v___x_877_; 
lean_dec_ref(v_p_u2082_858_);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_877_ = lean_box(0);
return v___x_877_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec_ref(v_p_u2082_858_);
lean_dec_ref(v_p_u2081_857_);
lean_dec(v_lhsPrec_856_);
lean_dec(v_prec_855_);
v___x_878_ = lean_box(0);
return v___x_878_;
}
}
}
else
{
lean_object* v___x_879_; 
lean_dec_ref_known(v_name_853_, 2);
lean_dec_ref_known(v_p_852_, 3);
lean_dec_ref_known(v_a_851_, 4);
v___x_879_ = lean_box(0);
return v___x_879_;
}
}
else
{
lean_object* v___x_880_; 
lean_dec(v_name_853_);
lean_dec_ref_known(v_p_852_, 3);
lean_dec_ref_known(v_a_851_, 4);
v___x_880_ = lean_box(0);
return v___x_880_;
}
}
else
{
lean_object* v___x_881_; 
lean_dec_ref_known(v_a_851_, 4);
lean_dec_ref(v_p_852_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec(v_a_851_);
v___x_882_ = lean_box(0);
return v___x_882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object* v_env_892_, lean_object* v_opts_893_, lean_object* v_kind_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_892_, v_opts_893_, v_kind_894_);
lean_dec_ref(v_opts_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object* v_env_896_, lean_object* v_opts_897_, lean_object* v_kind_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = l_Lean_Fmt_infixFmtAttribute;
lean_inc_ref(v_env_896_);
v___x_900_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_899_, v_env_896_, v_kind_898_);
v___x_901_ = l_List_head_x3f___redArg(v___x_900_);
lean_dec(v___x_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_896_, v_opts_897_, v_kind_898_);
return v___x_902_;
}
else
{
lean_dec(v_kind_898_);
lean_dec_ref(v_env_896_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object* v_env_903_, lean_object* v_opts_904_, lean_object* v_kind_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_903_, v_opts_904_, v_kind_905_);
lean_dec_ref(v_opts_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object* v_env_907_, lean_object* v_opts_908_, lean_object* v_kind_909_){
_start:
{
uint8_t v___x_910_; lean_object* v___x_911_; 
v___x_910_ = 1;
v___x_911_ = l_Lean_Environment_evalConst___redArg(v_env_907_, v_opts_908_, v_kind_909_, v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; 
lean_dec_ref_known(v___x_911_, 1);
v___x_912_ = lean_box(0);
return v___x_912_;
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_a_913_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_911_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object* v_env_921_, lean_object* v_opts_922_, lean_object* v_kind_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(v_env_921_, v_opts_922_, v_kind_923_);
lean_dec(v_kind_923_);
lean_dec_ref(v_opts_922_);
lean_dec_ref(v_env_921_);
return v_res_924_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object* v_env_925_, lean_object* v_opts_926_, lean_object* v_kind_927_){
_start:
{
uint8_t v___x_928_; lean_object* v___x_929_; 
v___x_928_ = 0;
lean_inc(v_kind_927_);
lean_inc_ref(v_env_925_);
v___x_929_ = l_Lean_Environment_find_x3f(v_env_925_, v_kind_927_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_dec(v_kind_927_);
lean_dec_ref(v_env_925_);
return v___x_928_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_val_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = l_Lean_ConstantInfo_type(v_val_930_);
lean_dec(v_val_930_);
v___x_932_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11));
v___x_933_ = l_Lean_Expr_isConstOf(v___x_931_, v___x_932_);
lean_dec_ref(v___x_931_);
if (v___x_933_ == 0)
{
lean_dec(v_kind_927_);
lean_dec_ref(v_env_925_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Environment_evalConst___redArg(v_env_925_, v_opts_926_, v_kind_927_, v___x_933_);
lean_dec(v_kind_927_);
lean_dec_ref(v_env_925_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref_known(v___x_934_, 1);
return v___x_928_;
}
else
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
if (lean_obj_tag(v_a_935_) == 3)
{
lean_object* v_p_936_; 
v_p_936_ = lean_ctor_get(v_a_935_, 2);
lean_inc_ref(v_p_936_);
if (lean_obj_tag(v_p_936_) == 2)
{
lean_object* v_name_937_; 
v_name_937_ = lean_ctor_get(v_p_936_, 0);
lean_inc(v_name_937_);
if (lean_obj_tag(v_name_937_) == 1)
{
lean_object* v_pre_938_; 
v_pre_938_ = lean_ctor_get(v_name_937_, 0);
if (lean_obj_tag(v_pre_938_) == 0)
{
lean_object* v_prec_939_; lean_object* v_p_u2081_940_; lean_object* v_p_u2082_941_; lean_object* v_str_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_prec_939_ = lean_ctor_get(v_a_935_, 1);
lean_inc(v_prec_939_);
lean_dec_ref_known(v_a_935_, 3);
v_p_u2081_940_ = lean_ctor_get(v_p_936_, 1);
lean_inc_ref(v_p_u2081_940_);
v_p_u2082_941_ = lean_ctor_get(v_p_936_, 2);
lean_inc_ref(v_p_u2082_941_);
lean_dec_ref_known(v_p_936_, 3);
v_str_942_ = lean_ctor_get(v_name_937_, 1);
lean_inc_ref(v_str_942_);
lean_dec_ref_known(v_name_937_, 2);
v___x_943_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5));
v___x_944_ = lean_string_dec_eq(v_str_942_, v___x_943_);
lean_dec_ref(v_str_942_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_p_u2082_941_);
lean_dec_ref(v_p_u2081_940_);
lean_dec(v_prec_939_);
return v___x_928_;
}
else
{
if (lean_obj_tag(v_p_u2081_940_) == 5)
{
lean_dec_ref_known(v_p_u2081_940_, 1);
if (lean_obj_tag(v_p_u2082_941_) == 7)
{
lean_object* v_catName_945_; 
v_catName_945_ = lean_ctor_get(v_p_u2082_941_, 0);
lean_inc(v_catName_945_);
if (lean_obj_tag(v_catName_945_) == 1)
{
lean_object* v_pre_946_; 
v_pre_946_ = lean_ctor_get(v_catName_945_, 0);
if (lean_obj_tag(v_pre_946_) == 0)
{
lean_object* v_rbp_947_; lean_object* v_str_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_rbp_947_ = lean_ctor_get(v_p_u2082_941_, 1);
lean_inc(v_rbp_947_);
lean_dec_ref_known(v_p_u2082_941_, 2);
v_str_948_ = lean_ctor_get(v_catName_945_, 1);
lean_inc_ref(v_str_948_);
lean_dec_ref_known(v_catName_945_, 2);
v___x_949_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_950_ = lean_string_dec_eq(v_str_948_, v___x_949_);
lean_dec_ref(v_str_948_);
if (v___x_950_ == 0)
{
lean_dec(v_rbp_947_);
lean_dec(v_prec_939_);
return v___x_928_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_eq(v_prec_939_, v_rbp_947_);
lean_dec(v_rbp_947_);
lean_dec(v_prec_939_);
return v___x_951_;
}
}
else
{
lean_dec_ref_known(v_catName_945_, 2);
lean_dec_ref_known(v_p_u2082_941_, 2);
lean_dec(v_prec_939_);
return v___x_928_;
}
}
else
{
lean_dec_ref_known(v_p_u2082_941_, 2);
lean_dec(v_catName_945_);
lean_dec(v_prec_939_);
return v___x_928_;
}
}
else
{
lean_dec_ref(v_p_u2082_941_);
lean_dec(v_prec_939_);
return v___x_928_;
}
}
else
{
lean_dec_ref(v_p_u2082_941_);
lean_dec_ref(v_p_u2081_940_);
lean_dec(v_prec_939_);
return v___x_928_;
}
}
}
else
{
lean_dec_ref_known(v_name_937_, 2);
lean_dec_ref_known(v_p_936_, 3);
lean_dec_ref_known(v_a_935_, 3);
return v___x_928_;
}
}
else
{
lean_dec_ref_known(v_p_936_, 3);
lean_dec(v_name_937_);
lean_dec_ref_known(v_a_935_, 3);
return v___x_928_;
}
}
else
{
lean_dec_ref(v_p_936_);
lean_dec_ref_known(v_a_935_, 3);
return v___x_928_;
}
}
else
{
lean_dec(v_a_935_);
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object* v_env_952_, lean_object* v_opts_953_, lean_object* v_kind_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_952_, v_opts_953_, v_kind_954_);
lean_dec_ref(v_opts_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object* v_env_957_, lean_object* v_opts_958_, lean_object* v_kind_959_){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; 
v___x_960_ = 1;
v___x_961_ = l_Lean_Environment_evalConst___redArg(v_env_957_, v_opts_958_, v_kind_959_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; 
lean_dec_ref_known(v___x_961_, 1);
v___x_962_ = lean_box(0);
return v___x_962_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_961_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_961_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object* v_env_971_, lean_object* v_opts_972_, lean_object* v_kind_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(v_env_971_, v_opts_972_, v_kind_973_);
lean_dec(v_kind_973_);
lean_dec_ref(v_opts_972_);
lean_dec_ref(v_env_971_);
return v_res_974_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object* v_env_975_, lean_object* v_opts_976_, lean_object* v_kind_977_){
_start:
{
uint8_t v___x_978_; lean_object* v___x_979_; 
v___x_978_ = 0;
lean_inc(v_kind_977_);
lean_inc_ref(v_env_975_);
v___x_979_ = l_Lean_Environment_find_x3f(v_env_975_, v_kind_977_, v___x_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec(v_kind_977_);
lean_dec_ref(v_env_975_);
return v___x_978_;
}
else
{
lean_object* v_val_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_ConstantInfo_type(v_val_980_);
lean_dec(v_val_980_);
v___x_982_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__13));
v___x_983_ = l_Lean_Expr_isConstOf(v___x_981_, v___x_982_);
lean_dec_ref(v___x_981_);
if (v___x_983_ == 0)
{
lean_dec(v_kind_977_);
lean_dec_ref(v_env_975_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Environment_evalConst___redArg(v_env_975_, v_opts_976_, v_kind_977_, v___x_983_);
lean_dec(v_kind_977_);
lean_dec_ref(v_env_975_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
return v___x_978_;
}
else
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
if (lean_obj_tag(v_a_985_) == 4)
{
lean_object* v_p_986_; 
v_p_986_ = lean_ctor_get(v_a_985_, 3);
if (lean_obj_tag(v_p_986_) == 5)
{
lean_object* v_prec_987_; lean_object* v_lhsPrec_988_; uint8_t v___x_989_; 
v_prec_987_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_prec_987_);
v_lhsPrec_988_ = lean_ctor_get(v_a_985_, 2);
lean_inc(v_lhsPrec_988_);
lean_dec_ref_known(v_a_985_, 4);
v___x_989_ = lean_nat_dec_eq(v_prec_987_, v_lhsPrec_988_);
lean_dec(v_lhsPrec_988_);
lean_dec(v_prec_987_);
return v___x_989_;
}
else
{
lean_dec_ref_known(v_a_985_, 4);
return v___x_978_;
}
}
else
{
lean_dec(v_a_985_);
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object* v_env_990_, lean_object* v_opts_991_, lean_object* v_kind_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_990_, v_opts_991_, v_kind_992_);
lean_dec_ref(v_opts_991_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object* v_a_1121_, lean_object* v_as_1122_, size_t v_i_1123_, size_t v_stop_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_usize_dec_eq(v_i_1123_, v_stop_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_array_uget_borrowed(v_as_1122_, v_i_1123_);
v___x_1127_ = lean_name_eq(v_a_1121_, v___x_1126_);
if (v___x_1127_ == 0)
{
size_t v___x_1128_; size_t v___x_1129_; 
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1123_, v___x_1128_);
v_i_1123_ = v___x_1129_;
goto _start;
}
else
{
return v___x_1127_;
}
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = 0;
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object* v_a_1132_, lean_object* v_as_1133_, lean_object* v_i_1134_, lean_object* v_stop_1135_){
_start:
{
size_t v_i_boxed_1136_; size_t v_stop_boxed_1137_; uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_i_boxed_1136_ = lean_unbox_usize(v_i_1134_);
lean_dec(v_i_1134_);
v_stop_boxed_1137_ = lean_unbox_usize(v_stop_1135_);
lean_dec(v_stop_1135_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1132_, v_as_1133_, v_i_boxed_1136_, v_stop_boxed_1137_);
lean_dec_ref(v_as_1133_);
lean_dec(v_a_1132_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object* v_as_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_array_get_size(v_as_1140_);
v___x_1144_ = lean_nat_dec_lt(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
return v___x_1144_;
}
else
{
if (v___x_1144_ == 0)
{
return v___x_1144_;
}
else
{
size_t v___x_1145_; size_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = lean_usize_of_nat(v___x_1143_);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1141_, v_as_1140_, v___x_1145_, v___x_1146_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object* v_as_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_as_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_as_1148_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object* v_x_1157_){
_start:
{
switch(lean_obj_tag(v_x_1157_))
{
case 5:
{
uint8_t v___x_1158_; 
v___x_1158_ = 1;
return v___x_1158_;
}
case 6:
{
uint8_t v___x_1159_; 
v___x_1159_ = 1;
return v___x_1159_;
}
case 12:
{
uint8_t v___x_1160_; 
v___x_1160_ = 1;
return v___x_1160_;
}
case 0:
{
lean_object* v_name_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_name_1161_ = lean_ctor_get(v_x_1157_, 0);
v___x_1162_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases));
v___x_1163_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1162_, v_name_1161_);
return v___x_1163_;
}
case 1:
{
lean_object* v_name_1164_; lean_object* v_p_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_name_1164_ = lean_ctor_get(v_x_1157_, 0);
v_p_1165_ = lean_ctor_get(v_x_1157_, 1);
v___x_1166_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases));
v___x_1167_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1166_, v_name_1164_);
if (v___x_1167_ == 0)
{
return v___x_1167_;
}
else
{
v_x_1157_ = v_p_1165_;
goto _start;
}
}
case 2:
{
lean_object* v_name_1169_; lean_object* v_p_u2081_1170_; lean_object* v_p_u2082_1171_; uint8_t v___y_1173_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_name_1169_ = lean_ctor_get(v_x_1157_, 0);
v_p_u2081_1170_ = lean_ctor_get(v_x_1157_, 1);
v_p_u2082_1171_ = lean_ctor_get(v_x_1157_, 2);
v___x_1176_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0));
v___x_1177_ = lean_name_eq(v_name_1169_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2));
v___x_1179_ = lean_name_eq(v_name_1169_, v___x_1178_);
v___y_1173_ = v___x_1179_;
goto v___jp_1172_;
}
else
{
v___y_1173_ = v___x_1177_;
goto v___jp_1172_;
}
v___jp_1172_:
{
if (v___y_1173_ == 0)
{
return v___y_1173_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_p_u2081_1170_);
if (v___x_1174_ == 0)
{
return v___x_1174_;
}
else
{
v_x_1157_ = v_p_u2082_1171_;
goto _start;
}
}
}
}
case 3:
{
lean_object* v_p_1180_; 
v_p_1180_ = lean_ctor_get(v_x_1157_, 2);
v_x_1157_ = v_p_1180_;
goto _start;
}
case 9:
{
lean_object* v_p_1182_; 
v_p_1182_ = lean_ctor_get(v_x_1157_, 2);
v_x_1157_ = v_p_1182_;
goto _start;
}
default: 
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object* v_x_1185_){
_start:
{
uint8_t v_res_1186_; lean_object* v_r_1187_; 
v_res_1186_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_x_1185_);
lean_dec_ref(v_x_1185_);
v_r_1187_ = lean_box(v_res_1186_);
return v_r_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object* v_env_1188_, lean_object* v_opts_1189_, lean_object* v_kind_1190_){
_start:
{
uint8_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = 1;
v___x_1192_ = l_Lean_Environment_evalConst___redArg(v_env_1188_, v_opts_1189_, v_kind_1190_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; 
lean_dec_ref_known(v___x_1192_, 1);
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object* v_env_1202_, lean_object* v_opts_1203_, lean_object* v_kind_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(v_env_1202_, v_opts_1203_, v_kind_1204_);
lean_dec(v_kind_1204_);
lean_dec_ref(v_opts_1203_);
lean_dec_ref(v_env_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object* v_env_1206_, lean_object* v_opts_1207_, lean_object* v_kind_1208_){
_start:
{
uint8_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = 0;
lean_inc(v_kind_1208_);
lean_inc_ref(v_env_1206_);
v___x_1210_ = l_Lean_Environment_find_x3f(v_env_1206_, v_kind_1208_, v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec(v_kind_1208_);
lean_dec_ref(v_env_1206_);
return v___x_1209_;
}
else
{
lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_val_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = l_Lean_ConstantInfo_type(v_val_1211_);
lean_dec(v_val_1211_);
v___x_1213_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__11));
v___x_1214_ = l_Lean_Expr_isConstOf(v___x_1212_, v___x_1213_);
lean_dec_ref(v___x_1212_);
if (v___x_1214_ == 0)
{
lean_dec(v_kind_1208_);
lean_dec_ref(v_env_1206_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Environment_evalConst___redArg(v_env_1206_, v_opts_1207_, v_kind_1208_, v___x_1214_);
lean_dec(v_kind_1208_);
lean_dec_ref(v_env_1206_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref_known(v___x_1215_, 1);
return v___x_1209_;
}
else
{
lean_object* v_a_1216_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
if (lean_obj_tag(v_a_1216_) == 4)
{
lean_dec_ref_known(v_a_1216_, 4);
return v___x_1209_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_a_1216_);
lean_dec(v_a_1216_);
return v___x_1217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object* v_env_1218_, lean_object* v_opts_1219_, lean_object* v_kind_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_1218_, v_opts_1219_, v_kind_1220_);
lean_dec_ref(v_opts_1219_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object* v_env_1223_, lean_object* v_kind_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1226_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1225_, v_env_1223_, v_kind_1224_);
v___x_1227_ = l_List_head_x3f___redArg(v___x_1226_);
lean_dec(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object* v_env_1228_, lean_object* v_kind_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Fmt_getConditionalFormatter_x3f(v_env_1228_, v_kind_1229_);
lean_dec(v_kind_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object* v_env_1231_, lean_object* v_kind_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_1234_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1233_, v_env_1231_, v_kind_1232_);
v___x_1235_ = l_List_head_x3f___redArg(v___x_1234_);
lean_dec(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object* v_env_1236_, lean_object* v_kind_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1236_, v_kind_1237_);
lean_dec(v_kind_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object* v_msg_1253_){
_start:
{
lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___f_1254_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0));
v___f_1255_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1));
v___f_1256_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2));
v___f_1257_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3));
v___f_1258_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4));
v___f_1259_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5));
v___f_1260_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6));
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___f_1254_);
lean_ctor_set(v___x_1261_, 1, v___f_1255_);
v___x_1262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___f_1256_);
lean_ctor_set(v___x_1262_, 2, v___f_1257_);
lean_ctor_set(v___x_1262_, 3, v___f_1258_);
lean_ctor_set(v___x_1262_, 4, v___f_1259_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___f_1260_);
v___x_1264_ = ((lean_object*)(l_Lean_Fmt_instInhabitedQuantifierChain_default));
v___x_1265_ = l_instInhabitedOfMonad___redArg(v___x_1263_, v___x_1264_);
v___x_1266_ = lean_panic_fn_borrowed(v___x_1265_, v_msg_1253_);
lean_dec(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object* v_env_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_snd_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1332_; 
v_snd_1269_ = lean_ctor_get(v_a_1268_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1268_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v_a_1268_, 0);
lean_dec(v_unused_1333_);
v___x_1271_ = v_a_1268_;
v_isShared_1272_ = v_isSharedCheck_1332_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snd_1269_);
lean_dec(v_a_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1332_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_snd_1273_; lean_object* v_fst_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1331_; 
v_snd_1273_ = lean_ctor_get(v_snd_1269_, 1);
v_fst_1274_ = lean_ctor_get(v_snd_1269_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_snd_1269_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1276_ = v_snd_1269_;
v_isShared_1277_ = v_isSharedCheck_1331_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1273_);
lean_inc(v_fst_1274_);
lean_dec(v_snd_1269_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1331_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_fst_1274_) == 1)
{
lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1313_; 
v_fst_1278_ = lean_ctor_get(v_snd_1273_, 0);
v_snd_1279_ = lean_ctor_get(v_snd_1273_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_snd_1273_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1281_ = v_snd_1273_;
v_isShared_1282_ = v_isSharedCheck_1313_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_inc(v_fst_1278_);
lean_dec(v_snd_1273_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1313_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_val_1283_; lean_object* v___x_1284_; 
v_val_1283_ = lean_ctor_get(v_fst_1274_, 0);
lean_inc(v_val_1283_);
lean_inc(v_fst_1278_);
v___x_1284_ = lean_apply_1(v_val_1283_, v_fst_1278_);
if (lean_obj_tag(v___x_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v_toQuantifierHeadComponents_1286_; lean_object* v_body_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_fst_1278_);
lean_dec_ref_known(v_fst_1274_, 1);
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_toQuantifierHeadComponents_1286_ = lean_ctor_get(v_val_1285_, 0);
lean_inc_ref(v_toQuantifierHeadComponents_1286_);
v_body_1287_ = lean_ctor_get(v_val_1285_, 1);
lean_inc_n(v_body_1287_, 2);
lean_dec(v_val_1285_);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_array_push(v_snd_1279_, v_toQuantifierHeadComponents_1286_);
v___x_1290_ = l_Lean_Syntax_getKind(v_body_1287_);
lean_inc_ref(v_env_1267_);
v___x_1291_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1267_, v___x_1290_);
lean_dec(v___x_1290_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1289_);
lean_ctor_set(v___x_1281_, 0, v_body_1287_);
v___x_1293_ = v___x_1281_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_body_1287_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1289_);
v___x_1293_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1293_);
lean_ctor_set(v___x_1276_, 0, v___x_1291_);
v___x_1295_ = v___x_1276_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1297_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1295_);
lean_ctor_set(v___x_1271_, 0, v___x_1288_);
v___x_1297_ = v___x_1271_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v_a_1268_ = v___x_1297_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v___x_1284_);
lean_dec_ref(v_env_1267_);
lean_inc(v_fst_1278_);
lean_inc(v_snd_1279_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_snd_1279_);
lean_ctor_set(v___x_1302_, 1, v_fst_1278_);
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
if (v_isShared_1282_ == 0)
{
v___x_1305_ = v___x_1281_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_snd_1279_);
v___x_1305_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1305_);
v___x_1307_ = v___x_1276_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_fst_1274_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1307_);
lean_ctor_set(v___x_1271_, 0, v___x_1303_);
v___x_1309_ = v___x_1271_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v_env_1267_);
v_fst_1314_ = lean_ctor_get(v_snd_1273_, 0);
v_snd_1315_ = lean_ctor_get(v_snd_1273_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_snd_1273_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1317_ = v_snd_1273_;
v_isShared_1318_ = v_isSharedCheck_1330_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_snd_1273_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1330_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_inc(v_fst_1314_);
lean_inc(v_snd_1315_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_snd_1315_);
lean_ctor_set(v___x_1319_, 1, v_fst_1314_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
if (v_isShared_1318_ == 0)
{
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_fst_1314_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_snd_1315_);
v___x_1322_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1322_);
v___x_1324_ = v___x_1276_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_fst_1274_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1324_);
lean_ctor_set(v___x_1271_, 0, v___x_1320_);
v___x_1326_ = v___x_1271_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_1339_ = lean_unsigned_to_nat(2u);
v___x_1340_ = lean_unsigned_to_nat(249u);
v___x_1341_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1));
v___x_1342_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_1343_ = l_mkPanicMessageWithDecl(v___x_1342_, v___x_1341_, v___x_1340_, v___x_1339_, v___x_1338_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object* v_env_1344_, lean_object* v_deconstructQuantifier_x3f_1345_, lean_object* v_stx_1346_){
_start:
{
lean_object* v_deconstructQuantifier_x3f_1347_; lean_object* v_quantifiers_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_fst_1354_; 
v_deconstructQuantifier_x3f_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_deconstructQuantifier_x3f_1347_, 0, v_deconstructQuantifier_x3f_1345_);
v_quantifiers_1348_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0));
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_stx_1346_);
lean_ctor_set(v___x_1350_, 1, v_quantifiers_1348_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_deconstructQuantifier_x3f_1347_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1344_, v___x_1352_);
v_fst_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_fst_1354_);
lean_dec_ref(v___x_1353_);
if (lean_obj_tag(v_fst_1354_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3);
v___x_1356_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; 
v_val_1357_ = lean_ctor_get(v_fst_1354_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v_fst_1354_, 1);
return v_val_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object* v_env_1358_, lean_object* v_inst_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1358_, v_a_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object* v_chainKinds_1362_, lean_object* v_stx_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = l_Lean_Syntax_getNumArgs(v_stx_1363_);
v___x_1365_ = lean_unsigned_to_nat(3u);
v___x_1366_ = lean_nat_dec_eq(v___x_1364_, v___x_1365_);
lean_dec(v___x_1364_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_mk_empty_array_with_capacity(v___x_1367_);
v___x_1369_ = lean_array_push(v___x_1368_, v_stx_1363_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
lean_inc(v_stx_1363_);
v___x_1370_ = l_Lean_Syntax_getKind(v_stx_1363_);
v___x_1371_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_chainKinds_1362_, v___x_1370_);
lean_dec(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_mk_empty_array_with_capacity(v___x_1372_);
v___x_1374_ = lean_array_push(v___x_1373_, v_stx_1363_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v_op_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v_op_1376_ = l_Lean_Syntax_getArg(v_stx_1363_, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_isAtom(v_op_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_op_1376_);
v___x_1378_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1379_ = lean_array_push(v___x_1378_, v_stx_1363_);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; lean_object* v_left_1381_; lean_object* v___x_1382_; lean_object* v_right_1383_; lean_object* v_leftChain_1384_; lean_object* v_rightChain_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1380_ = lean_unsigned_to_nat(0u);
v_left_1381_ = l_Lean_Syntax_getArg(v_stx_1363_, v___x_1380_);
v___x_1382_ = lean_unsigned_to_nat(2u);
v_right_1383_ = l_Lean_Syntax_getArg(v_stx_1363_, v___x_1382_);
lean_dec(v_stx_1363_);
v_leftChain_1384_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_chainKinds_1362_, v_left_1381_);
v_rightChain_1385_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_chainKinds_1362_, v_right_1383_);
v___x_1386_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1387_ = lean_array_push(v___x_1386_, v_op_1376_);
v___x_1388_ = l_Array_append___redArg(v_leftChain_1384_, v___x_1387_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = l_Array_append___redArg(v___x_1388_, v_rightChain_1385_);
lean_dec_ref(v_rightChain_1385_);
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object* v_chainKinds_1390_, lean_object* v_stx_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_chainKinds_1390_, v_stx_1391_);
lean_dec_ref(v_chainKinds_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_a_1396_, lean_object* v_b_1397_){
_start:
{
lean_object* v_it_1399_; lean_object* v_startInclusive_1400_; lean_object* v_endExclusive_1401_; 
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v_currPos_1407_; lean_object* v_searcher_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1512_; 
v_currPos_1407_ = lean_ctor_get(v_a_1396_, 0);
v_searcher_1408_ = lean_ctor_get(v_a_1396_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1410_ = v_a_1396_;
v_isShared_1411_ = v_isSharedCheck_1512_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_searcher_1408_);
lean_inc(v_currPos_1407_);
lean_dec(v_a_1396_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1512_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_it_1413_; lean_object* v_it_1419_; lean_object* v_startPos_1420_; lean_object* v_endPos_1421_; 
switch(lean_obj_tag(v_searcher_1408_))
{
case 0:
{
lean_object* v_pos_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1410_);
v_pos_1434_ = lean_ctor_get(v_searcher_1408_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_searcher_1408_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v_searcher_1408_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_pos_1434_);
lean_dec(v_searcher_1408_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_startInclusive_1438_; lean_object* v_endExclusive_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_startInclusive_1438_ = lean_ctor_get(v___x_1394_, 1);
v_endExclusive_1439_ = lean_ctor_get(v___x_1394_, 2);
v___x_1440_ = lean_nat_sub(v_endExclusive_1439_, v_startInclusive_1438_);
v___x_1441_ = lean_nat_dec_eq(v_pos_1434_, v___x_1440_);
lean_dec(v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_pos_1434_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 1);
v___x_1443_ = v___x_1436_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_pos_1434_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_inc(v_pos_1434_);
v_it_1419_ = v___x_1443_;
v_startPos_1420_ = v_pos_1434_;
v_endPos_1421_ = v_pos_1434_;
goto v___jp_1418_;
}
}
else
{
lean_object* v___x_1445_; 
lean_del_object(v___x_1436_);
v___x_1445_ = lean_box(3);
lean_inc(v_pos_1434_);
v_it_1419_ = v___x_1445_;
v_startPos_1420_ = v_pos_1434_;
v_endPos_1421_ = v_pos_1434_;
goto v___jp_1418_;
}
}
}
case 1:
{
lean_object* v_pos_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_pos_1447_ = lean_ctor_get(v_searcher_1408_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_searcher_1408_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v_searcher_1408_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_pos_1447_);
lean_dec(v_searcher_1408_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_string_utf8_next_fast(v___x_1393_, v_pos_1447_);
lean_dec(v_pos_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v_it_1413_ = v___x_1453_;
goto v___jp_1412_;
}
}
}
case 2:
{
lean_object* v_needle_1456_; lean_object* v_table_1457_; lean_object* v_stackPos_1458_; lean_object* v_needlePos_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1511_; 
v_needle_1456_ = lean_ctor_get(v_searcher_1408_, 0);
v_table_1457_ = lean_ctor_get(v_searcher_1408_, 1);
v_stackPos_1458_ = lean_ctor_get(v_searcher_1408_, 2);
v_needlePos_1459_ = lean_ctor_get(v_searcher_1408_, 3);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_searcher_1408_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1461_ = v_searcher_1408_;
v_isShared_1462_ = v_isSharedCheck_1511_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_needlePos_1459_);
lean_inc(v_stackPos_1458_);
lean_inc(v_table_1457_);
lean_inc(v_needle_1456_);
lean_dec(v_searcher_1408_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1511_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_str_1463_; lean_object* v_startInclusive_1464_; lean_object* v_endExclusive_1465_; lean_object* v_basePos_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_str_1463_ = lean_ctor_get(v_needle_1456_, 0);
v_startInclusive_1464_ = lean_ctor_get(v_needle_1456_, 1);
v_endExclusive_1465_ = lean_ctor_get(v_needle_1456_, 2);
v_basePos_1466_ = lean_nat_sub(v_stackPos_1458_, v_needlePos_1459_);
v___x_1467_ = lean_nat_sub(v_endExclusive_1465_, v_startInclusive_1464_);
v___x_1468_ = lean_nat_add(v_basePos_1466_, v___x_1467_);
v___x_1469_ = lean_nat_dec_le(v___x_1468_, v___x_1395_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
lean_dec(v___x_1467_);
lean_del_object(v___x_1461_);
lean_dec(v_needlePos_1459_);
lean_dec(v_stackPos_1458_);
lean_dec_ref(v_table_1457_);
lean_dec_ref(v_needle_1456_);
v___x_1470_ = lean_nat_dec_lt(v_basePos_1466_, v___x_1395_);
lean_dec(v_basePos_1466_);
if (v___x_1470_ == 0)
{
lean_del_object(v___x_1410_);
goto v___jp_1432_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_box(3);
v_it_1413_ = v___x_1471_;
goto v___jp_1412_;
}
}
else
{
uint8_t v_stackByte_1472_; lean_object* v___x_1473_; uint8_t v_patByte_1474_; uint8_t v___x_1475_; 
lean_dec(v_basePos_1466_);
lean_inc(v_stackPos_1458_);
v_stackByte_1472_ = lean_string_get_byte_fast(v___x_1393_, v_stackPos_1458_);
v___x_1473_ = lean_nat_add(v_startInclusive_1464_, v_needlePos_1459_);
v_patByte_1474_ = lean_string_get_byte_fast(v_str_1463_, v___x_1473_);
v___x_1475_ = lean_uint8_dec_eq(v_stackByte_1472_, v_patByte_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
lean_dec(v___x_1467_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_nat_dec_eq(v_needlePos_1459_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_newNeedlePos_1480_; uint8_t v___x_1481_; 
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_sub(v_needlePos_1459_, v___x_1478_);
lean_dec(v_needlePos_1459_);
v_newNeedlePos_1480_ = lean_array_fget_borrowed(v_table_1457_, v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_nat_dec_eq(v_newNeedlePos_1480_, v___x_1476_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1483_; 
lean_inc(v_newNeedlePos_1480_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v_newNeedlePos_1480_);
v___x_1483_ = v___x_1461_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_needle_1456_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_table_1457_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_stackPos_1458_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_newNeedlePos_1480_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
v_it_1413_ = v___x_1483_;
goto v___jp_1412_;
}
}
else
{
lean_object* v_nextStackPos_1485_; lean_object* v___x_1487_; 
v_nextStackPos_1485_ = l_String_Slice_posGE___redArg(v___x_1394_, v_stackPos_1458_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v___x_1476_);
lean_ctor_set(v___x_1461_, 2, v_nextStackPos_1485_);
v___x_1487_ = v___x_1461_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_needle_1456_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_table_1457_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_nextStackPos_1485_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v___x_1476_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v_it_1413_ = v___x_1487_;
goto v___jp_1412_;
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_nextStackPos_1491_; lean_object* v___x_1493_; 
lean_dec(v_needlePos_1459_);
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_add(v_stackPos_1458_, v___x_1489_);
lean_dec(v_stackPos_1458_);
v_nextStackPos_1491_ = l_String_Slice_posGE___redArg(v___x_1394_, v___x_1490_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v___x_1476_);
lean_ctor_set(v___x_1461_, 2, v_nextStackPos_1491_);
v___x_1493_ = v___x_1461_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_needle_1456_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_table_1457_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_nextStackPos_1491_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v___x_1476_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
v_it_1413_ = v___x_1493_;
goto v___jp_1412_;
}
}
}
else
{
lean_object* v___x_1495_; lean_object* v_nextStackPos_1496_; lean_object* v_nextNeedlePos_1497_; uint8_t v___x_1498_; 
lean_del_object(v___x_1410_);
v___x_1495_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1496_ = lean_nat_add(v_stackPos_1458_, v___x_1495_);
lean_dec(v_stackPos_1458_);
v_nextNeedlePos_1497_ = lean_nat_add(v_needlePos_1459_, v___x_1495_);
lean_dec(v_needlePos_1459_);
v___x_1498_ = lean_nat_dec_eq(v_nextNeedlePos_1497_, v___x_1467_);
lean_dec(v___x_1467_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v_nextNeedlePos_1497_);
lean_ctor_set(v___x_1461_, 2, v_nextStackPos_1496_);
v___x_1500_ = v___x_1461_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_needle_1456_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_table_1457_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_nextStackPos_1496_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_nextNeedlePos_1497_);
v___x_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_currPos_1407_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v_a_1396_ = v___x_1501_;
goto _start;
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1504_ = lean_nat_sub(v_nextStackPos_1496_, v_nextNeedlePos_1497_);
lean_dec(v_nextNeedlePos_1497_);
v___x_1505_ = l_String_Slice_pos_x21(v___x_1394_, v___x_1504_);
lean_dec(v___x_1504_);
v___x_1506_ = l_String_Slice_pos_x21(v___x_1394_, v_nextStackPos_1496_);
v___x_1507_ = lean_unsigned_to_nat(0u);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v___x_1507_);
lean_ctor_set(v___x_1461_, 2, v_nextStackPos_1496_);
v___x_1509_ = v___x_1461_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_needle_1456_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_table_1457_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_nextStackPos_1496_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
v_it_1419_ = v___x_1509_;
v_startPos_1420_ = v___x_1505_;
v_endPos_1421_ = v___x_1506_;
goto v___jp_1418_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1410_);
goto v___jp_1432_;
}
}
v___jp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_it_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_currPos_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_it_1413_);
v___x_1415_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v_a_1396_ = v___x_1415_;
goto _start;
}
}
v___jp_1418_:
{
lean_object* v_slice_1422_; lean_object* v_startInclusive_1423_; lean_object* v_endExclusive_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_slice_1422_ = l_String_Slice_subslice_x21(v___x_1394_, v_currPos_1407_, v_startPos_1420_);
v_startInclusive_1423_ = lean_ctor_get(v_slice_1422_, 0);
v_endExclusive_1424_ = lean_ctor_get(v_slice_1422_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_slice_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v_slice_1422_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_endExclusive_1424_);
lean_inc(v_startInclusive_1423_);
lean_dec(v_slice_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_nextIt_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_it_1419_);
lean_ctor_set(v___x_1426_, 0, v_endPos_1421_);
v_nextIt_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_endPos_1421_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_it_1419_);
v_nextIt_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_it_1399_ = v_nextIt_1429_;
v_startInclusive_1400_ = v_startInclusive_1423_;
v_endExclusive_1401_ = v_endExclusive_1424_;
goto v___jp_1398_;
}
}
}
v___jp_1432_:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(1);
lean_inc(v___x_1395_);
v_it_1399_ = v___x_1433_;
v_startInclusive_1400_ = v_currPos_1407_;
v_endExclusive_1401_ = v___x_1395_;
goto v___jp_1398_;
}
}
}
else
{
lean_dec(v___x_1395_);
lean_dec_ref(v___x_1393_);
return v_b_1397_;
}
v___jp_1398_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v___x_1393_);
v___x_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1393_);
lean_ctor_set(v___x_1402_, 1, v_startInclusive_1400_);
lean_ctor_set(v___x_1402_, 2, v_endExclusive_1401_);
v___x_1403_ = l_String_Slice_toString(v___x_1402_);
lean_dec_ref_known(v___x_1402_, 3);
v___x_1404_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1403_);
v___x_1405_ = lean_array_push(v_b_1397_, v___x_1404_);
v_a_1396_ = v_it_1399_;
v_b_1397_ = v___x_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v_a_1516_, lean_object* v_b_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1513_, v___x_1514_, v___x_1515_, v_a_1516_, v_b_1517_);
lean_dec_ref(v___x_1514_);
return v_res_1518_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtRawAsInSource___closed__3(void){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Fmt_Doc_hardNl(lean_box(0));
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t v_isFallback_1525_, lean_object* v_stx_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
uint8_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = 0;
v___x_1530_ = l_Lean_Syntax_getPos_x3f(v_stx_1526_, v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 1)
{
lean_object* v_val_1531_; lean_object* v___x_1532_; 
v_val_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1526_, v___x_1529_);
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_text_1533_; lean_object* v_val_1534_; lean_object* v_source_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_text_1533_ = lean_ctor_get(v_a_1527_, 1);
v_val_1534_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1532_, 1);
v_source_1535_ = lean_ctor_get(v_text_1533_, 0);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_string_utf8_byte_size(v_source_1535_);
lean_inc_ref(v_source_1535_);
v___x_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1538_, 0, v_source_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
lean_ctor_set(v___x_1538_, 2, v___x_1537_);
v___x_1539_ = l_String_Slice_pos_x3f(v___x_1538_, v_val_1531_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref_known(v___x_1538_, 3);
lean_dec(v_val_1534_);
v___x_1540_ = lean_box(0);
v___x_1541_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1542_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1543_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1543_, 0, v_stx_1526_);
lean_ctor_set(v___x_1543_, 1, v___x_1540_);
lean_ctor_set(v___x_1543_, 2, v___x_1541_);
lean_ctor_set(v___x_1543_, 3, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1528_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1546_; 
v_val_1545_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1546_ = l_String_Slice_pos_x3f(v___x_1538_, v_val_1534_);
lean_dec_ref_known(v___x_1538_, 3);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_val_1545_);
v___x_1547_ = lean_box(0);
v___x_1548_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1549_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1550_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_1550_, 0, v_stx_1526_);
lean_ctor_set(v___x_1550_, 1, v___x_1547_);
lean_ctor_set(v___x_1550_, 2, v___x_1548_);
lean_ctor_set(v___x_1550_, 3, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_a_1528_);
return v___x_1551_;
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_val_1552_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1553_ = lean_string_utf8_extract_fast(v_source_1535_, v_val_1545_, v_val_1552_);
lean_dec(v_val_1552_);
lean_dec(v_val_1545_);
v___x_1554_ = lean_string_utf8_byte_size(v___x_1553_);
lean_inc_ref(v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1536_);
lean_ctor_set(v___x_1555_, 2, v___x_1554_);
v___x_1556_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v___x_1555_);
v___x_1557_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1558_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1553_, v___x_1555_, v___x_1554_, v___x_1556_, v___x_1557_);
lean_dec_ref_known(v___x_1555_, 3);
v___x_1559_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1560_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1559_, v___x_1558_);
v___x_1561_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1529_, v___x_1560_);
v___x_1562_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___x_1561_, v_stx_1526_, v_a_1528_);
lean_dec(v_stx_1526_);
if (lean_obj_tag(v___x_1562_) == 0)
{
if (v_isFallback_1525_ == 0)
{
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_a_1564_ = lean_ctor_get(v___x_1562_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1566_ = v___x_1562_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_a_1564_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v___x_1532_);
lean_dec(v_val_1531_);
v___x_1573_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1574_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1573_, v_stx_1526_, v_a_1528_);
lean_dec(v_stx_1526_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v___x_1530_);
v___x_1575_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1576_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1575_, v_stx_1526_, v_a_1528_);
lean_dec(v_stx_1526_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object* v_isFallback_1577_, lean_object* v_stx_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
uint8_t v_isFallback_boxed_1581_; lean_object* v_res_1582_; 
v_isFallback_boxed_1581_ = lean_unbox(v_isFallback_1577_);
v_res_1582_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_boxed_1581_, v_stx_1578_, v_a_1579_, v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1583_, v___x_1584_, v___x_1585_, v_a_1588_, v_b_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_inst_1594_, lean_object* v_R_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(v___x_1591_, v___x_1592_, v___x_1593_, v_inst_1594_, v_R_1595_, v_a_1596_, v_b_1597_);
lean_dec_ref(v___x_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t v_sz_1599_, size_t v_i_1600_, lean_object* v_bs_1601_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_lt(v_i_1600_, v_sz_1599_);
if (v___x_1602_ == 0)
{
return v_bs_1601_;
}
else
{
lean_object* v_v_1603_; lean_object* v___x_1604_; lean_object* v_bs_x27_1605_; lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v_v_1603_ = lean_array_uget(v_bs_1601_, v_i_1600_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v_bs_x27_1605_ = lean_array_uset(v_bs_1601_, v_i_1600_, v___x_1604_);
v___x_1606_ = l_Lean_Fmt_Doc_text___override___redArg(v_v_1603_);
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1600_, v___x_1607_);
v___x_1609_ = lean_array_uset(v_bs_x27_1605_, v_i_1600_, v___x_1606_);
v_i_1600_ = v___x_1608_;
v_bs_1601_ = v___x_1609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object* v_sz_1611_, lean_object* v_i_1612_, lean_object* v_bs_1613_){
_start:
{
size_t v_sz_boxed_1614_; size_t v_i_boxed_1615_; lean_object* v_res_1616_; 
v_sz_boxed_1614_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1615_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_boxed_1614_, v_i_boxed_1615_, v_bs_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object* v_ctx_1617_, size_t v_sz_1618_, size_t v_i_1619_, lean_object* v_bs_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_usize_dec_lt(v_i_1619_, v_sz_1618_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v_ctx_1617_);
return v_bs_1620_;
}
else
{
lean_object* v_v_1622_; lean_object* v_str_1623_; lean_object* v_startPos_1624_; lean_object* v_stopPos_1625_; lean_object* v_anchorColumnPos_1626_; lean_object* v___x_1627_; lean_object* v_bs_x27_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_v_1622_ = lean_array_uget_borrowed(v_bs_1620_, v_i_1619_);
v_str_1623_ = lean_ctor_get(v_v_1622_, 0);
lean_inc_ref(v_str_1623_);
v_startPos_1624_ = lean_ctor_get(v_v_1622_, 1);
lean_inc(v_startPos_1624_);
v_stopPos_1625_ = lean_ctor_get(v_v_1622_, 2);
lean_inc(v_stopPos_1625_);
v_anchorColumnPos_1626_ = lean_ctor_get(v_ctx_1617_, 0);
v___x_1627_ = lean_unsigned_to_nat(0u);
v_bs_x27_1628_ = lean_array_uset(v_bs_1620_, v_i_1619_, v___x_1627_);
v___x_1629_ = lean_string_utf8_extract(v_str_1623_, v_startPos_1624_, v_stopPos_1625_);
lean_dec(v_stopPos_1625_);
lean_dec(v_startPos_1624_);
lean_dec_ref(v_str_1623_);
lean_inc(v_anchorColumnPos_1626_);
v___x_1630_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(v___x_1629_, v_anchorColumnPos_1626_);
v___x_1631_ = ((size_t)1ULL);
v___x_1632_ = lean_usize_add(v_i_1619_, v___x_1631_);
v___x_1633_ = lean_array_uset(v_bs_x27_1628_, v_i_1619_, v___x_1630_);
v_i_1619_ = v___x_1632_;
v_bs_1620_ = v___x_1633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object* v_ctx_1635_, lean_object* v_sz_1636_, lean_object* v_i_1637_, lean_object* v_bs_1638_){
_start:
{
size_t v_sz_boxed_1639_; size_t v_i_boxed_1640_; lean_object* v_res_1641_; 
v_sz_boxed_1639_ = lean_unbox_usize(v_sz_1636_);
lean_dec(v_sz_1636_);
v_i_boxed_1640_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v_res_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1635_, v_sz_boxed_1639_, v_i_boxed_1640_, v_bs_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object* v_a_1642_, lean_object* v_b_1643_){
_start:
{
lean_object* v_array_1644_; lean_object* v_start_1645_; lean_object* v_stop_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1659_; 
v_array_1644_ = lean_ctor_get(v_a_1642_, 0);
v_start_1645_ = lean_ctor_get(v_a_1642_, 1);
v_stop_1646_ = lean_ctor_get(v_a_1642_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_stop_1646_);
lean_inc(v_start_1645_);
lean_inc(v_array_1644_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_lt(v_start_1645_, v_stop_1646_);
if (v___x_1650_ == 0)
{
lean_del_object(v___x_1648_);
lean_dec(v_stop_1646_);
lean_dec(v_start_1645_);
lean_dec_ref(v_array_1644_);
return v_b_1643_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_add(v_start_1645_, v___x_1651_);
lean_inc_ref(v_array_1644_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___x_1652_);
v___x_1654_ = v___x_1648_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_array_1644_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_stop_1646_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_array_fget(v_array_1644_, v_start_1645_);
lean_dec(v_start_1645_);
lean_dec_ref(v_array_1644_);
v___x_1656_ = lean_array_push(v_b_1643_, v___x_1655_);
v_a_1642_ = v___x_1654_;
v_b_1643_ = v___x_1656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object* v_ctx_1664_, lean_object* v_trailing_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_lastTokenTailPos_1667_; lean_object* v_startPos_1668_; uint8_t v___x_1669_; 
v_lastTokenTailPos_1667_ = lean_ctor_get(v_ctx_1664_, 2);
v_startPos_1668_ = lean_ctor_get(v_trailing_1665_, 1);
v___x_1669_ = lean_nat_dec_le(v_lastTokenTailPos_1667_, v_startPos_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_lines_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_str_1676_; lean_object* v_startPos_1677_; lean_object* v_stopPos_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; size_t v_sz_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v_newLines_1690_; size_t v_sz_1691_; lean_object* v_formatted_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1670_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0));
lean_inc_ref(v_trailing_1665_);
v___x_1671_ = l_Substring_Raw_splitOn(v_trailing_1665_, v___x_1670_);
v_lines_1672_ = lean_array_mk(v___x_1671_);
v___x_1673_ = l_instInhabitedRaw__1;
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_array_get(v___x_1673_, v_lines_1672_, v___x_1674_);
v_str_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_str_1676_);
v_startPos_1677_ = lean_ctor_get(v___x_1675_, 1);
lean_inc(v_startPos_1677_);
v_stopPos_1678_ = lean_ctor_get(v___x_1675_, 2);
lean_inc(v_stopPos_1678_);
lean_dec(v___x_1675_);
v___x_1679_ = lean_string_utf8_extract(v_str_1676_, v_startPos_1677_, v_stopPos_1678_);
lean_dec(v_stopPos_1678_);
lean_dec(v_startPos_1677_);
lean_dec_ref(v_str_1676_);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_mk_empty_array_with_capacity(v___x_1680_);
lean_inc_ref(v___x_1681_);
v___x_1682_ = lean_array_push(v___x_1681_, v___x_1679_);
v___x_1683_ = lean_array_get_size(v_lines_1672_);
v___x_1684_ = l_Array_toSubarray___redArg(v_lines_1672_, v___x_1680_, v___x_1683_);
v___x_1685_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0));
v___x_1686_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v___x_1684_, v___x_1685_);
v_sz_1687_ = lean_array_size(v___x_1686_);
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1664_, v_sz_1687_, v___x_1688_, v___x_1686_);
v_newLines_1690_ = l_Array_append___redArg(v___x_1682_, v___x_1689_);
lean_dec_ref(v___x_1689_);
v_sz_1691_ = lean_array_size(v_newLines_1690_);
v_formatted_1692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1691_, v___x_1688_, v_newLines_1690_);
v___x_1693_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1694_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1693_, v_formatted_1692_);
v___x_1695_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1694_);
v___x_1696_ = l_Lean_Syntax_Range_ofSubstring(v_trailing_1665_);
lean_dec_ref(v_trailing_1665_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_array_push(v___x_1681_, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v_a_1666_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v_trailing_1665_);
lean_dec_ref(v_ctx_1664_);
v___x_1701_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_a_1666_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object* v_ctx_1703_, lean_object* v___trailingTk_1704_, lean_object* v_trailing_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(v_ctx_1703_, v_trailing_1705_, v_a_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object* v_ctx_1709_, lean_object* v___trailingTk_1710_, lean_object* v_trailing_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(v_ctx_1709_, v___trailingTk_1710_, v_trailing_1711_, v_a_1712_, v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v___trailingTk_1710_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object* v_inst_1715_, lean_object* v_R_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v_a_1717_, v_b_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object* v_ctx_1720_, lean_object* v_leading_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_stopPos_1723_; lean_object* v_firstTokenPos_1724_; uint8_t v___x_1725_; 
v_stopPos_1723_ = lean_ctor_get(v_leading_1721_, 2);
v_firstTokenPos_1724_ = lean_ctor_get(v_ctx_1720_, 1);
v___x_1725_ = lean_nat_dec_le(v_stopPos_1723_, v_firstTokenPos_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v_lines_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v_newLines_1731_; size_t v_sz_1732_; lean_object* v_formatted_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1726_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0));
lean_inc_ref(v_leading_1721_);
v___x_1727_ = l_Substring_Raw_splitOn(v_leading_1721_, v___x_1726_);
v_lines_1728_ = lean_array_mk(v___x_1727_);
v_sz_1729_ = lean_array_size(v_lines_1728_);
v___x_1730_ = ((size_t)0ULL);
v_newLines_1731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1720_, v_sz_1729_, v___x_1730_, v_lines_1728_);
v_sz_1732_ = lean_array_size(v_newLines_1731_);
v_formatted_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1732_, v___x_1730_, v_newLines_1731_);
v___x_1734_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1735_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1734_, v_formatted_1733_);
v___x_1736_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_Range_ofSubstring(v_leading_1721_);
lean_dec_ref(v_leading_1721_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1736_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1740_);
v___x_1742_ = lean_array_push(v___x_1741_, v___x_1739_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1722_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v_leading_1721_);
lean_dec_ref(v_ctx_1720_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1722_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object* v_ctx_1746_, lean_object* v___leadingTk_1747_, lean_object* v_leading_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(v_ctx_1746_, v_leading_1748_, v_a_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object* v_ctx_1752_, lean_object* v___leadingTk_1753_, lean_object* v_leading_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(v_ctx_1752_, v___leadingTk_1753_, v_leading_1754_, v_a_1755_, v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v___leadingTk_1753_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object* v_stx_1760_, lean_object* v_token_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = 0;
v___x_1769_ = l_Lean_Syntax_getPos_x3f(v_stx_1760_, v___x_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref(v_token_1761_);
lean_dec(v_stx_1760_);
goto v___jp_1765_;
}
else
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1760_, v___x_1768_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref(v_token_1761_);
lean_dec(v_stx_1760_);
goto v___jp_1765_;
}
else
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1840_; 
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1841_);
v___x_1772_ = v___x_1770_;
v_isShared_1773_ = v_isSharedCheck_1840_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v___x_1770_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1840_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc_ref(v_a_1762_);
v___x_1774_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed), 5, 1);
lean_closure_set(v___x_1774_, 0, v_a_1762_);
lean_inc(v_stx_1760_);
v___x_1775_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_1760_, v___x_1774_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
v_a_1777_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1775_, 2);
lean_inc_ref(v_a_1762_);
v___x_1778_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed), 5, 1);
lean_closure_set(v___x_1778_, 0, v_a_1762_);
lean_inc(v_stx_1760_);
v___x_1779_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_1760_, v___x_1778_, v_a_1763_, v_a_1777_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v_a_1781_; lean_object* v___y_1783_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
v_a_1781_ = lean_ctor_get(v___x_1779_, 1);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1779_, 2);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_string_utf8_byte_size(v_token_1761_);
lean_inc_ref(v_token_1761_);
v___x_1810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1810_, 0, v_token_1761_);
lean_ctor_set(v___x_1810_, 1, v___x_1808_);
lean_ctor_set(v___x_1810_, 2, v___x_1809_);
v___x_1811_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_token_1761_, v___x_1810_, v___x_1809_, v___x_1811_, v___x_1812_);
lean_dec_ref_known(v___x_1810_, 3);
v___x_1814_ = lean_array_get_size(v___x_1813_);
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = lean_nat_dec_eq(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1818_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1817_, v___x_1813_);
v___x_1819_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1768_, v___x_1818_);
v___y_1783_ = v___x_1819_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_array_get(v___x_1820_, v___x_1813_, v___x_1808_);
lean_dec_ref(v___x_1813_);
v___y_1783_ = v___x_1821_;
goto v___jp_1782_;
}
v___jp_1782_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___y_1783_, v_stx_1760_, v_a_1781_);
lean_dec(v_stx_1760_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1798_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_a_1786_ = lean_ctor_get(v___x_1784_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1788_ = v___x_1784_;
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = l_Lean_Fmt_TaggedDoc_append(v_a_1776_, v_a_1785_);
v___x_1791_ = l_Lean_Fmt_TaggedDoc_append(v___x_1790_, v_a_1780_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1791_);
v___x_1793_ = v___x_1772_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1795_ = v___x_1788_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_a_1786_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_a_1780_);
lean_dec(v_a_1776_);
lean_del_object(v___x_1772_);
v_a_1799_ = lean_ctor_get(v___x_1784_, 0);
v_a_1800_ = lean_ctor_get(v___x_1784_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1784_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_inc(v_a_1799_);
lean_dec(v___x_1784_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1799_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1776_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_token_1761_);
lean_dec(v_stx_1760_);
v_a_1822_ = lean_ctor_get(v___x_1779_, 0);
v_a_1823_ = lean_ctor_get(v___x_1779_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1779_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_inc(v_a_1822_);
lean_dec(v___x_1779_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1822_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1772_);
lean_dec_ref(v_token_1761_);
lean_dec(v_stx_1760_);
v_a_1831_ = lean_ctor_get(v___x_1775_, 0);
v_a_1832_ = lean_ctor_get(v___x_1775_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1775_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_inc(v_a_1831_);
lean_dec(v___x_1775_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
v___jp_1765_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___closed__0));
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_a_1764_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object* v_stx_1842_, lean_object* v_token_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1842_, v_token_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1847_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object* v_stx_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
switch(lean_obj_tag(v_stx_1853_))
{
case 0:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v_a_1856_);
return v___x_1858_;
}
case 1:
{
lean_object* v_kind_1859_; lean_object* v_args_1860_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_kind_1859_ = lean_ctor_get(v_stx_1853_, 1);
lean_inc(v_kind_1859_);
v_args_1860_ = lean_ctor_get(v_stx_1853_, 2);
lean_inc_ref(v_args_1860_);
lean_dec_ref_known(v_stx_1853_, 3);
v___x_1913_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__2));
v___x_1914_ = lean_name_eq(v_kind_1859_, v___x_1913_);
lean_dec(v_kind_1859_);
if (v___x_1914_ == 0)
{
v___y_1862_ = v_a_1854_;
v___y_1863_ = v_a_1855_;
v___y_1864_ = v_a_1856_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v_args_1860_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
v___y_1862_ = v_a_1854_;
v___y_1863_ = v_a_1855_;
v___y_1864_ = v_a_1856_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_array_fget(v_args_1860_, v___x_1915_);
lean_dec_ref(v_args_1860_);
v_stx_1853_ = v___x_1918_;
goto _start;
}
}
v___jp_1861_:
{
size_t v_sz_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_sz_1865_ = lean_array_size(v_args_1860_);
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_1865_, v___x_1866_, v_args_1860_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
if (lean_obj_tag(v_a_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1884_; 
v_a_1869_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1885_);
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1883_; 
v_a_1873_ = lean_ctor_get(v_a_1868_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_a_1868_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1875_ = v_a_1868_;
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v_a_1868_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1878_);
v___x_1880_ = v___x_1871_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_a_1869_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1902_; 
v_a_1886_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1903_);
v___x_1888_ = v___x_1867_;
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1867_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1901_; 
v_a_1890_ = lean_ctor_get(v_a_1868_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1868_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1892_ = v_a_1868_;
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v_a_1868_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = l_Lean_Fmt_TaggedDoc_join(v_a_1890_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1896_);
v___x_1898_ = v___x_1888_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_a_1886_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_a_1904_ = lean_ctor_get(v___x_1867_, 0);
v_a_1905_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1867_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_inc(v_a_1904_);
lean_dec(v___x_1867_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
case 2:
{
lean_object* v_val_1920_; lean_object* v___x_1921_; 
v_val_1920_ = lean_ctor_get(v_stx_1853_, 1);
lean_inc_ref(v_val_1920_);
v___x_1921_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1853_, v_val_1920_, v_a_1854_, v_a_1855_, v_a_1856_);
return v___x_1921_;
}
default: 
{
lean_object* v_rawVal_1922_; lean_object* v_str_1923_; lean_object* v_startPos_1924_; lean_object* v_stopPos_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_rawVal_1922_ = lean_ctor_get(v_stx_1853_, 1);
v_str_1923_ = lean_ctor_get(v_rawVal_1922_, 0);
v_startPos_1924_ = lean_ctor_get(v_rawVal_1922_, 1);
v_stopPos_1925_ = lean_ctor_get(v_rawVal_1922_, 2);
v___x_1926_ = lean_string_utf8_extract(v_str_1923_, v_startPos_1924_, v_stopPos_1925_);
v___x_1927_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1853_, v___x_1926_, v_a_1854_, v_a_1855_, v_a_1856_);
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t v_sz_1928_, size_t v_i_1929_, lean_object* v_bs_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_usize_dec_lt(v_i_1929_, v_sz_1928_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_bs_1930_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___y_1933_);
return v___x_1936_;
}
else
{
lean_object* v_v_1937_; lean_object* v___x_1938_; 
v_v_1937_ = lean_array_uget_borrowed(v_bs_1930_, v_i_1929_);
lean_inc(v_v_1937_);
v___x_1938_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_v_1937_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
if (lean_obj_tag(v_a_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_bs_1930_);
v_a_1940_ = lean_ctor_get(v___x_1938_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1956_);
v___x_1942_ = v___x_1938_;
v_isShared_1943_ = v_isSharedCheck_1955_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1955_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1954_; 
v_a_1944_ = lean_ctor_get(v_a_1939_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1939_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1946_ = v_a_1939_;
v_isShared_1947_ = v_isSharedCheck_1954_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v_a_1939_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1954_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1951_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1949_);
v___x_1951_ = v___x_1942_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_a_1940_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v_bs_x27_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v_a_1957_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1938_, 2);
v_a_1958_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v_a_1939_, 1);
v___x_1959_ = lean_unsigned_to_nat(0u);
v_bs_x27_1960_ = lean_array_uset(v_bs_1930_, v_i_1929_, v___x_1959_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_add(v_i_1929_, v___x_1961_);
v___x_1963_ = lean_array_uset(v_bs_x27_1960_, v_i_1929_, v_a_1958_);
v_i_1929_ = v___x_1962_;
v_bs_1930_ = v___x_1963_;
v___y_1933_ = v_a_1957_;
goto _start;
}
}
else
{
lean_object* v_a_1965_; lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_bs_1930_);
v_a_1965_ = lean_ctor_get(v___x_1938_, 0);
v_a_1966_ = lean_ctor_get(v___x_1938_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1938_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_inc(v_a_1965_);
lean_dec(v___x_1938_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1965_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_bs_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
size_t v_sz_boxed_1980_; size_t v_i_boxed_1981_; lean_object* v_res_1982_; 
v_sz_boxed_1980_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1981_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_boxed_1980_, v_i_boxed_1981_, v_bs_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object* v_stx_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object* v_stx_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
uint8_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = 0;
v___x_1992_ = l_Lean_Syntax_getPos_x3f(v_stx_1988_, v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 1)
{
lean_object* v_val_1993_; lean_object* v___x_1994_; 
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1988_, v___x_1991_);
if (lean_obj_tag(v___x_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1996_; 
v_val_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v___x_1996_ = l_Lean_Fmt_getLineInfos(v_val_1993_, v_val_1995_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2009_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_a_1998_ = lean_ctor_get(v___x_1996_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2000_ = v___x_1996_;
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_array_get_size(v_a_1997_);
lean_dec(v_a_1997_);
v___x_2004_ = lean_nat_dec_lt(v___x_2002_, v___x_2003_);
v___x_2005_ = lean_box(v___x_2004_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2005_);
v___x_2007_ = v___x_2000_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_1998_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2010_ = lean_ctor_get(v___x_1996_, 0);
v_a_2011_ = lean_ctor_get(v___x_1996_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1996_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_dec(v___x_1996_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec(v___x_1994_);
lean_dec(v_val_1993_);
v___x_2019_ = lean_box(v___x_1991_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_a_1990_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v___x_1992_);
v___x_2021_ = lean_box(v___x_1991_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v_a_1990_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object* v_stx_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_2023_, v_a_2024_, v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_stx_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object* v_msg_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_panic_fn_borrowed(v___x_2028_, v_msg_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object* v_x2_2030_, lean_object* v_as_2031_, size_t v_i_2032_, size_t v_stop_2033_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_usize_dec_eq(v_i_2032_, v_stop_2033_);
if (v___x_2034_ == 0)
{
lean_object* v_startPos_2035_; lean_object* v___x_2036_; lean_object* v_start_2037_; uint8_t v___x_2038_; uint8_t v___x_2039_; 
v_startPos_2035_ = lean_ctor_get(v_x2_2030_, 4);
v___x_2036_ = lean_array_uget_borrowed(v_as_2031_, v_i_2032_);
v_start_2037_ = lean_ctor_get(v___x_2036_, 0);
v___x_2038_ = 1;
v___x_2039_ = lean_nat_dec_le(v_startPos_2035_, v_start_2037_);
if (v___x_2039_ == 0)
{
return v___x_2038_;
}
else
{
if (v___x_2034_ == 0)
{
size_t v___x_2040_; size_t v___x_2041_; 
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2032_, v___x_2040_);
v_i_2032_ = v___x_2041_;
goto _start;
}
else
{
return v___x_2038_;
}
}
}
else
{
uint8_t v___x_2043_; 
v___x_2043_ = 0;
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object* v_x2_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_){
_start:
{
size_t v_i_boxed_2048_; size_t v_stop_boxed_2049_; uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_i_boxed_2048_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2049_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v_x2_2044_, v_as_2045_, v_i_boxed_2048_, v_stop_boxed_2049_);
lean_dec_ref(v_as_2045_);
lean_dec_ref(v_x2_2044_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object* v_as_2052_, size_t v_i_2053_, size_t v_stop_2054_, lean_object* v_b_2055_){
_start:
{
lean_object* v___y_2057_; uint8_t v___x_2061_; 
v___x_2061_ = lean_usize_dec_eq(v_i_2053_, v_stop_2054_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v_tokenRanges_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2062_ = lean_array_uget_borrowed(v_as_2052_, v_i_2053_);
v_tokenRanges_2068_ = lean_ctor_get(v___x_2062_, 3);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_array_get_size(v_tokenRanges_2068_);
v___x_2071_ = lean_nat_dec_lt(v___x_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
goto v___jp_2063_;
}
else
{
if (v___x_2071_ == 0)
{
goto v___jp_2063_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_of_nat(v___x_2070_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v___x_2062_, v_tokenRanges_2068_, v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
goto v___jp_2063_;
}
else
{
v___y_2057_ = v_b_2055_;
goto v___jp_2056_;
}
}
}
v___jp_2063_:
{
lean_object* v_length_2064_; lean_object* v_indentation_2065_; uint8_t v___x_2066_; 
v_length_2064_ = lean_ctor_get(v___x_2062_, 0);
v_indentation_2065_ = lean_ctor_get(v___x_2062_, 1);
v___x_2066_ = lean_nat_dec_lt(v_indentation_2065_, v_length_2064_);
if (v___x_2066_ == 0)
{
v___y_2057_ = v_b_2055_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2067_; 
lean_inc(v___x_2062_);
v___x_2067_ = lean_array_push(v_b_2055_, v___x_2062_);
v___y_2057_ = v___x_2067_;
goto v___jp_2056_;
}
}
}
else
{
return v_b_2055_;
}
v___jp_2056_:
{
size_t v___x_2058_; size_t v___x_2059_; 
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2053_, v___x_2058_);
v_i_2053_ = v___x_2059_;
v_b_2055_ = v___y_2057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object* v_as_2075_, lean_object* v_i_2076_, lean_object* v_stop_2077_, lean_object* v_b_2078_){
_start:
{
size_t v_i_boxed_2079_; size_t v_stop_boxed_2080_; lean_object* v_res_2081_; 
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_stop_boxed_2080_ = lean_unbox_usize(v_stop_2077_);
lean_dec(v_stop_2077_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v_as_2075_, v_i_boxed_2079_, v_stop_boxed_2080_, v_b_2078_);
lean_dec_ref(v_as_2075_);
return v_res_2081_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2082_, lean_object* v___x_2083_, lean_object* v_as_2084_, size_t v_i_2085_, size_t v_stop_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_eq(v_i_2085_, v_stop_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2088_ = 1;
v___x_2089_ = lean_array_uget_borrowed(v_as_2084_, v_i_2085_);
v___x_2090_ = lean_nat_dec_le(v___x_2082_, v___x_2089_);
if (v___x_2090_ == 0)
{
return v___x_2088_;
}
else
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_nat_dec_le(v___x_2082_, v___x_2083_);
if (v___x_2091_ == 0)
{
size_t v___x_2092_; size_t v___x_2093_; 
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2085_, v___x_2092_);
v_i_2085_ = v___x_2093_;
goto _start;
}
else
{
return v___x_2088_;
}
}
}
else
{
uint8_t v___x_2095_; 
v___x_2095_ = 0;
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v_as_2098_, lean_object* v_i_2099_, lean_object* v_stop_2100_){
_start:
{
size_t v_i_boxed_2101_; size_t v_stop_boxed_2102_; uint8_t v_res_2103_; lean_object* v_r_2104_; 
v_i_boxed_2101_ = lean_unbox_usize(v_i_2099_);
lean_dec(v_i_2099_);
v_stop_boxed_2102_ = lean_unbox_usize(v_stop_2100_);
lean_dec(v_stop_2100_);
v_res_2103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2096_, v___x_2097_, v_as_2098_, v_i_boxed_2101_, v_stop_boxed_2102_);
lean_dec_ref(v_as_2098_);
lean_dec(v___x_2097_);
lean_dec(v___x_2096_);
v_r_2104_ = lean_box(v_res_2103_);
return v_r_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_bs_2107_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
if (v___x_2108_ == 0)
{
return v_bs_2107_;
}
else
{
lean_object* v_v_2109_; lean_object* v_indentation_2110_; lean_object* v___x_2111_; lean_object* v_bs_x27_2112_; size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v_v_2109_ = lean_array_uget_borrowed(v_bs_2107_, v_i_2106_);
v_indentation_2110_ = lean_ctor_get(v_v_2109_, 1);
lean_inc(v_indentation_2110_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v_bs_x27_2112_ = lean_array_uset(v_bs_2107_, v_i_2106_, v___x_2111_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_i_2106_, v___x_2113_);
v___x_2115_ = lean_array_uset(v_bs_x27_2112_, v_i_2106_, v_indentation_2110_);
v_i_2106_ = v___x_2114_;
v_bs_2107_ = v___x_2115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2117_, lean_object* v_i_2118_, lean_object* v_bs_2119_){
_start:
{
size_t v_sz_boxed_2120_; size_t v_i_boxed_2121_; lean_object* v_res_2122_; 
v_sz_boxed_2120_ = lean_unbox_usize(v_sz_2117_);
lean_dec(v_sz_2117_);
v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2120_, v_i_boxed_2121_, v_bs_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_, lean_object* v_b_2126_){
_start:
{
lean_object* v___y_2128_; uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = lean_array_uget_borrowed(v_as_2123_, v_i_2124_);
v___x_2134_ = lean_nat_dec_le(v_b_2126_, v___x_2133_);
if (v___x_2134_ == 0)
{
v___y_2128_ = v___x_2133_;
goto v___jp_2127_;
}
else
{
v___y_2128_ = v_b_2126_;
goto v___jp_2127_;
}
}
else
{
lean_inc(v_b_2126_);
return v_b_2126_;
}
v___jp_2127_:
{
size_t v___x_2129_; size_t v___x_2130_; 
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_add(v_i_2124_, v___x_2129_);
v_i_2124_ = v___x_2130_;
v_b_2126_ = v___y_2128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2135_, lean_object* v_i_2136_, lean_object* v_stop_2137_, lean_object* v_b_2138_){
_start:
{
size_t v_i_boxed_2139_; size_t v_stop_boxed_2140_; lean_object* v_res_2141_; 
v_i_boxed_2139_ = lean_unbox_usize(v_i_2136_);
lean_dec(v_i_2136_);
v_stop_boxed_2140_ = lean_unbox_usize(v_stop_2137_);
lean_dec(v_stop_2137_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2135_, v_i_boxed_2139_, v_stop_boxed_2140_, v_b_2138_);
lean_dec(v_b_2138_);
lean_dec_ref(v_as_2135_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_array_fget_borrowed(v_arr_2142_, v___x_2143_);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_array_get_size(v_arr_2142_);
v___x_2147_ = lean_nat_dec_lt(v___x_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_inc(v___x_2144_);
return v___x_2144_;
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_nat_dec_le(v___x_2146_, v___x_2146_);
if (v___x_2148_ == 0)
{
if (v___x_2147_ == 0)
{
lean_inc(v___x_2144_);
return v___x_2144_;
}
else
{
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((size_t)1ULL);
v___x_2150_ = lean_usize_of_nat(v___x_2146_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2142_, v___x_2149_, v___x_2150_, v___x_2144_);
return v___x_2151_;
}
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((size_t)1ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2146_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2142_, v___x_2152_, v___x_2153_, v___x_2144_);
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2155_);
lean_dec_ref(v_arr_2155_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = lean_array_get_size(v_arr_2157_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_nat_dec_eq(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2157_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2164_);
lean_dec_ref(v_arr_2164_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2166_, lean_object* v_stx_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_rawDoc_2171_; lean_object* v___y_2172_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2191_; lean_object* v___y_2192_; uint8_t v___y_2193_; uint8_t v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = 0;
v___x_2196_ = l_Lean_Syntax_getPos_x3f(v_stx_2167_, v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; 
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2167_, v___x_2195_);
if (lean_obj_tag(v___x_2198_) == 1)
{
lean_object* v_val_2199_; lean_object* v___x_2200_; 
v_val_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_n(v_val_2199_, 2);
lean_dec_ref_known(v___x_2198_, 1);
lean_inc(v_val_2197_);
v___x_2200_ = l_Lean_Fmt_getLineInfos(v_val_2197_, v_val_2199_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_indentation_2206_; lean_object* v_line_2207_; lean_object* v_startPos_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; size_t v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2237_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
v_a_2202_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2200_, 2);
v___x_2203_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_array_get_borrowed(v___x_2203_, v_a_2201_, v___x_2204_);
v_indentation_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_indentation_2206_);
v_line_2207_ = lean_ctor_get(v___x_2205_, 2);
v_startPos_2208_ = lean_ctor_get(v___x_2205_, 4);
v___x_2209_ = lean_nat_sub(v_val_2197_, v_startPos_2208_);
v___x_2210_ = l_String_Pos_Raw_offsetOfPosAux(v_line_2207_, v___x_2209_, v___x_2204_, v___x_2204_);
lean_dec(v___x_2209_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_array_get_size(v_a_2201_);
v___x_2251_ = l_Array_toSubarray___redArg(v_a_2201_, v___x_2249_, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2253_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2251_, v___x_2252_);
v___x_2254_ = lean_array_get_size(v___x_2253_);
v___x_2255_ = lean_nat_dec_lt(v___x_2204_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_dec_ref(v___x_2253_);
v___y_2237_ = v___x_2252_;
goto v___jp_2236_;
}
else
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_nat_dec_le(v___x_2254_, v___x_2254_);
if (v___x_2256_ == 0)
{
if (v___x_2255_ == 0)
{
lean_dec_ref(v___x_2253_);
v___y_2237_ = v___x_2252_;
goto v___jp_2236_;
}
else
{
size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = lean_usize_of_nat(v___x_2254_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2253_, v___x_2257_, v___x_2258_, v___x_2252_);
lean_dec_ref(v___x_2253_);
v___y_2237_ = v___x_2259_;
goto v___jp_2236_;
}
}
else
{
size_t v___x_2260_; size_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = ((size_t)0ULL);
v___x_2261_ = lean_usize_of_nat(v___x_2254_);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2253_, v___x_2260_, v___x_2261_, v___x_2252_);
lean_dec_ref(v___x_2253_);
v___y_2237_ = v___x_2262_;
goto v___jp_2236_;
}
}
v___jp_2211_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___y_2214_);
lean_ctor_set(v___x_2215_, 1, v_val_2197_);
lean_ctor_set(v___x_2215_, 2, v_val_2199_);
lean_inc(v_stx_2167_);
v___x_2216_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2167_, v___x_2215_, v_a_2168_, v_a_2202_);
lean_dec_ref_known(v___x_2215_, 3);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
if (lean_obj_tag(v_a_2217_) == 1)
{
lean_object* v_a_2218_; lean_object* v_a_2219_; uint8_t v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2216_, 2);
v_a_2219_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v_a_2217_, 1);
v___x_2220_ = lean_nat_dec_le(v___x_2210_, v_indentation_2206_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_array_get_size(v___y_2213_);
v___x_2222_ = lean_nat_dec_lt(v___x_2204_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_dec_ref(v___y_2213_);
lean_dec(v___x_2210_);
lean_dec(v_indentation_2206_);
v___y_2185_ = v_a_2219_;
v___y_2186_ = v_a_2218_;
goto v___jp_2184_;
}
else
{
if (v___x_2222_ == 0)
{
lean_dec_ref(v___y_2213_);
lean_dec(v___x_2210_);
lean_dec(v_indentation_2206_);
v___y_2185_ = v_a_2219_;
v___y_2186_ = v_a_2218_;
goto v___jp_2184_;
}
else
{
size_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = lean_usize_of_nat(v___x_2221_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2210_, v_indentation_2206_, v___y_2213_, v___y_2212_, v___x_2223_);
lean_dec_ref(v___y_2213_);
lean_dec(v_indentation_2206_);
lean_dec(v___x_2210_);
if (v___x_2224_ == 0)
{
v___y_2185_ = v_a_2219_;
v___y_2186_ = v_a_2218_;
goto v___jp_2184_;
}
else
{
v___y_2191_ = v_a_2219_;
v___y_2192_ = v_a_2218_;
v___y_2193_ = v___x_2220_;
goto v___jp_2190_;
}
}
}
}
else
{
lean_dec_ref(v___y_2213_);
lean_dec(v___x_2210_);
lean_dec(v_indentation_2206_);
v___y_2191_ = v_a_2219_;
v___y_2192_ = v_a_2218_;
v___y_2193_ = v___x_2220_;
goto v___jp_2190_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
lean_dec(v_a_2217_);
lean_dec_ref(v___y_2213_);
lean_dec(v___x_2210_);
lean_dec(v_indentation_2206_);
v_a_2225_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2216_, 2);
v___x_2226_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_2166_, v_stx_2167_, v_a_2168_, v_a_2225_);
return v___x_2226_;
}
}
else
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v___y_2213_);
lean_dec(v___x_2210_);
lean_dec(v_indentation_2206_);
lean_dec(v_stx_2167_);
v_a_2227_ = lean_ctor_get(v___x_2216_, 0);
v_a_2228_ = lean_ctor_get(v___x_2216_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2216_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_inc(v_a_2227_);
lean_dec(v___x_2216_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2227_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
v___jp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; size_t v_sz_2241_; size_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_mk_empty_array_with_capacity(v___x_2238_);
lean_inc(v___x_2210_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2210_);
v_sz_2241_ = lean_array_size(v___y_2237_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2241_, v___x_2242_, v___y_2237_);
v___x_2244_ = l_Array_append___redArg(v___x_2240_, v___x_2243_);
v___x_2245_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2244_);
lean_dec_ref(v___x_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2247_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2246_);
v___y_2212_ = v___x_2242_;
v___y_2213_ = v___x_2243_;
v___y_2214_ = v___x_2247_;
goto v___jp_2211_;
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2245_, 1);
v___y_2212_ = v___x_2242_;
v___y_2213_ = v___x_2243_;
v___y_2214_ = v_val_2248_;
goto v___jp_2211_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_val_2199_);
lean_dec(v_val_2197_);
lean_dec(v_stx_2167_);
v_a_2263_ = lean_ctor_get(v___x_2200_, 0);
v_a_2264_ = lean_ctor_get(v___x_2200_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2200_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_inc(v_a_2263_);
lean_dec(v___x_2200_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2263_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v___x_2198_);
lean_dec(v_val_2197_);
v___x_2272_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2273_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2272_, v_stx_2167_, v_a_2169_);
lean_dec(v_stx_2167_);
return v___x_2273_;
}
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v___x_2196_);
v___x_2274_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2275_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2274_, v_stx_2167_, v_a_2169_);
lean_dec(v_stx_2167_);
return v___x_2275_;
}
v___jp_2170_:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_rawDoc_2171_, v_stx_2167_, v___y_2172_);
lean_dec(v_stx_2167_);
if (lean_obj_tag(v___x_2173_) == 0)
{
if (v_isFallback_2166_ == 0)
{
return v___x_2173_;
}
else
{
lean_object* v_a_2174_; lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2183_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_a_2175_ = lean_ctor_get(v___x_2173_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2177_ = v___x_2173_;
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_2174_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2175_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
return v___x_2173_;
}
}
v___jp_2184_:
{
lean_object* v_doc_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_doc_2187_ = lean_ctor_get(v___y_2185_, 0);
lean_inc(v_doc_2187_);
lean_dec_ref(v___y_2185_);
v___x_2188_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2187_);
v___x_2189_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2188_);
v_rawDoc_2171_ = v___x_2189_;
v___y_2172_ = v___y_2186_;
goto v___jp_2170_;
}
v___jp_2190_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2191_);
v_rawDoc_2171_ = v___x_2194_;
v___y_2172_ = v___y_2192_;
goto v___jp_2170_;
}
else
{
v___y_2185_ = v___y_2191_;
v___y_2186_ = v___y_2192_;
goto v___jp_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2276_, lean_object* v_stx_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
uint8_t v_isFallback_boxed_2280_; lean_object* v_res_2281_; 
v_isFallback_boxed_2280_ = lean_unbox(v_isFallback_2276_);
v_res_2281_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2280_, v_stx_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_a_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2282_, lean_object* v_h_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2285_, lean_object* v_h_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2285_, v_h_2286_);
lean_dec_ref(v_arr_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2288_, lean_object* v_____r_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_a_2288_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2294_, lean_object* v_____r_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2294_, v_____r_2295_, v___y_2296_, v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2299_, lean_object* v_b_2300_, lean_object* v_x_2301_){
_start:
{
if (lean_obj_tag(v_x_2301_) == 0)
{
lean_dec(v_b_2300_);
lean_dec_ref(v_a_2299_);
return v_x_2301_;
}
else
{
lean_object* v_key_2302_; lean_object* v_value_2303_; lean_object* v_tail_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2316_; 
v_key_2302_ = lean_ctor_get(v_x_2301_, 0);
v_value_2303_ = lean_ctor_get(v_x_2301_, 1);
v_tail_2304_ = lean_ctor_get(v_x_2301_, 2);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_x_2301_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2306_ = v_x_2301_;
v_isShared_2307_ = v_isSharedCheck_2316_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_tail_2304_);
lean_inc(v_value_2303_);
lean_inc(v_key_2302_);
lean_dec(v_x_2301_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2316_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
uint8_t v___x_2308_; 
v___x_2308_ = l_Lean_Syntax_instBEqRange_beq(v_key_2302_, v_a_2299_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2299_, v_b_2300_, v_tail_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 2, v___x_2309_);
v___x_2311_ = v___x_2306_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_key_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_value_2303_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_object* v___x_2314_; 
lean_dec(v_value_2303_);
lean_dec(v_key_2302_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v_b_2300_);
lean_ctor_set(v___x_2306_, 0, v_a_2299_);
v___x_2314_ = v___x_2306_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2299_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_b_2300_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_tail_2304_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
return v_x_2317_;
}
else
{
lean_object* v_key_2319_; lean_object* v_value_2320_; lean_object* v_tail_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2344_; 
v_key_2319_ = lean_ctor_get(v_x_2318_, 0);
v_value_2320_ = lean_ctor_get(v_x_2318_, 1);
v_tail_2321_ = lean_ctor_get(v_x_2318_, 2);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_x_2318_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2323_ = v_x_2318_;
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_tail_2321_);
lean_inc(v_value_2320_);
lean_inc(v_key_2319_);
lean_dec(v_x_2318_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; uint64_t v___x_2326_; uint64_t v___x_2327_; uint64_t v___x_2328_; uint64_t v_fold_2329_; uint64_t v___x_2330_; uint64_t v___x_2331_; uint64_t v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; size_t v___x_2335_; size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2325_ = lean_array_get_size(v_x_2317_);
v___x_2326_ = l_Lean_Syntax_instHashableRange_hash(v_key_2319_);
v___x_2327_ = 32ULL;
v___x_2328_ = lean_uint64_shift_right(v___x_2326_, v___x_2327_);
v_fold_2329_ = lean_uint64_xor(v___x_2326_, v___x_2328_);
v___x_2330_ = 16ULL;
v___x_2331_ = lean_uint64_shift_right(v_fold_2329_, v___x_2330_);
v___x_2332_ = lean_uint64_xor(v_fold_2329_, v___x_2331_);
v___x_2333_ = lean_uint64_to_usize(v___x_2332_);
v___x_2334_ = lean_usize_of_nat(v___x_2325_);
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_sub(v___x_2334_, v___x_2335_);
v___x_2337_ = lean_usize_land(v___x_2333_, v___x_2336_);
v___x_2338_ = lean_array_uget_borrowed(v_x_2317_, v___x_2337_);
lean_inc(v___x_2338_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 2, v___x_2338_);
v___x_2340_ = v___x_2323_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_key_2319_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_value_2320_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_array_uset(v_x_2317_, v___x_2337_, v___x_2340_);
v_x_2317_ = v___x_2341_;
v_x_2318_ = v_tail_2321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2345_, lean_object* v_source_2346_, lean_object* v_target_2347_){
_start:
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_array_get_size(v_source_2346_);
v___x_2349_ = lean_nat_dec_lt(v_i_2345_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v_source_2346_);
lean_dec(v_i_2345_);
return v_target_2347_;
}
else
{
lean_object* v_es_2350_; lean_object* v___x_2351_; lean_object* v_source_2352_; lean_object* v_target_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_es_2350_ = lean_array_fget(v_source_2346_, v_i_2345_);
v___x_2351_ = lean_box(0);
v_source_2352_ = lean_array_fset(v_source_2346_, v_i_2345_, v___x_2351_);
v_target_2353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2347_, v_es_2350_);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_i_2345_, v___x_2354_);
lean_dec(v_i_2345_);
v_i_2345_ = v___x_2355_;
v_source_2346_ = v_source_2352_;
v_target_2347_ = v_target_2353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v_nbuckets_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2358_ = lean_array_get_size(v_data_2357_);
v___x_2359_ = lean_unsigned_to_nat(2u);
v_nbuckets_2360_ = lean_nat_mul(v___x_2358_, v___x_2359_);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_mk_array(v_nbuckets_2360_, v___x_2362_);
v___x_2364_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2361_, v_data_2357_, v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2365_, lean_object* v_x_2366_){
_start:
{
if (lean_obj_tag(v_x_2366_) == 0)
{
uint8_t v___x_2367_; 
v___x_2367_ = 0;
return v___x_2367_;
}
else
{
lean_object* v_key_2368_; lean_object* v_tail_2369_; uint8_t v___x_2370_; 
v_key_2368_ = lean_ctor_get(v_x_2366_, 0);
v_tail_2369_ = lean_ctor_get(v_x_2366_, 2);
v___x_2370_ = l_Lean_Syntax_instBEqRange_beq(v_key_2368_, v_a_2365_);
if (v___x_2370_ == 0)
{
v_x_2366_ = v_tail_2369_;
goto _start;
}
else
{
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2372_, lean_object* v_x_2373_){
_start:
{
uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_res_2374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2372_, v_x_2373_);
lean_dec(v_x_2373_);
lean_dec_ref(v_a_2372_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2376_, lean_object* v_a_2377_, lean_object* v_b_2378_){
_start:
{
lean_object* v_size_2379_; lean_object* v_buckets_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2423_; 
v_size_2379_ = lean_ctor_get(v_m_2376_, 0);
v_buckets_2380_ = lean_ctor_get(v_m_2376_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_m_2376_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2382_ = v_m_2376_;
v_isShared_2383_ = v_isSharedCheck_2423_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_buckets_2380_);
lean_inc(v_size_2379_);
lean_dec(v_m_2376_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2423_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; uint64_t v___x_2385_; uint64_t v___x_2386_; uint64_t v___x_2387_; uint64_t v_fold_2388_; uint64_t v___x_2389_; uint64_t v___x_2390_; uint64_t v___x_2391_; size_t v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; size_t v___x_2396_; lean_object* v_bkt_2397_; uint8_t v___x_2398_; 
v___x_2384_ = lean_array_get_size(v_buckets_2380_);
v___x_2385_ = l_Lean_Syntax_instHashableRange_hash(v_a_2377_);
v___x_2386_ = 32ULL;
v___x_2387_ = lean_uint64_shift_right(v___x_2385_, v___x_2386_);
v_fold_2388_ = lean_uint64_xor(v___x_2385_, v___x_2387_);
v___x_2389_ = 16ULL;
v___x_2390_ = lean_uint64_shift_right(v_fold_2388_, v___x_2389_);
v___x_2391_ = lean_uint64_xor(v_fold_2388_, v___x_2390_);
v___x_2392_ = lean_uint64_to_usize(v___x_2391_);
v___x_2393_ = lean_usize_of_nat(v___x_2384_);
v___x_2394_ = ((size_t)1ULL);
v___x_2395_ = lean_usize_sub(v___x_2393_, v___x_2394_);
v___x_2396_ = lean_usize_land(v___x_2392_, v___x_2395_);
v_bkt_2397_ = lean_array_uget_borrowed(v_buckets_2380_, v___x_2396_);
v___x_2398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2377_, v_bkt_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v_size_x27_2400_; lean_object* v___x_2401_; lean_object* v_buckets_x27_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2399_ = lean_unsigned_to_nat(1u);
v_size_x27_2400_ = lean_nat_add(v_size_2379_, v___x_2399_);
lean_dec(v_size_2379_);
lean_inc(v_bkt_2397_);
v___x_2401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2401_, 0, v_a_2377_);
lean_ctor_set(v___x_2401_, 1, v_b_2378_);
lean_ctor_set(v___x_2401_, 2, v_bkt_2397_);
v_buckets_x27_2402_ = lean_array_uset(v_buckets_2380_, v___x_2396_, v___x_2401_);
v___x_2403_ = lean_unsigned_to_nat(4u);
v___x_2404_ = lean_nat_mul(v_size_x27_2400_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(3u);
v___x_2406_ = lean_nat_div(v___x_2404_, v___x_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_array_get_size(v_buckets_x27_2402_);
v___x_2408_ = lean_nat_dec_le(v___x_2406_, v___x_2407_);
lean_dec(v___x_2406_);
if (v___x_2408_ == 0)
{
lean_object* v_val_2409_; lean_object* v___x_2411_; 
v_val_2409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2402_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v_val_2409_);
lean_ctor_set(v___x_2382_, 0, v_size_x27_2400_);
v___x_2411_ = v___x_2382_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_size_x27_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_val_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
else
{
lean_object* v___x_2414_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v_buckets_x27_2402_);
lean_ctor_set(v___x_2382_, 0, v_size_x27_2400_);
v___x_2414_ = v___x_2382_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_size_x27_2400_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_buckets_x27_2402_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
lean_object* v___x_2416_; lean_object* v_buckets_x27_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
lean_inc(v_bkt_2397_);
v___x_2416_ = lean_box(0);
v_buckets_x27_2417_ = lean_array_uset(v_buckets_2380_, v___x_2396_, v___x_2416_);
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2377_, v_b_2378_, v_bkt_2397_);
v___x_2419_ = lean_array_uset(v_buckets_x27_2417_, v___x_2396_, v___x_2418_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v___x_2419_);
v___x_2421_ = v___x_2382_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_size_2379_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2424_, lean_object* v_formatterName_2425_, lean_object* v_stx_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___y_2430_; lean_object* v_a_2442_; lean_object* v_a_2443_; lean_object* v___x_2476_; 
lean_inc_ref(v_a_2427_);
lean_inc(v_stx_2426_);
v___x_2476_ = lean_apply_3(v_f_2424_, v_stx_2426_, v_a_2427_, v_a_2428_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2476_, 2);
v___x_2479_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2477_, v_stx_2426_, v_a_2478_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_stx_2426_);
lean_dec(v_formatterName_2425_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 1);
v_a_2481_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2483_ = v___x_2479_;
v_isShared_2484_ = v_isSharedCheck_2504_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2480_);
lean_inc(v_a_2481_);
lean_dec(v___x_2479_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2504_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_toBacktrackableState_2485_; lean_object* v_shareCommonState_2486_; lean_object* v_freshTagId_2487_; lean_object* v_missingFormatters_2488_; lean_object* v_partialFormatters_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2503_; 
v_toBacktrackableState_2485_ = lean_ctor_get(v_a_2480_, 0);
v_shareCommonState_2486_ = lean_ctor_get(v_a_2480_, 1);
v_freshTagId_2487_ = lean_ctor_get(v_a_2480_, 2);
v_missingFormatters_2488_ = lean_ctor_get(v_a_2480_, 3);
v_partialFormatters_2489_ = lean_ctor_get(v_a_2480_, 4);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2480_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2491_ = v_a_2480_;
v_isShared_2492_ = v_isSharedCheck_2503_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_partialFormatters_2489_);
lean_inc(v_missingFormatters_2488_);
lean_inc(v_freshTagId_2487_);
lean_inc(v_shareCommonState_2486_);
lean_inc(v_toBacktrackableState_2485_);
lean_dec(v_a_2480_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2503_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2498_; 
v___x_2493_ = l_Lean_ShareCommon_objectFactory;
v___x_2494_ = lean_state_sharecommon(v___x_2493_, v_shareCommonState_2486_, v_a_2481_);
v_fst_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_fst_2495_);
v_snd_2496_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2496_);
lean_dec_ref(v___x_2494_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_snd_2496_);
v___x_2498_ = v___x_2491_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_toBacktrackableState_2485_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_snd_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_freshTagId_2487_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_missingFormatters_2488_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_partialFormatters_2489_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 1, v___x_2498_);
lean_ctor_set(v___x_2483_, 0, v_fst_2495_);
v___x_2500_ = v___x_2483_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_fst_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v_a_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2505_);
v_a_2506_ = lean_ctor_get(v___x_2479_, 1);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2479_, 2);
v_a_2442_ = v_a_2505_;
v_a_2443_ = v_a_2506_;
goto v___jp_2441_;
}
}
else
{
lean_object* v_a_2507_; lean_object* v_a_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2507_);
v_a_2508_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2476_, 2);
v_a_2442_ = v_a_2507_;
v_a_2443_ = v_a_2508_;
goto v___jp_2441_;
}
v___jp_2429_:
{
lean_object* v_a_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_a_2431_ = lean_ctor_get(v___y_2430_, 0);
v_a_2432_ = lean_ctor_get(v___y_2430_, 1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___y_2430_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___y_2430_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_inc(v_a_2431_);
lean_dec(v___y_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_a_2436_; lean_object* v___x_2438_; 
v_a_2436_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_a_2436_);
lean_dec(v_a_2431_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v_a_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2436_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_a_2432_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
v___jp_2441_:
{
if (lean_obj_tag(v_a_2442_) == 1)
{
uint8_t v___x_2444_; lean_object* v___x_2445_; 
lean_dec_ref_known(v_a_2442_, 1);
v___x_2444_ = 1;
lean_inc(v_stx_2426_);
v___x_2445_ = l_Lean_Fmt_fmtRaw(v___x_2444_, v_stx_2426_, v_a_2427_, v_a_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2474_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_a_2447_ = lean_ctor_get(v___x_2445_, 1);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2449_ = v___x_2445_;
v_isShared_2450_ = v_isSharedCheck_2474_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2474_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = 0;
v___x_2452_ = l_Lean_Syntax_getRange_x3f(v_stx_2426_, v___x_2451_);
if (lean_obj_tag(v___x_2452_) == 1)
{
lean_object* v_val_2453_; lean_object* v_toBacktrackableState_2454_; lean_object* v_shareCommonState_2455_; lean_object* v_freshTagId_2456_; lean_object* v_missingFormatters_2457_; lean_object* v_partialFormatters_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2471_; 
v_val_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v_toBacktrackableState_2454_ = lean_ctor_get(v_a_2447_, 0);
v_shareCommonState_2455_ = lean_ctor_get(v_a_2447_, 1);
v_freshTagId_2456_ = lean_ctor_get(v_a_2447_, 2);
v_missingFormatters_2457_ = lean_ctor_get(v_a_2447_, 3);
v_partialFormatters_2458_ = lean_ctor_get(v_a_2447_, 4);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2447_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2460_ = v_a_2447_;
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_partialFormatters_2458_);
lean_inc(v_missingFormatters_2457_);
lean_inc(v_freshTagId_2456_);
lean_inc(v_shareCommonState_2455_);
lean_inc(v_toBacktrackableState_2454_);
lean_dec(v_a_2447_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_box(0);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_formatterName_2425_);
lean_ctor_set(v___x_2449_, 0, v_stx_2426_);
v___x_2464_ = v___x_2449_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_stx_2426_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_formatterName_2425_);
v___x_2464_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2458_, v_val_2453_, v___x_2464_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 4, v___x_2465_);
v___x_2467_ = v___x_2460_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_toBacktrackableState_2454_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_shareCommonState_2455_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_freshTagId_2456_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_missingFormatters_2457_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2446_, v___x_2462_, v_a_2427_, v___x_2467_);
v___y_2430_ = v___x_2468_;
goto v___jp_2429_;
}
}
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v___x_2452_);
lean_del_object(v___x_2449_);
lean_dec(v_stx_2426_);
lean_dec(v_formatterName_2425_);
v___x_2472_ = lean_box(0);
v___x_2473_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2446_, v___x_2472_, v_a_2427_, v_a_2447_);
v___y_2430_ = v___x_2473_;
goto v___jp_2429_;
}
}
}
else
{
lean_dec(v_stx_2426_);
lean_dec(v_formatterName_2425_);
return v___x_2445_;
}
}
else
{
lean_object* v___x_2475_; 
lean_dec(v_stx_2426_);
lean_dec(v_formatterName_2425_);
v___x_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2442_);
lean_ctor_set(v___x_2475_, 1, v_a_2443_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2509_, lean_object* v_formatterName_2510_, lean_object* v_stx_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Fmt_fmtWith(v_f_2509_, v_formatterName_2510_, v_stx_2511_, v_a_2512_, v_a_2513_);
lean_dec_ref(v_a_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2515_, lean_object* v_m_2516_, lean_object* v_a_2517_, lean_object* v_b_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2516_, v_a_2517_, v_b_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2520_, lean_object* v_a_2521_, lean_object* v_x_2522_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2521_, v_x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2524_, lean_object* v_a_2525_, lean_object* v_x_2526_){
_start:
{
uint8_t v_res_2527_; lean_object* v_r_2528_; 
v_res_2527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2524_, v_a_2525_, v_x_2526_);
lean_dec(v_x_2526_);
lean_dec_ref(v_a_2525_);
v_r_2528_ = lean_box(v_res_2527_);
return v_r_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2529_, lean_object* v_data_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2532_, lean_object* v_a_2533_, lean_object* v_b_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2533_, v_b_2534_, v_x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2537_, lean_object* v_i_2538_, lean_object* v_source_2539_, lean_object* v_target_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2538_, v_source_2539_, v_target_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2543_, v_x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2549_, lean_object* v_kind_2550_, lean_object* v_as_2551_, size_t v_sz_2552_, size_t v_i_2553_, lean_object* v_b_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_lt(v_i_2553_, v_sz_2552_);
if (v___x_2555_ == 0)
{
lean_dec(v_kind_2550_);
lean_inc_ref(v_b_2554_);
return v_b_2554_;
}
else
{
lean_object* v_a_2556_; lean_object* v_provider_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2573_; 
v_a_2556_ = lean_array_uget(v_as_2551_, v_i_2553_);
v_provider_2557_ = lean_ctor_get(v_a_2556_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_a_2556_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v_a_2556_, 0);
lean_dec(v_unused_2574_);
v___x_2559_ = v_a_2556_;
v_isShared_2560_ = v_isSharedCheck_2573_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_provider_2557_);
lean_dec(v_a_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2573_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_env_2561_; lean_object* v_opts_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_env_2561_ = lean_ctor_get(v_a_2549_, 0);
v_opts_2562_ = lean_ctor_get(v_a_2549_, 3);
v___x_2563_ = lean_box(0);
lean_inc(v_kind_2550_);
lean_inc_ref(v_opts_2562_);
lean_inc_ref(v_env_2561_);
v___x_2564_ = lean_apply_3(v_provider_2557_, v_env_2561_, v_opts_2562_, v_kind_2550_);
if (lean_obj_tag(v___x_2564_) == 1)
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
lean_dec(v_kind_2550_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2563_);
lean_ctor_set(v___x_2559_, 0, v___x_2565_);
v___x_2567_ = v___x_2559_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2563_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; 
lean_dec(v___x_2564_);
lean_del_object(v___x_2559_);
v___x_2569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2553_, v___x_2570_);
v_i_2553_ = v___x_2571_;
v_b_2554_ = v___x_2569_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2575_, lean_object* v_kind_2576_, lean_object* v_as_2577_, lean_object* v_sz_2578_, lean_object* v_i_2579_, lean_object* v_b_2580_){
_start:
{
size_t v_sz_boxed_2581_; size_t v_i_boxed_2582_; lean_object* v_res_2583_; 
v_sz_boxed_2581_ = lean_unbox_usize(v_sz_2578_);
lean_dec(v_sz_2578_);
v_i_boxed_2582_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_res_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2575_, v_kind_2576_, v_as_2577_, v_sz_boxed_2581_, v_i_boxed_2582_, v_b_2580_);
lean_dec_ref(v_b_2580_);
lean_dec_ref(v_as_2577_);
lean_dec_ref(v_a_2575_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_env_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; size_t v_sz_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v_fst_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2605_; 
v_env_2587_ = lean_ctor_get(v_a_2585_, 0);
lean_inc_ref(v_env_2587_);
v___x_2588_ = l_Lean_Fmt_getFmtProviders(v_env_2587_);
v___x_2589_ = lean_box(0);
v___x_2590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2591_ = lean_array_size(v___x_2588_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2585_, v_kind_2584_, v___x_2588_, v_sz_2591_, v___x_2592_, v___x_2590_);
lean_dec_ref(v___x_2588_);
v_fst_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2593_, 1);
lean_dec(v_unused_2606_);
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_fst_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
if (lean_obj_tag(v_fst_2594_) == 0)
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v_a_2586_);
lean_ctor_set(v___x_2596_, 0, v___x_2589_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_a_2586_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2603_; 
v_val_2601_ = lean_ctor_get(v_fst_2594_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v_fst_2594_, 1);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v_a_2586_);
lean_ctor_set(v___x_2596_, 0, v_val_2601_);
v___x_2603_ = v___x_2596_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_val_2601_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_a_2586_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2607_, v_a_2608_, v_a_2609_);
lean_dec_ref(v_a_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
switch(lean_obj_tag(v_stx_2611_))
{
case 0:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v_a_2613_);
return v___x_2615_;
}
case 1:
{
lean_object* v_kind_2616_; lean_object* v___x_2617_; lean_object* v_a_2618_; 
lean_inc_ref(v_stx_2611_);
v_kind_2616_ = l_Lean_Syntax_getKind(v_stx_2611_);
lean_inc(v_kind_2616_);
v___x_2617_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2616_, v_a_2612_, v_a_2613_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
if (lean_obj_tag(v_a_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v_a_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___x_2623_; 
lean_dec(v_kind_2616_);
v_val_2619_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_val_2619_);
lean_dec_ref_known(v_a_2618_, 1);
v_a_2620_ = lean_ctor_get(v___x_2617_, 1);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2617_);
v_fst_2621_ = lean_ctor_get(v_val_2619_, 0);
lean_inc(v_fst_2621_);
v_snd_2622_ = lean_ctor_get(v_val_2619_, 1);
lean_inc(v_snd_2622_);
lean_dec(v_val_2619_);
v___x_2623_ = l_Lean_Fmt_fmtWith(v_snd_2622_, v_fst_2621_, v_stx_2611_, v_a_2612_, v_a_2620_);
return v___x_2623_;
}
else
{
lean_object* v_a_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_a_2618_);
v_a_2624_ = lean_ctor_get(v___x_2617_, 1);
lean_inc(v_a_2624_);
lean_dec_ref(v___x_2617_);
v___x_2625_ = 1;
lean_inc_ref(v_stx_2611_);
v___x_2626_ = l_Lean_Fmt_fmtRaw(v___x_2625_, v_stx_2611_, v_a_2612_, v_a_2624_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v_a_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
v_a_2628_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_a_2628_);
v___x_2629_ = 0;
v___x_2630_ = l_Lean_Syntax_getRange_x3f(v_stx_2611_, v___x_2629_);
lean_dec_ref_known(v_stx_2611_, 3);
if (lean_obj_tag(v___x_2630_) == 1)
{
lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; lean_object* v_unused_2653_; 
v_unused_2652_ = lean_ctor_get(v___x_2626_, 1);
lean_dec(v_unused_2652_);
v_unused_2653_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2653_);
v___x_2632_ = v___x_2626_;
v_isShared_2633_ = v_isSharedCheck_2651_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v___x_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2651_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_val_2634_; lean_object* v_toBacktrackableState_2635_; lean_object* v_shareCommonState_2636_; lean_object* v_freshTagId_2637_; lean_object* v_missingFormatters_2638_; lean_object* v_partialFormatters_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2650_; 
v_val_2634_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2630_, 1);
v_toBacktrackableState_2635_ = lean_ctor_get(v_a_2628_, 0);
v_shareCommonState_2636_ = lean_ctor_get(v_a_2628_, 1);
v_freshTagId_2637_ = lean_ctor_get(v_a_2628_, 2);
v_missingFormatters_2638_ = lean_ctor_get(v_a_2628_, 3);
v_partialFormatters_2639_ = lean_ctor_get(v_a_2628_, 4);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_a_2628_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2641_ = v_a_2628_;
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_partialFormatters_2639_);
lean_inc(v_missingFormatters_2638_);
lean_inc(v_freshTagId_2637_);
lean_inc(v_shareCommonState_2636_);
lean_inc(v_toBacktrackableState_2635_);
lean_dec(v_a_2628_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2638_, v_val_2634_, v_kind_2616_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 3, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_toBacktrackableState_2635_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_shareCommonState_2636_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_freshTagId_2637_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_partialFormatters_2639_);
v___x_2645_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2647_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2645_);
v___x_2647_ = v___x_2632_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2627_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
else
{
lean_dec(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec(v_kind_2616_);
return v___x_2626_;
}
}
else
{
lean_dec_ref_known(v_stx_2611_, 3);
lean_dec(v_kind_2616_);
return v___x_2626_;
}
}
}
case 2:
{
lean_object* v_val_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v_valDocs_2660_; lean_object* v___x_2661_; lean_object* v_valDoc_2662_; lean_object* v___x_2663_; 
v_val_2654_ = lean_ctor_get(v_stx_2611_, 1);
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_string_utf8_byte_size(v_val_2654_);
lean_inc_ref_n(v_val_2654_, 2);
v___x_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2657_, 0, v_val_2654_);
lean_ctor_set(v___x_2657_, 1, v___x_2655_);
lean_ctor_set(v___x_2657_, 2, v___x_2656_);
v___x_2658_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v___x_2657_);
v___x_2659_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2660_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_val_2654_, v___x_2657_, v___x_2656_, v___x_2658_, v___x_2659_);
lean_dec_ref_known(v___x_2657_, 3);
v___x_2661_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2662_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2661_, v_valDocs_2660_);
v___x_2663_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2662_, v_stx_2611_, v_a_2613_);
lean_dec_ref_known(v_stx_2611_, 2);
return v___x_2663_;
}
default: 
{
lean_object* v_rawVal_2664_; lean_object* v_str_2665_; lean_object* v_startPos_2666_; lean_object* v_stopPos_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2683_; 
v_rawVal_2664_ = lean_ctor_get(v_stx_2611_, 1);
lean_inc_ref(v_rawVal_2664_);
v_str_2665_ = lean_ctor_get(v_rawVal_2664_, 0);
v_startPos_2666_ = lean_ctor_get(v_rawVal_2664_, 1);
v_stopPos_2667_ = lean_ctor_get(v_rawVal_2664_, 2);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_rawVal_2664_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2669_ = v_rawVal_2664_;
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_stopPos_2667_);
lean_inc(v_startPos_2666_);
lean_inc(v_str_2665_);
lean_dec(v_rawVal_2664_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2671_ = lean_string_utf8_extract(v_str_2665_, v_startPos_2666_, v_stopPos_2667_);
lean_dec(v_stopPos_2667_);
lean_dec(v_startPos_2666_);
lean_dec_ref(v_str_2665_);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_string_utf8_byte_size(v___x_2671_);
lean_inc_ref(v___x_2671_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 2, v___x_2673_);
lean_ctor_set(v___x_2669_, 1, v___x_2672_);
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2675_ = v___x_2669_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v_valDocs_2678_; lean_object* v___x_2679_; lean_object* v_valDoc_2680_; lean_object* v___x_2681_; 
v___x_2676_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v___x_2675_);
v___x_2677_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2678_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_2671_, v___x_2675_, v___x_2673_, v___x_2676_, v___x_2677_);
lean_dec_ref(v___x_2675_);
v___x_2679_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2680_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2679_, v_valDocs_2678_);
v___x_2681_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2680_, v_stx_2611_, v_a_2613_);
lean_dec_ref_known(v_stx_2611_, 4);
return v___x_2681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Fmt_fmt(v_stx_2684_, v_a_2685_, v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0(lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
if (lean_obj_tag(v_x_2689_) == 0)
{
uint8_t v___x_2690_; 
v___x_2690_ = 1;
return v___x_2690_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
return v___x_2691_;
}
}
else
{
if (lean_obj_tag(v_x_2689_) == 0)
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
else
{
lean_object* v_val_2693_; lean_object* v_val_2694_; uint8_t v___x_2695_; 
v_val_2693_ = lean_ctor_get(v_x_2688_, 0);
v_val_2694_ = lean_ctor_get(v_x_2689_, 0);
v___x_2695_ = l_Lean_Syntax_instBEqRange_beq(v_val_2693_, v_val_2694_);
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0___boxed(lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0(v_x_2696_, v_x_2697_);
lean_dec(v_x_2697_);
lean_dec(v_x_2696_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0(uint8_t v___x_2700_, lean_object* v___x_2701_, lean_object* v_x_2702_){
_start:
{
if (lean_obj_tag(v_x_2702_) == 15)
{
lean_object* v_i_2703_; lean_object* v_stx_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_i_2703_ = lean_ctor_get(v_x_2702_, 0);
v_stx_2704_ = lean_ctor_get(v_i_2703_, 0);
v___x_2705_ = l_Lean_Syntax_getRange_x3f(v_stx_2704_, v___x_2700_);
v___x_2706_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode_spec__0(v___x_2705_, v___x_2701_);
lean_dec(v___x_2705_);
return v___x_2706_;
}
else
{
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0___boxed(lean_object* v___x_2707_, lean_object* v___x_2708_, lean_object* v_x_2709_){
_start:
{
uint8_t v___x_2372__boxed_2710_; uint8_t v_res_2711_; lean_object* v_r_2712_; 
v___x_2372__boxed_2710_ = lean_unbox(v___x_2707_);
v_res_2711_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0(v___x_2372__boxed_2710_, v___x_2708_, v_x_2709_);
lean_dec_ref(v_x_2709_);
lean_dec(v___x_2708_);
v_r_2712_ = lean_box(v_res_2711_);
return v_r_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___y_2718_; lean_object* v_initialSnap_x3f_2729_; 
v_initialSnap_x3f_2729_ = lean_ctor_get(v_a_2715_, 2);
if (lean_obj_tag(v_initialSnap_x3f_2729_) == 1)
{
lean_object* v_text_2730_; lean_object* v_val_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; 
v_text_2730_ = lean_ctor_get(v_a_2715_, 1);
v_val_2731_ = lean_ctor_get(v_initialSnap_x3f_2729_, 0);
v___x_2732_ = 0;
v___x_2733_ = l_Lean_Syntax_getRange_x3f(v_a_2714_, v___x_2732_);
if (lean_obj_tag(v___x_2733_) == 1)
{
lean_object* v_val_2734_; lean_object* v_start_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2798_; 
v_val_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_val_2734_);
v_start_2735_ = lean_ctor_get(v_val_2734_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_val_2734_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v_val_2734_, 1);
lean_dec(v_unused_2799_);
v___x_2737_ = v_val_2734_;
v_isShared_2738_ = v_isSharedCheck_2798_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_start_2735_);
lean_dec(v_val_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2798_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_inc_ref(v_text_2730_);
lean_inc(v_val_2731_);
v___x_2739_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_val_2731_, v_text_2730_, v_start_2735_, v___x_2732_);
v___x_2740_ = lean_task_get_own(v___x_2739_);
if (lean_obj_tag(v___x_2740_) == 1)
{
lean_object* v_val_2741_; lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
v_val_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_val_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = lean_box(v___x_2732_);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2743_, 0, v___x_2742_);
lean_closure_set(v___f_2743_, 1, v___x_2733_);
v___x_2744_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_2743_, v_val_2741_);
if (lean_obj_tag(v___x_2744_) == 1)
{
lean_object* v_val_2745_; 
v_val_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_val_2745_);
lean_dec_ref_known(v___x_2744_, 1);
if (lean_obj_tag(v_val_2745_) == 15)
{
lean_object* v_i_2746_; lean_object* v_stx_2747_; lean_object* v_chosenAltIdx_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2786_; 
v_i_2746_ = lean_ctor_get(v_val_2745_, 0);
lean_inc_ref(v_i_2746_);
lean_dec_ref_known(v_val_2745_, 1);
v_stx_2747_ = lean_ctor_get(v_i_2746_, 0);
v_chosenAltIdx_2748_ = lean_ctor_get(v_i_2746_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_i_2746_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2750_ = v_i_2746_;
v_isShared_2751_ = v_isSharedCheck_2786_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_chosenAltIdx_2748_);
lean_inc(v_stx_2747_);
lean_dec(v_i_2746_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2786_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2752_ = l_Lean_Syntax_getNumArgs(v_stx_2747_);
lean_dec(v_stx_2747_);
v___x_2753_ = l_Lean_Syntax_getNumArgs(v_a_2714_);
v___x_2754_ = lean_nat_dec_eq(v___x_2752_, v___x_2753_);
lean_dec(v___x_2753_);
lean_dec(v___x_2752_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
lean_dec(v_chosenAltIdx_2748_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2756_ = lean_box(0);
lean_inc(v_a_2714_);
v___x_2757_ = l_Lean_Syntax_formatStx(v_a_2714_, v___x_2756_, v___x_2754_);
v___x_2758_ = l_Std_Format_defWidth;
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = l_Std_Format_pretty(v___x_2757_, v___x_2758_, v___x_2759_, v___x_2759_);
v___x_2761_ = lean_string_append(v___x_2755_, v___x_2760_);
lean_dec_ref(v___x_2760_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 5);
lean_ctor_set(v___x_2750_, 1, v___x_2761_);
lean_ctor_set(v___x_2750_, 0, v_a_2714_);
v___x_2763_ = v___x_2750_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2714_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2765_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 1);
lean_ctor_set(v___x_2737_, 1, v_a_2716_);
lean_ctor_set(v___x_2737_, 0, v___x_2763_);
v___x_2765_ = v___x_2737_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_a_2716_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2768_ = l_Lean_Syntax_getArgs(v_a_2714_);
v___x_2769_ = lean_array_get_size(v___x_2768_);
v___x_2770_ = lean_nat_dec_lt(v_chosenAltIdx_2748_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec_ref(v___x_2768_);
lean_dec(v_chosenAltIdx_2748_);
v___x_2771_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2772_ = lean_box(0);
lean_inc(v_a_2714_);
v___x_2773_ = l_Lean_Syntax_formatStx(v_a_2714_, v___x_2772_, v___x_2732_);
v___x_2774_ = l_Std_Format_defWidth;
v___x_2775_ = lean_unsigned_to_nat(0u);
v___x_2776_ = l_Std_Format_pretty(v___x_2773_, v___x_2774_, v___x_2775_, v___x_2775_);
v___x_2777_ = lean_string_append(v___x_2771_, v___x_2776_);
lean_dec_ref(v___x_2776_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 5);
lean_ctor_set(v___x_2750_, 1, v___x_2777_);
lean_ctor_set(v___x_2750_, 0, v_a_2714_);
v___x_2779_ = v___x_2750_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2714_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 1);
lean_ctor_set(v___x_2737_, 1, v_a_2716_);
lean_ctor_set(v___x_2737_, 0, v___x_2779_);
v___x_2781_ = v___x_2737_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_a_2716_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2750_);
lean_del_object(v___x_2737_);
lean_dec(v_a_2714_);
v___x_2784_ = lean_array_fget(v___x_2768_, v_chosenAltIdx_2748_);
lean_dec(v_chosenAltIdx_2748_);
lean_dec_ref(v___x_2768_);
v___x_2785_ = l_Lean_Fmt_fmt(v___x_2784_, v_a_2715_, v_a_2716_);
return v___x_2785_;
}
}
}
}
else
{
lean_dec(v_val_2745_);
lean_del_object(v___x_2737_);
v___y_2718_ = v_a_2716_;
goto v___jp_2717_;
}
}
else
{
lean_dec(v___x_2744_);
lean_del_object(v___x_2737_);
v___y_2718_ = v_a_2716_;
goto v___jp_2717_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_dec(v___x_2740_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2787_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2788_ = lean_box(0);
lean_inc(v_a_2714_);
v___x_2789_ = l_Lean_Syntax_formatStx(v_a_2714_, v___x_2788_, v___x_2732_);
v___x_2790_ = l_Std_Format_defWidth;
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = l_Std_Format_pretty(v___x_2789_, v___x_2790_, v___x_2791_, v___x_2791_);
v___x_2793_ = lean_string_append(v___x_2787_, v___x_2792_);
lean_dec_ref(v___x_2792_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 5);
lean_ctor_set(v___x_2737_, 1, v___x_2793_);
lean_ctor_set(v___x_2737_, 0, v_a_2714_);
v___x_2795_ = v___x_2737_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2714_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_a_2716_);
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec(v___x_2733_);
v___x_2800_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2801_ = lean_box(0);
lean_inc(v_a_2714_);
v___x_2802_ = l_Lean_Syntax_formatStx(v_a_2714_, v___x_2801_, v___x_2732_);
v___x_2803_ = l_Std_Format_defWidth;
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = l_Std_Format_pretty(v___x_2802_, v___x_2803_, v___x_2804_, v___x_2804_);
v___x_2806_ = lean_string_append(v___x_2800_, v___x_2805_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2714_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v_a_2716_);
return v___x_2808_;
}
}
else
{
uint8_t v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = 1;
v___x_2810_ = l_Lean_Fmt_fmtRaw(v___x_2809_, v_a_2714_, v_a_2715_, v_a_2716_);
return v___x_2810_;
}
v___jp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2720_ = lean_box(0);
v___x_2721_ = 0;
lean_inc(v_a_2714_);
v___x_2722_ = l_Lean_Syntax_formatStx(v_a_2714_, v___x_2720_, v___x_2721_);
v___x_2723_ = l_Std_Format_defWidth;
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = l_Std_Format_pretty(v___x_2722_, v___x_2723_, v___x_2724_, v___x_2724_);
v___x_2726_ = lean_string_append(v___x_2719_, v___x_2725_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_a_2714_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___y_2718_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_a_2811_, v_a_2812_, v_a_2813_);
lean_dec_ref(v_a_2812_);
return v_res_2814_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = l_Lean_Fmt_instInhabitedState_default;
v___x_2816_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v___x_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_msg_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0, &l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0);
v___x_2820_ = lean_panic_fn_borrowed(v___x_2819_, v_msg_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2821_){
_start:
{
lean_object* v_aPtr_2822_; lean_object* v_bPtr_2823_; size_t v_ptr_2824_; size_t v_ptr_2825_; uint64_t v___x_2826_; uint64_t v___x_2827_; uint64_t v___x_2828_; uint64_t v___x_2829_; uint64_t v___x_2830_; 
v_aPtr_2822_ = lean_ctor_get(v_x_2821_, 0);
v_bPtr_2823_ = lean_ctor_get(v_x_2821_, 1);
v_ptr_2824_ = lean_ctor_get_usize(v_aPtr_2822_, 1);
v_ptr_2825_ = lean_ctor_get_usize(v_bPtr_2823_, 1);
v___x_2826_ = 0ULL;
v___x_2827_ = lean_usize_to_uint64(v_ptr_2824_);
v___x_2828_ = lean_uint64_mix_hash(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_usize_to_uint64(v_ptr_2825_);
v___x_2830_ = lean_uint64_mix_hash(v___x_2828_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2831_){
_start:
{
uint64_t v_res_2832_; lean_object* v_r_2833_; 
v_res_2832_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_x_2831_);
lean_dec_ref(v_x_2831_);
v_r_2833_ = lean_box_uint64(v_res_2832_);
return v_r_2833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
lean_object* v_aPtr_2836_; lean_object* v_aPtr_2837_; lean_object* v_bPtr_2838_; lean_object* v_bPtr_2839_; size_t v_ptr_2840_; size_t v_ptr_2841_; uint8_t v___x_2842_; 
v_aPtr_2836_ = lean_ctor_get(v_x_2834_, 0);
v_aPtr_2837_ = lean_ctor_get(v_x_2835_, 0);
v_bPtr_2838_ = lean_ctor_get(v_x_2834_, 1);
v_bPtr_2839_ = lean_ctor_get(v_x_2835_, 1);
v_ptr_2840_ = lean_ctor_get_usize(v_aPtr_2836_, 1);
v_ptr_2841_ = lean_ctor_get_usize(v_aPtr_2837_, 1);
v___x_2842_ = lean_usize_dec_eq(v_ptr_2840_, v_ptr_2841_);
if (v___x_2842_ == 0)
{
return v___x_2842_;
}
else
{
size_t v_ptr_2843_; size_t v_ptr_2844_; uint8_t v___x_2845_; 
v_ptr_2843_ = lean_ctor_get_usize(v_bPtr_2838_, 1);
v_ptr_2844_ = lean_ctor_get_usize(v_bPtr_2839_, 1);
v___x_2845_ = lean_usize_dec_eq(v_ptr_2843_, v_ptr_2844_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
uint8_t v_res_2848_; lean_object* v_r_2849_; 
v_res_2848_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_x_2846_, v_x_2847_);
lean_dec_ref(v_x_2847_);
lean_dec_ref(v_x_2846_);
v_r_2849_ = lean_box(v_res_2848_);
return v_r_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_box(0);
return v___x_2852_;
}
else
{
lean_object* v_key_2853_; lean_object* v_value_2854_; lean_object* v_tail_2855_; uint8_t v___x_2856_; 
v_key_2853_ = lean_ctor_get(v_x_2851_, 0);
v_value_2854_ = lean_ctor_get(v_x_2851_, 1);
v_tail_2855_ = lean_ctor_get(v_x_2851_, 2);
v___x_2856_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2853_, v_a_2850_);
if (v___x_2856_ == 0)
{
v_x_2851_ = v_tail_2855_;
goto _start;
}
else
{
lean_object* v___x_2858_; 
lean_inc(v_value_2854_);
v___x_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2858_, 0, v_value_2854_);
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2859_, v_x_2860_);
lean_dec(v_x_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object* v_m_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_buckets_2864_; lean_object* v___x_2865_; uint64_t v___x_2866_; uint64_t v___x_2867_; uint64_t v___x_2868_; uint64_t v_fold_2869_; uint64_t v___x_2870_; uint64_t v___x_2871_; uint64_t v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; size_t v___x_2876_; size_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_buckets_2864_ = lean_ctor_get(v_m_2862_, 1);
v___x_2865_ = lean_array_get_size(v_buckets_2864_);
v___x_2866_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2863_);
v___x_2867_ = 32ULL;
v___x_2868_ = lean_uint64_shift_right(v___x_2866_, v___x_2867_);
v_fold_2869_ = lean_uint64_xor(v___x_2866_, v___x_2868_);
v___x_2870_ = 16ULL;
v___x_2871_ = lean_uint64_shift_right(v_fold_2869_, v___x_2870_);
v___x_2872_ = lean_uint64_xor(v_fold_2869_, v___x_2871_);
v___x_2873_ = lean_uint64_to_usize(v___x_2872_);
v___x_2874_ = lean_usize_of_nat(v___x_2865_);
v___x_2875_ = ((size_t)1ULL);
v___x_2876_ = lean_usize_sub(v___x_2874_, v___x_2875_);
v___x_2877_ = lean_usize_land(v___x_2873_, v___x_2876_);
v___x_2878_ = lean_array_uget_borrowed(v_buckets_2864_, v___x_2877_);
v___x_2879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2863_, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_2880_, v_a_2881_);
lean_dec_ref(v_a_2881_);
lean_dec_ref(v_m_2880_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 0)
{
return v_x_2883_;
}
else
{
lean_object* v_key_2885_; lean_object* v_value_2886_; lean_object* v_tail_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2910_; 
v_key_2885_ = lean_ctor_get(v_x_2884_, 0);
v_value_2886_ = lean_ctor_get(v_x_2884_, 1);
v_tail_2887_ = lean_ctor_get(v_x_2884_, 2);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_x_2884_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2889_ = v_x_2884_;
v_isShared_2890_ = v_isSharedCheck_2910_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_tail_2887_);
lean_inc(v_value_2886_);
lean_inc(v_key_2885_);
lean_dec(v_x_2884_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2910_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; uint64_t v___x_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; uint64_t v_fold_2895_; uint64_t v___x_2896_; uint64_t v___x_2897_; uint64_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2891_ = lean_array_get_size(v_x_2883_);
v___x_2892_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_key_2885_);
v___x_2893_ = 32ULL;
v___x_2894_ = lean_uint64_shift_right(v___x_2892_, v___x_2893_);
v_fold_2895_ = lean_uint64_xor(v___x_2892_, v___x_2894_);
v___x_2896_ = 16ULL;
v___x_2897_ = lean_uint64_shift_right(v_fold_2895_, v___x_2896_);
v___x_2898_ = lean_uint64_xor(v_fold_2895_, v___x_2897_);
v___x_2899_ = lean_uint64_to_usize(v___x_2898_);
v___x_2900_ = lean_usize_of_nat(v___x_2891_);
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_sub(v___x_2900_, v___x_2901_);
v___x_2903_ = lean_usize_land(v___x_2899_, v___x_2902_);
v___x_2904_ = lean_array_uget_borrowed(v_x_2883_, v___x_2903_);
lean_inc(v___x_2904_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 2, v___x_2904_);
v___x_2906_ = v___x_2889_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_key_2885_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_value_2886_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_array_uset(v_x_2883_, v___x_2903_, v___x_2906_);
v_x_2883_ = v___x_2907_;
v_x_2884_ = v_tail_2887_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object* v_i_2911_, lean_object* v_source_2912_, lean_object* v_target_2913_){
_start:
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = lean_array_get_size(v_source_2912_);
v___x_2915_ = lean_nat_dec_lt(v_i_2911_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec_ref(v_source_2912_);
lean_dec(v_i_2911_);
return v_target_2913_;
}
else
{
lean_object* v_es_2916_; lean_object* v___x_2917_; lean_object* v_source_2918_; lean_object* v_target_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_es_2916_ = lean_array_fget(v_source_2912_, v_i_2911_);
v___x_2917_ = lean_box(0);
v_source_2918_ = lean_array_fset(v_source_2912_, v_i_2911_, v___x_2917_);
v_target_2919_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_target_2913_, v_es_2916_);
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = lean_nat_add(v_i_2911_, v___x_2920_);
lean_dec(v_i_2911_);
v_i_2911_ = v___x_2921_;
v_source_2912_ = v_source_2918_;
v_target_2913_ = v_target_2919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object* v_data_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v_nbuckets_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2924_ = lean_array_get_size(v_data_2923_);
v___x_2925_ = lean_unsigned_to_nat(2u);
v_nbuckets_2926_ = lean_nat_mul(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_mk_array(v_nbuckets_2926_, v___x_2928_);
v___x_2930_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v___x_2927_, v_data_2923_, v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_a_2931_, lean_object* v_x_2932_){
_start:
{
if (lean_obj_tag(v_x_2932_) == 0)
{
uint8_t v___x_2933_; 
v___x_2933_ = 0;
return v___x_2933_;
}
else
{
lean_object* v_key_2934_; lean_object* v_tail_2935_; uint8_t v___x_2936_; 
v_key_2934_ = lean_ctor_get(v_x_2932_, 0);
v_tail_2935_ = lean_ctor_get(v_x_2932_, 2);
v___x_2936_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2934_, v_a_2931_);
if (v___x_2936_ == 0)
{
v_x_2932_ = v_tail_2935_;
goto _start;
}
else
{
return v___x_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_a_2938_, lean_object* v_x_2939_){
_start:
{
uint8_t v_res_2940_; lean_object* v_r_2941_; 
v_res_2940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2938_, v_x_2939_);
lean_dec(v_x_2939_);
lean_dec_ref(v_a_2938_);
v_r_2941_ = lean_box(v_res_2940_);
return v_r_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_a_2942_, lean_object* v_b_2943_, lean_object* v_x_2944_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
lean_dec(v_b_2943_);
lean_dec_ref(v_a_2942_);
return v_x_2944_;
}
else
{
lean_object* v_key_2945_; lean_object* v_value_2946_; lean_object* v_tail_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2959_; 
v_key_2945_ = lean_ctor_get(v_x_2944_, 0);
v_value_2946_ = lean_ctor_get(v_x_2944_, 1);
v_tail_2947_ = lean_ctor_get(v_x_2944_, 2);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_x_2944_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2949_ = v_x_2944_;
v_isShared_2950_ = v_isSharedCheck_2959_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_tail_2947_);
lean_inc(v_value_2946_);
lean_inc(v_key_2945_);
lean_dec(v_x_2944_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2959_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
uint8_t v___x_2951_; 
v___x_2951_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2945_, v_a_2942_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2942_, v_b_2943_, v_tail_2947_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 2, v___x_2952_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_key_2945_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_value_2946_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
else
{
lean_object* v___x_2957_; 
lean_dec(v_value_2946_);
lean_dec(v_key_2945_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v_b_2943_);
lean_ctor_set(v___x_2949_, 0, v_a_2942_);
v___x_2957_ = v___x_2949_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2942_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_b_2943_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_tail_2947_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object* v_m_2960_, lean_object* v_a_2961_, lean_object* v_b_2962_){
_start:
{
lean_object* v_size_2963_; lean_object* v_buckets_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3007_; 
v_size_2963_ = lean_ctor_get(v_m_2960_, 0);
v_buckets_2964_ = lean_ctor_get(v_m_2960_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_m_2960_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2966_ = v_m_2960_;
v_isShared_2967_ = v_isSharedCheck_3007_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_buckets_2964_);
lean_inc(v_size_2963_);
lean_dec(v_m_2960_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3007_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; uint64_t v___x_2969_; uint64_t v___x_2970_; uint64_t v___x_2971_; uint64_t v_fold_2972_; uint64_t v___x_2973_; uint64_t v___x_2974_; uint64_t v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; lean_object* v_bkt_2981_; uint8_t v___x_2982_; 
v___x_2968_ = lean_array_get_size(v_buckets_2964_);
v___x_2969_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2961_);
v___x_2970_ = 32ULL;
v___x_2971_ = lean_uint64_shift_right(v___x_2969_, v___x_2970_);
v_fold_2972_ = lean_uint64_xor(v___x_2969_, v___x_2971_);
v___x_2973_ = 16ULL;
v___x_2974_ = lean_uint64_shift_right(v_fold_2972_, v___x_2973_);
v___x_2975_ = lean_uint64_xor(v_fold_2972_, v___x_2974_);
v___x_2976_ = lean_uint64_to_usize(v___x_2975_);
v___x_2977_ = lean_usize_of_nat(v___x_2968_);
v___x_2978_ = ((size_t)1ULL);
v___x_2979_ = lean_usize_sub(v___x_2977_, v___x_2978_);
v___x_2980_ = lean_usize_land(v___x_2976_, v___x_2979_);
v_bkt_2981_ = lean_array_uget_borrowed(v_buckets_2964_, v___x_2980_);
v___x_2982_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2961_, v_bkt_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v_size_x27_2984_; lean_object* v___x_2985_; lean_object* v_buckets_x27_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2983_ = lean_unsigned_to_nat(1u);
v_size_x27_2984_ = lean_nat_add(v_size_2963_, v___x_2983_);
lean_dec(v_size_2963_);
lean_inc(v_bkt_2981_);
v___x_2985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2961_);
lean_ctor_set(v___x_2985_, 1, v_b_2962_);
lean_ctor_set(v___x_2985_, 2, v_bkt_2981_);
v_buckets_x27_2986_ = lean_array_uset(v_buckets_2964_, v___x_2980_, v___x_2985_);
v___x_2987_ = lean_unsigned_to_nat(4u);
v___x_2988_ = lean_nat_mul(v_size_x27_2984_, v___x_2987_);
v___x_2989_ = lean_unsigned_to_nat(3u);
v___x_2990_ = lean_nat_div(v___x_2988_, v___x_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_array_get_size(v_buckets_x27_2986_);
v___x_2992_ = lean_nat_dec_le(v___x_2990_, v___x_2991_);
lean_dec(v___x_2990_);
if (v___x_2992_ == 0)
{
lean_object* v_val_2993_; lean_object* v___x_2995_; 
v_val_2993_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_buckets_x27_2986_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v_val_2993_);
lean_ctor_set(v___x_2966_, 0, v_size_x27_2984_);
v___x_2995_ = v___x_2966_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_size_x27_2984_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_val_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
else
{
lean_object* v___x_2998_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v_buckets_x27_2986_);
lean_ctor_set(v___x_2966_, 0, v_size_x27_2984_);
v___x_2998_ = v___x_2966_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_size_x27_2984_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_buckets_x27_2986_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v___x_3000_; lean_object* v_buckets_x27_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
lean_inc(v_bkt_2981_);
v___x_3000_ = lean_box(0);
v_buckets_x27_3001_ = lean_array_uset(v_buckets_2964_, v___x_2980_, v___x_3000_);
v___x_3002_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2961_, v_b_2962_, v_bkt_2981_);
v___x_3003_ = lean_array_uset(v_buckets_x27_3001_, v___x_2980_, v___x_3002_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_3003_);
v___x_3005_ = v___x_2966_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_size_2963_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_a_3008_, lean_object* v_b_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___y_3016_; lean_object* v_da1_3021_; lean_object* v_da2_3022_; lean_object* v_db1_3023_; lean_object* v_db2_3024_; lean_object* v___y_3025_; lean_object* v_sa_3032_; lean_object* v_sb_3033_; lean_object* v___y_3034_; 
switch(lean_obj_tag(v_a_3008_))
{
case 0:
{
if (lean_obj_tag(v_b_3009_) == 0)
{
uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = 1;
v___x_3039_ = lean_box(v___x_3038_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_3010_);
return v___x_3040_;
}
else
{
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 1:
{
if (lean_obj_tag(v_b_3009_) == 1)
{
lean_object* v_f_3041_; lean_object* v_f_3042_; 
v_f_3041_ = lean_ctor_get(v_a_3008_, 2);
lean_inc_ref(v_f_3041_);
lean_dec_ref_known(v_a_3008_, 3);
v_f_3042_ = lean_ctor_get(v_b_3009_, 2);
lean_inc_ref(v_f_3042_);
lean_dec_ref_known(v_b_3009_, 3);
v_sa_3032_ = v_f_3041_;
v_sb_3033_ = v_f_3042_;
v___y_3034_ = v_a_3010_;
goto v___jp_3031_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 2:
{
if (lean_obj_tag(v_b_3009_) == 2)
{
lean_object* v_s_3043_; lean_object* v_s_3044_; 
v_s_3043_ = lean_ctor_get(v_a_3008_, 2);
lean_inc_ref(v_s_3043_);
lean_dec_ref_known(v_a_3008_, 3);
v_s_3044_ = lean_ctor_get(v_b_3009_, 2);
lean_inc_ref(v_s_3044_);
lean_dec_ref_known(v_b_3009_, 3);
v_sa_3032_ = v_s_3043_;
v_sb_3033_ = v_s_3044_;
v___y_3034_ = v_a_3010_;
goto v___jp_3031_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 3:
{
if (lean_obj_tag(v_b_3009_) == 3)
{
lean_object* v_id_3045_; lean_object* v_d_3046_; lean_object* v_id_3047_; lean_object* v_d_3048_; uint8_t v___x_3049_; 
v_id_3045_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_id_3045_);
v_d_3046_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_d_3046_);
lean_dec_ref_known(v_a_3008_, 4);
v_id_3047_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_id_3047_);
v_d_3048_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_d_3048_);
lean_dec_ref_known(v_b_3009_, 4);
v___x_3049_ = lean_nat_dec_eq(v_id_3045_, v_id_3047_);
lean_dec(v_id_3047_);
lean_dec(v_id_3045_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec(v_d_3048_);
lean_dec(v_d_3046_);
v___x_3050_ = lean_box(v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_a_3010_);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3046_, v_d_3048_, v_a_3010_);
return v___x_3052_;
}
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 4:
{
if (lean_obj_tag(v_b_3009_) == 4)
{
lean_object* v_d_3053_; lean_object* v_d_3054_; lean_object* v___x_3055_; 
v_d_3053_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3053_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3054_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3054_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3055_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3053_, v_d_3054_, v_a_3010_);
return v___x_3055_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 5:
{
if (lean_obj_tag(v_b_3009_) == 5)
{
lean_object* v_d_3056_; lean_object* v_d_3057_; lean_object* v___x_3058_; 
v_d_3056_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3056_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3057_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3057_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3058_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3056_, v_d_3057_, v_a_3010_);
return v___x_3058_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 6:
{
if (lean_obj_tag(v_b_3009_) == 6)
{
lean_object* v_n_3059_; uint8_t v_isCumulative_3060_; lean_object* v_d_3061_; lean_object* v_n_3062_; uint8_t v_isCumulative_3063_; lean_object* v_d_3064_; uint8_t v___y_3066_; uint8_t v___x_3068_; 
v_n_3059_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_n_3059_);
v_isCumulative_3060_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*4 + 3);
v_d_3061_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_d_3061_);
lean_dec_ref_known(v_a_3008_, 4);
v_n_3062_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_n_3062_);
v_isCumulative_3063_ = lean_ctor_get_uint8(v_b_3009_, sizeof(void*)*4 + 3);
v_d_3064_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_d_3064_);
lean_dec_ref_known(v_b_3009_, 4);
v___x_3068_ = lean_nat_dec_eq(v_n_3059_, v_n_3062_);
lean_dec(v_n_3062_);
lean_dec(v_n_3059_);
if (v___x_3068_ == 0)
{
lean_dec(v_d_3064_);
lean_dec(v_d_3061_);
goto v___jp_3011_;
}
else
{
if (v_isCumulative_3060_ == 0)
{
if (v_isCumulative_3063_ == 0)
{
v___y_3066_ = v___x_3068_;
goto v___jp_3065_;
}
else
{
lean_dec(v_d_3064_);
lean_dec(v_d_3061_);
goto v___jp_3011_;
}
}
else
{
v___y_3066_ = v_isCumulative_3063_;
goto v___jp_3065_;
}
}
v___jp_3065_:
{
if (v___y_3066_ == 0)
{
lean_dec(v_d_3064_);
lean_dec(v_d_3061_);
goto v___jp_3011_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3061_, v_d_3064_, v_a_3010_);
return v___x_3067_;
}
}
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 7:
{
if (lean_obj_tag(v_b_3009_) == 7)
{
lean_object* v_d_3069_; lean_object* v_d_3070_; lean_object* v___x_3071_; 
v_d_3069_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3069_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3070_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3070_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3071_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3069_, v_d_3070_, v_a_3010_);
return v___x_3071_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 8:
{
if (lean_obj_tag(v_b_3009_) == 8)
{
uint8_t v_onlyNonCumulative_3072_; 
v_onlyNonCumulative_3072_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3072_ == 0)
{
uint8_t v_onlyNonCumulative_3073_; 
v_onlyNonCumulative_3073_ = lean_ctor_get_uint8(v_b_3009_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3073_ == 0)
{
lean_object* v_d_3074_; lean_object* v_d_3075_; lean_object* v___x_3076_; 
v_d_3074_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3074_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3075_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3075_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3076_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3074_, v_d_3075_, v_a_3010_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec_ref_known(v_b_3009_, 3);
lean_dec_ref_known(v_a_3008_, 3);
v___x_3077_ = lean_box(v_onlyNonCumulative_3072_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v_a_3010_);
return v___x_3078_;
}
}
else
{
uint8_t v_onlyNonCumulative_3079_; 
v_onlyNonCumulative_3079_ = lean_ctor_get_uint8(v_b_3009_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref_known(v_b_3009_, 3);
lean_dec_ref_known(v_a_3008_, 3);
v___x_3080_ = lean_box(v_onlyNonCumulative_3079_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v_a_3010_);
return v___x_3081_;
}
else
{
lean_object* v_d_3082_; lean_object* v_d_3083_; lean_object* v___x_3084_; 
v_d_3082_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3082_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3083_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3083_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3084_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3082_, v_d_3083_, v_a_3010_);
return v___x_3084_;
}
}
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 9:
{
if (lean_obj_tag(v_b_3009_) == 9)
{
lean_object* v_d_3085_; lean_object* v_d_3086_; lean_object* v___x_3087_; 
v_d_3085_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3085_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3086_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3086_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3087_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3085_, v_d_3086_, v_a_3010_);
return v___x_3087_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 10:
{
if (lean_obj_tag(v_b_3009_) == 10)
{
lean_object* v_d_3088_; lean_object* v_d_3089_; lean_object* v___x_3090_; 
v_d_3088_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_d_3088_);
lean_dec_ref_known(v_a_3008_, 3);
v_d_3089_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_d_3089_);
lean_dec_ref_known(v_b_3009_, 3);
v___x_3090_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3088_, v_d_3089_, v_a_3010_);
return v___x_3090_;
}
else
{
lean_dec_ref_known(v_a_3008_, 3);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 11:
{
if (lean_obj_tag(v_b_3009_) == 11)
{
lean_object* v_p_3091_; lean_object* v_p_3092_; lean_object* v_d_3093_; lean_object* v_d_3094_; lean_object* v_id_3095_; lean_object* v_id_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3106_; 
v_p_3091_ = lean_ctor_get(v_a_3008_, 2);
lean_inc_ref(v_p_3091_);
v_p_3092_ = lean_ctor_get(v_b_3009_, 2);
lean_inc_ref(v_p_3092_);
v_d_3093_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_d_3093_);
lean_dec_ref_known(v_a_3008_, 4);
v_d_3094_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_d_3094_);
lean_dec_ref_known(v_b_3009_, 4);
v_id_3095_ = lean_ctor_get(v_p_3091_, 1);
lean_inc(v_id_3095_);
lean_dec_ref(v_p_3091_);
v_id_3096_ = lean_ctor_get(v_p_3092_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_p_3092_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_p_3092_, 0);
lean_dec(v_unused_3107_);
v___x_3098_ = v_p_3092_;
v_isShared_3099_ = v_isSharedCheck_3106_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_id_3096_);
lean_dec(v_p_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3106_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_name_eq(v_id_3095_, v_id_3096_);
lean_dec(v_id_3096_);
lean_dec(v_id_3095_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec(v_d_3094_);
lean_dec(v_d_3093_);
v___x_3101_ = lean_box(v___x_3100_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 1, v_a_3010_);
lean_ctor_set(v___x_3098_, 0, v___x_3101_);
v___x_3103_ = v___x_3098_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_a_3010_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3105_; 
lean_del_object(v___x_3098_);
v___x_3105_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3093_, v_d_3094_, v_a_3010_);
return v___x_3105_;
}
}
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 12:
{
if (lean_obj_tag(v_b_3009_) == 12)
{
lean_object* v_cost_3108_; lean_object* v_d_3109_; lean_object* v_cost_3110_; lean_object* v_d_3111_; uint8_t v___x_3112_; 
v_cost_3108_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_cost_3108_);
v_d_3109_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_d_3109_);
lean_dec_ref_known(v_a_3008_, 4);
v_cost_3110_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_cost_3110_);
v_d_3111_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_d_3111_);
lean_dec_ref_known(v_b_3009_, 4);
v___x_3112_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3108_, v_cost_3110_);
lean_dec(v_cost_3110_);
lean_dec(v_cost_3108_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_d_3111_);
lean_dec(v_d_3109_);
v___x_3113_ = lean_box(v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v_a_3010_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3109_, v_d_3111_, v_a_3010_);
return v___x_3115_;
}
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
case 13:
{
if (lean_obj_tag(v_b_3009_) == 13)
{
lean_object* v_a_3116_; lean_object* v_b_3117_; lean_object* v_a_3118_; lean_object* v_b_3119_; 
v_a_3116_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_a_3116_);
v_b_3117_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_b_3117_);
lean_dec_ref_known(v_a_3008_, 4);
v_a_3118_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_a_3118_);
v_b_3119_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_b_3119_);
lean_dec_ref_known(v_b_3009_, 4);
v_da1_3021_ = v_a_3116_;
v_da2_3022_ = v_b_3117_;
v_db1_3023_ = v_a_3118_;
v_db2_3024_ = v_b_3119_;
v___y_3025_ = v_a_3010_;
goto v___jp_3020_;
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
default: 
{
if (lean_obj_tag(v_b_3009_) == 14)
{
lean_object* v_a_3120_; lean_object* v_b_3121_; lean_object* v_a_3122_; lean_object* v_b_3123_; 
v_a_3120_ = lean_ctor_get(v_a_3008_, 2);
lean_inc(v_a_3120_);
v_b_3121_ = lean_ctor_get(v_a_3008_, 3);
lean_inc(v_b_3121_);
lean_dec_ref_known(v_a_3008_, 4);
v_a_3122_ = lean_ctor_get(v_b_3009_, 2);
lean_inc(v_a_3122_);
v_b_3123_ = lean_ctor_get(v_b_3009_, 3);
lean_inc(v_b_3123_);
lean_dec_ref_known(v_b_3009_, 4);
v_da1_3021_ = v_a_3120_;
v_da2_3022_ = v_b_3121_;
v_db1_3023_ = v_a_3122_;
v_db2_3024_ = v_b_3123_;
v___y_3025_ = v_a_3010_;
goto v___jp_3020_;
}
else
{
lean_dec_ref_known(v_a_3008_, 4);
lean_dec(v_b_3009_);
v___y_3016_ = v_a_3010_;
goto v___jp_3015_;
}
}
}
v___jp_3011_:
{
uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = 0;
v___x_3013_ = lean_box(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v_a_3010_);
return v___x_3014_;
}
v___jp_3015_:
{
uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = 0;
v___x_3018_ = lean_box(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___y_3016_);
return v___x_3019_;
}
v___jp_3020_:
{
lean_object* v___x_3026_; lean_object* v_fst_3027_; uint8_t v___x_3028_; 
v___x_3026_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_3021_, v_db1_3023_, v___y_3025_);
v_fst_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_fst_3027_);
v___x_3028_ = lean_unbox(v_fst_3027_);
lean_dec(v_fst_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v_db2_3024_);
lean_dec(v_da2_3022_);
return v___x_3026_;
}
else
{
lean_object* v_snd_3029_; lean_object* v___x_3030_; 
v_snd_3029_ = lean_ctor_get(v___x_3026_, 1);
lean_inc(v_snd_3029_);
lean_dec_ref(v___x_3026_);
v___x_3030_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_3022_, v_db2_3024_, v_snd_3029_);
return v___x_3030_;
}
}
v___jp_3031_:
{
uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_string_dec_eq(v_sa_3032_, v_sb_3033_);
lean_dec_ref(v_sb_3033_);
lean_dec_ref(v_sa_3032_);
v___x_3036_ = lean_box(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___y_3034_);
return v___x_3037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3124_, lean_object* v_b_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_cacheKey_3129_; lean_object* v___x_3130_; 
lean_inc(v_a_3124_);
v___x_3127_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3124_);
lean_inc(v_b_3125_);
v___x_3128_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3125_);
v_cacheKey_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3129_, 0, v___x_3127_);
lean_ctor_set(v_cacheKey_3129_, 1, v___x_3128_);
v___x_3130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_a_3126_, v_cacheKey_3129_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; lean_object* v___x_3132_; 
lean_dec_ref_known(v_cacheKey_3129_, 2);
lean_dec(v_b_3125_);
lean_dec(v_a_3124_);
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_val_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_val_3131_);
lean_ctor_set(v___x_3132_, 1, v_a_3126_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v_fst_3134_; lean_object* v_snd_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v___x_3130_);
v___x_3133_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(v_a_3124_, v_b_3125_, v_a_3126_);
v_fst_3134_ = lean_ctor_get(v___x_3133_, 0);
v_snd_3135_ = lean_ctor_get(v___x_3133_, 1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3137_ = v___x_3133_;
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_snd_3135_);
lean_inc(v_fst_3134_);
lean_dec(v___x_3133_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
lean_inc(v_fst_3134_);
v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_snd_3135_, v_cacheKey_3129_, v_fst_3134_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_fst_3134_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_unsigned_to_nat(16u);
v___x_3146_ = lean_mk_array(v___x_3145_, v___x_3144_);
return v___x_3146_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v___x_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3150_, lean_object* v_b_3151_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_fst_3154_; uint8_t v___x_3155_; 
v___x_3152_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3153_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3150_, v_b_3151_, v___x_3152_);
v_fst_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_fst_3154_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = lean_unbox(v_fst_3154_);
lean_dec(v_fst_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3156_, lean_object* v_b_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3156_, v_b_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_a_3160_, lean_object* v_choiceStx_3161_, lean_object* v___x_3162_, lean_object* v_as_3163_, size_t v_sz_3164_, size_t v_i_3165_, lean_object* v_b_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_a_3170_; lean_object* v_a_3171_; uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_lt(v_i_3165_, v_sz_3164_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_dec(v_choiceStx_3161_);
lean_dec_ref(v_a_3160_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3166_);
lean_ctor_set(v___x_3176_, 1, v___y_3168_);
return v___x_3176_;
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3178_; 
lean_dec_ref(v___y_3168_);
v_a_3177_ = lean_array_uget_borrowed(v_as_3163_, v_i_3165_);
lean_inc_ref(v_a_3160_);
lean_inc(v_a_3177_);
v___x_3178_ = l_Lean_Fmt_fmt(v_a_3177_, v___y_3167_, v_a_3160_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_snd_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3258_; 
v_snd_3179_ = lean_ctor_get(v_b_3166_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_b_3166_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v_b_3166_, 0);
lean_dec(v_unused_3259_);
v___x_3181_ = v_b_3166_;
v_isShared_3182_ = v_isSharedCheck_3258_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_snd_3179_);
lean_dec(v_b_3166_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3258_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_a_3183_; lean_object* v_a_3184_; lean_object* v_fst_3185_; lean_object* v_snd_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3257_; 
v_a_3183_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3183_);
v_a_3184_ = lean_ctor_get(v___x_3178_, 1);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3178_, 2);
v_fst_3185_ = lean_ctor_get(v_snd_3179_, 0);
v_snd_3186_ = lean_ctor_get(v_snd_3179_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_snd_3179_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3188_ = v_snd_3179_;
v_isShared_3189_ = v_isSharedCheck_3257_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_snd_3186_);
lean_inc(v_fst_3185_);
lean_dec(v_snd_3179_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3257_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___x_3219_; lean_object* v_first_x3f_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; 
v___x_3219_ = lean_box(0);
if (lean_obj_tag(v_fst_3185_) == 0)
{
goto v___jp_3252_;
}
else
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = lean_unsigned_to_nat(0u);
v___x_3256_ = lean_nat_dec_eq(v___x_3162_, v___x_3255_);
if (v___x_3256_ == 0)
{
v_first_x3f_3221_ = v_fst_3185_;
v___y_3222_ = v___y_3167_;
v___y_3223_ = v_a_3184_;
goto v___jp_3220_;
}
else
{
lean_dec_ref_known(v_fst_3185_, 1);
goto v___jp_3252_;
}
}
v___jp_3190_:
{
lean_object* v___x_3193_; 
v___x_3193_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_choiceStx_3161_, v___y_3192_, v_a_3160_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3209_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_a_3195_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3197_ = v___x_3193_;
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3194_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___y_3191_);
v___x_3201_ = v___x_3188_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___y_3191_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_snd_3186_);
v___x_3201_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3201_);
lean_ctor_set(v___x_3181_, 0, v___x_3199_);
v___x_3203_ = v___x_3181_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3203_);
v___x_3205_ = v___x_3197_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_a_3195_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v___y_3191_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_del_object(v___x_3181_);
v_a_3210_ = lean_ctor_get(v___x_3193_, 0);
v_a_3211_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3193_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_inc(v_a_3210_);
lean_dec(v___x_3193_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
v___jp_3220_:
{
uint8_t v___x_3224_; 
lean_inc(v_a_3183_);
v___x_3224_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3183_);
if (v___x_3224_ == 0)
{
if (lean_obj_tag(v_snd_3186_) == 1)
{
lean_object* v_val_3225_; lean_object* v_fst_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3244_; 
v_val_3225_ = lean_ctor_get(v_snd_3186_, 0);
lean_inc(v_val_3225_);
v_fst_3226_ = lean_ctor_get(v_val_3225_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_val_3225_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_val_3225_, 1);
lean_dec(v_unused_3245_);
v___x_3228_ = v_val_3225_;
v_isShared_3229_ = v_isSharedCheck_3244_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_fst_3226_);
lean_dec(v_val_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3244_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_doc_3230_; lean_object* v_doc_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3242_; 
v_doc_3230_ = lean_ctor_get(v_a_3183_, 0);
lean_inc(v_doc_3230_);
lean_dec(v_a_3183_);
v_doc_3231_ = lean_ctor_get(v_fst_3226_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_fst_3226_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v_fst_3226_, 1);
lean_dec(v_unused_3243_);
v___x_3233_ = v_fst_3226_;
v_isShared_3234_ = v_isSharedCheck_3242_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_doc_3231_);
lean_dec(v_fst_3226_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3242_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3230_, v_doc_3231_);
if (v___x_3235_ == 0)
{
lean_del_object(v___x_3233_);
lean_del_object(v___x_3228_);
lean_dec_ref(v___y_3223_);
v___y_3191_ = v_first_x3f_3221_;
v___y_3192_ = v___y_3222_;
goto v___jp_3190_;
}
else
{
if (v___x_3224_ == 0)
{
lean_object* v___x_3237_; 
lean_del_object(v___x_3188_);
lean_del_object(v___x_3181_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v_snd_3186_);
lean_ctor_set(v___x_3228_, 0, v_first_x3f_3221_);
v___x_3237_ = v___x_3228_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_first_x3f_3221_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_snd_3186_);
v___x_3237_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3237_);
lean_ctor_set(v___x_3233_, 0, v___x_3219_);
v___x_3239_ = v___x_3233_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
v_a_3170_ = v___x_3239_;
v_a_3171_ = v___y_3223_;
goto v___jp_3169_;
}
}
}
else
{
lean_del_object(v___x_3233_);
lean_del_object(v___x_3228_);
lean_dec_ref(v___y_3223_);
v___y_3191_ = v_first_x3f_3221_;
v___y_3192_ = v___y_3222_;
goto v___jp_3190_;
}
}
}
}
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_del_object(v___x_3181_);
lean_inc_ref(v___y_3223_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3183_);
lean_ctor_set(v___x_3246_, 1, v___y_3223_);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_first_x3f_3221_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3219_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v_a_3170_ = v___x_3249_;
v_a_3171_ = v___y_3223_;
goto v___jp_3169_;
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_del_object(v___x_3188_);
lean_dec(v_a_3183_);
lean_del_object(v___x_3181_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_first_x3f_3221_);
lean_ctor_set(v___x_3250_, 1, v_snd_3186_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3219_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v_a_3170_ = v___x_3251_;
v_a_3171_ = v___y_3223_;
goto v___jp_3169_;
}
}
v___jp_3252_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_inc(v_a_3184_);
lean_inc(v_a_3183_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_a_3183_);
lean_ctor_set(v___x_3253_, 1, v_a_3184_);
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
v_first_x3f_3221_ = v___x_3254_;
v___y_3222_ = v___y_3167_;
v___y_3223_ = v_a_3184_;
goto v___jp_3220_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v_b_3166_);
lean_dec(v_choiceStx_3161_);
lean_dec_ref(v_a_3160_);
v_a_3260_ = lean_ctor_get(v___x_3178_, 0);
v_a_3261_ = lean_ctor_get(v___x_3178_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3178_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_inc(v_a_3260_);
lean_dec(v___x_3178_);
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
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3260_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_a_3261_);
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
v___jp_3169_:
{
size_t v___x_3172_; size_t v___x_3173_; 
v___x_3172_ = ((size_t)1ULL);
v___x_3173_ = lean_usize_add(v_i_3165_, v___x_3172_);
v_i_3165_ = v___x_3173_;
v_b_3166_ = v_a_3170_;
v___y_3168_ = v_a_3171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object* v_a_3269_, lean_object* v_choiceStx_3270_, lean_object* v___x_3271_, lean_object* v_as_3272_, lean_object* v_sz_3273_, lean_object* v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3273_);
lean_dec(v_sz_3273_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3274_);
lean_dec(v_i_3274_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3269_, v_choiceStx_3270_, v___x_3271_, v_as_3272_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3275_, v___y_3276_, v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_as_3272_);
lean_dec(v___x_3271_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v___y_3290_; lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3300_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3286_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_nat_dec_eq(v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; size_t v_sz_3305_; size_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3303_ = l_Lean_Syntax_getArgs(v_choiceStx_3286_);
v___x_3304_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1));
v_sz_3305_ = lean_array_size(v___x_3303_);
v___x_3306_ = ((size_t)0ULL);
lean_inc_ref(v_a_3288_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3288_, v_choiceStx_3286_, v___x_3300_, v___x_3303_, v_sz_3305_, v___x_3306_, v___x_3304_, v_a_3287_, v_a_3288_);
lean_dec_ref(v___x_3303_);
lean_dec(v___x_3300_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v_fst_3309_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
v_fst_3309_ = lean_ctor_get(v_a_3308_, 0);
if (lean_obj_tag(v_fst_3309_) == 0)
{
lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3325_; 
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; lean_object* v_unused_3327_; 
v_unused_3326_ = lean_ctor_get(v___x_3307_, 1);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3327_);
v___x_3311_ = v___x_3307_;
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
else
{
lean_dec(v___x_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_snd_3313_; lean_object* v_snd_3314_; 
v_snd_3313_ = lean_ctor_get(v_a_3308_, 1);
lean_inc(v_snd_3313_);
lean_dec(v_a_3308_);
v_snd_3314_ = lean_ctor_get(v_snd_3313_, 1);
if (lean_obj_tag(v_snd_3314_) == 1)
{
lean_object* v_val_3315_; lean_object* v_fst_3316_; lean_object* v_snd_3317_; lean_object* v___x_3319_; 
lean_inc_ref(v_snd_3314_);
lean_dec(v_snd_3313_);
v_val_3315_ = lean_ctor_get(v_snd_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v_snd_3314_, 1);
v_fst_3316_ = lean_ctor_get(v_val_3315_, 0);
lean_inc(v_fst_3316_);
v_snd_3317_ = lean_ctor_get(v_val_3315_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_val_3315_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v_snd_3317_);
lean_ctor_set(v___x_3311_, 0, v_fst_3316_);
v___x_3319_ = v___x_3311_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_fst_3316_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_snd_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
lean_object* v_fst_3321_; 
lean_del_object(v___x_3311_);
v_fst_3321_ = lean_ctor_get(v_snd_3313_, 0);
lean_inc(v_fst_3321_);
lean_dec(v_snd_3313_);
if (lean_obj_tag(v_fst_3321_) == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3323_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v___x_3322_);
v___y_3290_ = v___x_3323_;
goto v___jp_3289_;
}
else
{
lean_object* v_val_3324_; 
v_val_3324_ = lean_ctor_get(v_fst_3321_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v_fst_3321_, 1);
v___y_3290_ = v_val_3324_;
goto v___jp_3289_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
lean_inc_ref(v_fst_3309_);
lean_dec(v_a_3308_);
v_a_3328_ = lean_ctor_get(v___x_3307_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3337_);
v___x_3330_ = v___x_3307_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3307_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_val_3332_; lean_object* v___x_3334_; 
v_val_3332_ = lean_ctor_get(v_fst_3309_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_fst_3309_, 1);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v_val_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_a_3328_);
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
else
{
lean_object* v_a_3338_; lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
v_a_3338_ = lean_ctor_get(v___x_3307_, 0);
v_a_3339_ = lean_ctor_get(v___x_3307_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3307_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_inc(v_a_3338_);
lean_dec(v___x_3307_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3338_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v___x_3300_);
v___x_3347_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3348_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3347_, v_choiceStx_3286_, v_a_3288_);
lean_dec(v_choiceStx_3286_);
return v___x_3348_;
}
v___jp_3289_:
{
lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_fst_3291_ = lean_ctor_get(v___y_3290_, 0);
v_snd_3292_ = lean_ctor_get(v___y_3290_, 1);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___y_3290_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___y_3290_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_snd_3292_);
lean_inc(v_fst_3291_);
lean_dec(v___y_3290_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_fst_3291_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_snd_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3349_, v_a_3350_, v_a_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3353_, lean_object* v_m_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_3354_, v_a_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3357_, lean_object* v_m_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_00_u03b2_3357_, v_m_3358_, v_a_3359_);
lean_dec_ref(v_a_3359_);
lean_dec_ref(v_m_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3361_, lean_object* v_m_3362_, lean_object* v_a_3363_, lean_object* v_b_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_m_3362_, v_a_3363_, v_b_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3366_, lean_object* v_a_3367_, lean_object* v_x_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_3367_, v_x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3370_, lean_object* v_a_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_3370_, v_a_3371_, v_x_3372_);
lean_dec(v_x_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_3374_, lean_object* v_a_3375_, lean_object* v_x_3376_){
_start:
{
uint8_t v___x_3377_; 
v___x_3377_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_3375_, v_x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3378_, lean_object* v_a_3379_, lean_object* v_x_3380_){
_start:
{
uint8_t v_res_3381_; lean_object* v_r_3382_; 
v_res_3381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(v_00_u03b2_3378_, v_a_3379_, v_x_3380_);
lean_dec(v_x_3380_);
lean_dec_ref(v_a_3379_);
v_r_3382_ = lean_box(v_res_3381_);
return v_r_3382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_3383_, lean_object* v_data_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_data_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_3386_, lean_object* v_a_3387_, lean_object* v_b_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_3387_, v_b_3388_, v_x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object* v_00_u03b2_3391_, lean_object* v_i_3392_, lean_object* v_source_3393_, lean_object* v_target_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v_i_3392_, v_source_3393_, v_target_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object* v_00_u03b2_3396_, lean_object* v_x_3397_, lean_object* v_x_3398_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_x_3397_, v_x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(size_t v_sz_3400_, size_t v_i_3401_, lean_object* v_bs_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_usize_dec_lt(v_i_3401_, v_sz_3400_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_bs_3402_);
lean_ctor_set(v___x_3406_, 1, v___y_3404_);
return v___x_3406_;
}
else
{
lean_object* v_v_3407_; lean_object* v___x_3408_; 
v_v_3407_ = lean_array_uget_borrowed(v_bs_3402_, v_i_3401_);
lean_inc(v_v_3407_);
v___x_3408_ = l_Lean_Fmt_fmt(v_v_3407_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v_a_3410_; lean_object* v___x_3411_; lean_object* v_bs_x27_3412_; size_t v___x_3413_; size_t v___x_3414_; lean_object* v___x_3415_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
v_a_3410_ = lean_ctor_get(v___x_3408_, 1);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3408_, 2);
v___x_3411_ = lean_unsigned_to_nat(0u);
v_bs_x27_3412_ = lean_array_uset(v_bs_3402_, v_i_3401_, v___x_3411_);
v___x_3413_ = ((size_t)1ULL);
v___x_3414_ = lean_usize_add(v_i_3401_, v___x_3413_);
v___x_3415_ = lean_array_uset(v_bs_x27_3412_, v_i_3401_, v_a_3409_);
v_i_3401_ = v___x_3414_;
v_bs_3402_ = v___x_3415_;
v___y_3404_ = v_a_3410_;
goto _start;
}
else
{
lean_object* v_a_3417_; lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_bs_3402_);
v_a_3417_ = lean_ctor_get(v___x_3408_, 0);
v_a_3418_ = lean_ctor_get(v___x_3408_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3408_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_inc(v_a_3417_);
lean_dec(v___x_3408_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3417_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0___boxed(lean_object* v_sz_3426_, lean_object* v_i_3427_, lean_object* v_bs_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
size_t v_sz_boxed_3431_; size_t v_i_boxed_3432_; lean_object* v_res_3433_; 
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3426_);
lean_dec(v_sz_3426_);
v_i_boxed_3432_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_boxed_3431_, v_i_boxed_3432_, v_bs_3428_, v___y_3429_, v___y_3430_);
lean_dec_ref(v___y_3429_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_assoc_x3f_3440_, lean_object* v_extendedChainKinds_3441_, lean_object* v_stx_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; uint8_t v_val_3452_; 
if (lean_obj_tag(v_assoc_x3f_3440_) == 0)
{
lean_object* v_env_3474_; lean_object* v_opts_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_env_3474_ = lean_ctor_get(v_a_3443_, 0);
v_opts_3475_ = lean_ctor_get(v_a_3443_, 3);
lean_inc(v_stx_3442_);
v___x_3476_ = l_Lean_Syntax_getKind(v_stx_3442_);
lean_inc_ref(v_env_3474_);
v___x_3477_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_3474_, v_opts_3475_, v___x_3476_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_dec(v_stx_3442_);
lean_dec_ref(v_extendedChainKinds_3441_);
v___x_3478_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
v___x_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v_a_3444_);
return v___x_3479_;
}
else
{
lean_object* v_val_3480_; uint8_t v_assoc_3481_; 
v_val_3480_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v___x_3477_, 1);
v_assoc_3481_ = lean_ctor_get_uint8(v_val_3480_, sizeof(void*)*1);
lean_dec(v_val_3480_);
v_val_3452_ = v_assoc_3481_;
goto v___jp_3451_;
}
}
else
{
lean_object* v_val_3482_; uint8_t v___x_3483_; 
v_val_3482_ = lean_ctor_get(v_assoc_x3f_3440_, 0);
v___x_3483_ = lean_unbox(v_val_3482_);
v_val_3452_ = v___x_3483_;
goto v___jp_3451_;
}
v___jp_3445_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = l_Lean_Fmt_Layouts_infixOperator(v___y_3447_, v___y_3448_);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v___y_3446_);
return v___x_3450_;
}
v___jp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; size_t v_sz_3456_; size_t v___x_3457_; lean_object* v___x_3458_; 
lean_inc(v_stx_3442_);
v___x_3453_ = l_Lean_Syntax_getKind(v_stx_3442_);
v___x_3454_ = lean_array_push(v_extendedChainKinds_3441_, v___x_3453_);
v___x_3455_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v___x_3454_, v_stx_3442_);
lean_dec_ref(v___x_3454_);
v_sz_3456_ = lean_array_size(v___x_3455_);
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_3456_, v___x_3457_, v___x_3455_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3458_) == 0)
{
if (v_val_3452_ == 2)
{
lean_object* v_a_3459_; lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
v_a_3460_ = lean_ctor_get(v___x_3458_, 1);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3458_, 2);
v___x_3461_ = ((lean_object*)(l_Lean_Fmt_fmtInfixOperator___closed__0));
v___y_3446_ = v_a_3460_;
v___y_3447_ = v_a_3459_;
v___y_3448_ = v___x_3461_;
goto v___jp_3445_;
}
else
{
lean_object* v_a_3462_; lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3462_);
v_a_3463_ = lean_ctor_get(v___x_3458_, 1);
lean_inc(v_a_3463_);
lean_dec_ref_known(v___x_3458_, 2);
v___x_3464_ = ((lean_object*)(l_Lean_Fmt_fmtInfixOperator___closed__1));
v___y_3446_ = v_a_3463_;
v___y_3447_ = v_a_3462_;
v___y_3448_ = v___x_3464_;
goto v___jp_3445_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3465_ = lean_ctor_get(v___x_3458_, 0);
v_a_3466_ = lean_ctor_get(v___x_3458_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3458_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_inc(v_a_3465_);
lean_dec(v___x_3458_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3465_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_assoc_x3f_3484_, lean_object* v_extendedChainKinds_3485_, lean_object* v_stx_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Fmt_fmtInfixOperator(v_assoc_x3f_3484_, v_extendedChainKinds_3485_, v_stx_3486_, v_a_3487_, v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_assoc_x3f_3484_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = l_Lean_Syntax_getNumArgs(v_stx_3490_);
v___x_3494_ = lean_unsigned_to_nat(2u);
v___x_3495_ = lean_nat_dec_eq(v___x_3493_, v___x_3494_);
lean_dec(v___x_3493_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
v___x_3497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v_a_3492_);
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3490_, v___x_3498_, v_a_3492_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
v_a_3501_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3499_, 2);
v___x_3502_ = l_Lean_Fmt_fmt(v_a_3500_, v_a_3491_, v_a_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
v_a_3504_ = lean_ctor_get(v___x_3502_, 1);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3502_, 2);
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3490_, v___x_3505_, v_a_3504_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v_a_3508_; lean_object* v___x_3509_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
v_a_3508_ = lean_ctor_get(v___x_3506_, 1);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3506_, 2);
v___x_3509_ = l_Lean_Fmt_fmt(v_a_3507_, v_a_3491_, v_a_3508_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3520_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_a_3511_ = lean_ctor_get(v___x_3509_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3513_ = v___x_3509_;
v_isShared_3514_ = v_isSharedCheck_3520_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3520_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
uint8_t v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3515_ = 1;
v___x_3516_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_3503_, v_a_3510_, v___x_3515_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3516_);
v___x_3518_ = v___x_3513_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_a_3511_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_dec(v_a_3503_);
return v___x_3509_;
}
}
else
{
lean_object* v_a_3521_; lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_a_3503_);
v_a_3521_ = lean_ctor_get(v___x_3506_, 0);
v_a_3522_ = lean_ctor_get(v___x_3506_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3506_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_inc(v_a_3521_);
lean_dec(v___x_3506_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3521_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
return v___x_3502_;
}
}
else
{
lean_object* v_a_3530_; lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3530_ = lean_ctor_get(v___x_3499_, 0);
v_a_3531_ = lean_ctor_get(v___x_3499_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3499_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_inc(v_a_3530_);
lean_dec(v___x_3499_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3530_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3539_, v_a_3540_, v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_stx_3539_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3546_ = l_Lean_Syntax_getNumArgs(v_stx_3543_);
v___x_3547_ = lean_unsigned_to_nat(2u);
v___x_3548_ = lean_nat_dec_eq(v___x_3546_, v___x_3547_);
lean_dec(v___x_3546_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
v___x_3550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v_a_3545_);
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3543_, v___x_3551_, v_a_3545_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
v_a_3554_ = lean_ctor_get(v___x_3552_, 1);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3552_, 2);
v___x_3555_ = l_Lean_Fmt_fmt(v_a_3553_, v_a_3544_, v_a_3554_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
v_a_3557_ = lean_ctor_get(v___x_3555_, 1);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3555_, 2);
v___x_3558_ = lean_unsigned_to_nat(1u);
v___x_3559_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3543_, v___x_3558_, v_a_3557_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
v_a_3561_ = lean_ctor_get(v___x_3559_, 1);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3559_, 2);
v___x_3562_ = l_Lean_Fmt_fmt(v_a_3560_, v_a_3544_, v_a_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3573_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_a_3564_ = lean_ctor_get(v___x_3562_, 1);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3566_ = v___x_3562_;
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3568_ = 0;
v___x_3569_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3556_, v_a_3563_, v___x_3568_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3569_);
v___x_3571_ = v___x_3566_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_a_3564_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
else
{
lean_dec(v_a_3556_);
return v___x_3562_;
}
}
else
{
lean_object* v_a_3574_; lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_a_3556_);
v_a_3574_ = lean_ctor_get(v___x_3559_, 0);
v_a_3575_ = lean_ctor_get(v___x_3559_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3559_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_inc(v_a_3574_);
lean_dec(v___x_3559_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3574_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
return v___x_3555_;
}
}
else
{
lean_object* v_a_3583_; lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
v_a_3583_ = lean_ctor_get(v___x_3552_, 0);
v_a_3584_ = lean_ctor_get(v___x_3552_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3552_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_inc(v_a_3583_);
lean_dec(v___x_3552_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3583_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_3592_, v_a_3593_, v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_stx_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_3596_, size_t v_i_3597_, lean_object* v_bs_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v___x_3601_; 
v___x_3601_ = lean_usize_dec_lt(v_i_3597_, v_sz_3596_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v_bs_3598_);
lean_ctor_set(v___x_3602_, 1, v___y_3600_);
return v___x_3602_;
}
else
{
lean_object* v_v_3603_; lean_object* v_elseTk_3604_; lean_object* v_ifTk_3605_; lean_object* v_cond_3606_; lean_object* v_thenTk_3607_; lean_object* v_body_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3669_; 
v_v_3603_ = lean_array_uget(v_bs_3598_, v_i_3597_);
v_elseTk_3604_ = lean_ctor_get(v_v_3603_, 0);
v_ifTk_3605_ = lean_ctor_get(v_v_3603_, 1);
v_cond_3606_ = lean_ctor_get(v_v_3603_, 2);
v_thenTk_3607_ = lean_ctor_get(v_v_3603_, 3);
v_body_3608_ = lean_ctor_get(v_v_3603_, 4);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_v_3603_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3610_ = v_v_3603_;
v_isShared_3611_ = v_isSharedCheck_3669_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_body_3608_);
lean_inc(v_thenTk_3607_);
lean_inc(v_cond_3606_);
lean_inc(v_ifTk_3605_);
lean_inc(v_elseTk_3604_);
lean_dec(v_v_3603_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3669_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Fmt_fmt(v_elseTk_3604_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_a_3614_; lean_object* v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
v_a_3614_ = lean_ctor_get(v___x_3612_, 1);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3612_, 2);
v___x_3615_ = l_Lean_Fmt_fmt(v_ifTk_3605_, v___y_3599_, v_a_3614_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
v_a_3617_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3615_, 2);
v___x_3618_ = l_Lean_Fmt_fmt(v_thenTk_3607_, v___y_3599_, v_a_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_a_3620_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
v_a_3620_ = lean_ctor_get(v___x_3618_, 1);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3618_, 2);
v___x_3621_ = l_Lean_Fmt_fmt(v_body_3608_, v___y_3599_, v_a_3620_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v_a_3623_; lean_object* v___x_3624_; lean_object* v_bs_x27_3625_; lean_object* v___x_3627_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
v_a_3623_ = lean_ctor_get(v___x_3621_, 1);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3621_, 2);
v___x_3624_ = lean_unsigned_to_nat(0u);
v_bs_x27_3625_ = lean_array_uset(v_bs_3598_, v_i_3597_, v___x_3624_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 4, v_a_3622_);
lean_ctor_set(v___x_3610_, 3, v_a_3619_);
lean_ctor_set(v___x_3610_, 1, v_a_3616_);
lean_ctor_set(v___x_3610_, 0, v_a_3613_);
v___x_3627_ = v___x_3610_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3613_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_a_3616_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_cond_3606_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_a_3619_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
size_t v___x_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3597_, v___x_3628_);
v___x_3630_ = lean_array_uset(v_bs_x27_3625_, v_i_3597_, v___x_3627_);
v_i_3597_ = v___x_3629_;
v_bs_3598_ = v___x_3630_;
v___y_3600_ = v_a_3623_;
goto _start;
}
}
else
{
lean_object* v_a_3633_; lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_a_3619_);
lean_dec(v_a_3616_);
lean_dec(v_a_3613_);
lean_del_object(v___x_3610_);
lean_dec_ref(v_cond_3606_);
lean_dec_ref(v_bs_3598_);
v_a_3633_ = lean_ctor_get(v___x_3621_, 0);
v_a_3634_ = lean_ctor_get(v___x_3621_, 1);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3621_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_inc(v_a_3633_);
lean_dec(v___x_3621_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3633_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v_a_3616_);
lean_dec(v_a_3613_);
lean_del_object(v___x_3610_);
lean_dec(v_body_3608_);
lean_dec_ref(v_cond_3606_);
lean_dec_ref(v_bs_3598_);
v_a_3642_ = lean_ctor_get(v___x_3618_, 0);
v_a_3643_ = lean_ctor_get(v___x_3618_, 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3618_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_inc(v_a_3642_);
lean_dec(v___x_3618_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3642_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec(v_a_3613_);
lean_del_object(v___x_3610_);
lean_dec(v_body_3608_);
lean_dec(v_thenTk_3607_);
lean_dec_ref(v_cond_3606_);
lean_dec_ref(v_bs_3598_);
v_a_3651_ = lean_ctor_get(v___x_3615_, 0);
v_a_3652_ = lean_ctor_get(v___x_3615_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3615_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_inc(v_a_3651_);
lean_dec(v___x_3615_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3651_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_del_object(v___x_3610_);
lean_dec(v_body_3608_);
lean_dec(v_thenTk_3607_);
lean_dec_ref(v_cond_3606_);
lean_dec(v_ifTk_3605_);
lean_dec_ref(v_bs_3598_);
v_a_3660_ = lean_ctor_get(v___x_3612_, 0);
v_a_3661_ = lean_ctor_get(v___x_3612_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3612_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_inc(v_a_3660_);
lean_dec(v___x_3612_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3660_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_3670_, lean_object* v_i_3671_, lean_object* v_bs_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
size_t v_sz_boxed_3675_; size_t v_i_boxed_3676_; lean_object* v_res_3677_; 
v_sz_boxed_3675_ = lean_unbox_usize(v_sz_3670_);
lean_dec(v_sz_3670_);
v_i_boxed_3676_ = lean_unbox_usize(v_i_3671_);
lean_dec(v_i_3671_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_3675_, v_i_boxed_3676_, v_bs_3672_, v___y_3673_, v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_3678_, lean_object* v_x_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v_a_3678_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
lean_ctor_set(v___x_3683_, 1, v___y_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_3684_, v_x_3685_, v___y_3686_, v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v_x_3685_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_3689_, lean_object* v_val_3690_, lean_object* v_elseIfs_3691_, lean_object* v_ifTk_3692_, lean_object* v_cond_3693_, lean_object* v_thenTk_3694_, lean_object* v_thenBody_3695_, lean_object* v_a_3696_, lean_object* v_____r_3697_, lean_object* v_elseBody_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_inc(v_elseBody_3698_);
v___x_3701_ = l_Lean_Syntax_getKind(v_elseBody_3698_);
v___x_3702_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_3689_, v___x_3701_);
lean_dec(v___x_3701_);
if (lean_obj_tag(v___x_3702_) == 1)
{
lean_object* v_val_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3763_; 
v_val_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3763_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_val_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3763_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
lean_inc_ref(v___y_3699_);
v___x_3707_ = lean_apply_3(v_val_3703_, v_elseBody_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
if (lean_obj_tag(v_a_3708_) == 1)
{
lean_object* v_val_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3705_);
lean_dec_ref(v_a_3696_);
v_val_3709_ = lean_ctor_get(v_a_3708_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3711_ = v_a_3708_;
v_isShared_3712_ = v_isSharedCheck_3741_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_val_3709_);
lean_dec(v_a_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3741_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3739_; 
v_a_3713_ = lean_ctor_get(v___x_3707_, 1);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; 
v_unused_3740_ = lean_ctor_get(v___x_3707_, 0);
lean_dec(v_unused_3740_);
v___x_3715_ = v___x_3707_;
v_isShared_3716_ = v_isSharedCheck_3739_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3707_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3739_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_ifTk_3717_; lean_object* v_cond_3718_; lean_object* v_thenTk_3719_; lean_object* v_thenBody_3720_; lean_object* v_elseTk_x3f_3721_; lean_object* v_elseBody_x3f_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3737_; 
v_ifTk_3717_ = lean_ctor_get(v_val_3709_, 0);
v_cond_3718_ = lean_ctor_get(v_val_3709_, 1);
v_thenTk_3719_ = lean_ctor_get(v_val_3709_, 2);
v_thenBody_3720_ = lean_ctor_get(v_val_3709_, 3);
v_elseTk_x3f_3721_ = lean_ctor_get(v_val_3709_, 5);
v_elseBody_x3f_3722_ = lean_ctor_get(v_val_3709_, 6);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_val_3709_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v_val_3709_, 4);
lean_dec(v_unused_3738_);
v___x_3724_ = v_val_3709_;
v_isShared_3725_ = v_isSharedCheck_3737_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_elseBody_x3f_3722_);
lean_inc(v_elseTk_x3f_3721_);
lean_inc(v_thenBody_3720_);
lean_inc(v_thenTk_3719_);
lean_inc(v_cond_3718_);
lean_inc(v_ifTk_3717_);
lean_dec(v_val_3709_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3737_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3726_, 0, v_val_3690_);
lean_ctor_set(v___x_3726_, 1, v_ifTk_3717_);
lean_ctor_set(v___x_3726_, 2, v_cond_3718_);
lean_ctor_set(v___x_3726_, 3, v_thenTk_3719_);
lean_ctor_set(v___x_3726_, 4, v_thenBody_3720_);
v___x_3727_ = lean_array_push(v_elseIfs_3691_, v___x_3726_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 4, v___x_3727_);
lean_ctor_set(v___x_3724_, 3, v_thenBody_3695_);
lean_ctor_set(v___x_3724_, 2, v_thenTk_3694_);
lean_ctor_set(v___x_3724_, 1, v_cond_3693_);
lean_ctor_set(v___x_3724_, 0, v_ifTk_3692_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_ifTk_3692_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_cond_3693_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_thenTk_3694_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_thenBody_3695_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3736_, 5, v_elseTk_x3f_3721_);
lean_ctor_set(v_reuseFailAlloc_3736_, 6, v_elseBody_x3f_3722_);
v___x_3729_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3729_);
v___x_3731_ = v___x_3711_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3731_);
v___x_3733_ = v___x_3715_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_a_3713_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_a_3708_);
lean_dec(v_thenBody_3695_);
lean_dec(v_thenTk_3694_);
lean_dec_ref(v_cond_3693_);
lean_dec(v_ifTk_3692_);
lean_dec_ref(v_elseIfs_3691_);
lean_dec(v_val_3690_);
v_a_3742_ = lean_ctor_get(v___x_3707_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v___x_3707_, 0);
lean_dec(v_unused_3753_);
v___x_3744_ = v___x_3707_;
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3707_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 0);
lean_ctor_set(v___x_3705_, 0, v_a_3696_);
v___x_3747_ = v___x_3705_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3696_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3747_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_a_3742_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3705_);
lean_dec_ref(v_a_3696_);
lean_dec(v_thenBody_3695_);
lean_dec(v_thenTk_3694_);
lean_dec_ref(v_cond_3693_);
lean_dec(v_ifTk_3692_);
lean_dec_ref(v_elseIfs_3691_);
lean_dec(v_val_3690_);
v_a_3754_ = lean_ctor_get(v___x_3707_, 0);
v_a_3755_ = lean_ctor_get(v___x_3707_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3707_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_inc(v_a_3754_);
lean_dec(v___x_3707_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3754_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_a_3755_);
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
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_dec(v___x_3702_);
lean_dec(v_elseBody_3698_);
lean_dec(v_thenBody_3695_);
lean_dec(v_thenTk_3694_);
lean_dec_ref(v_cond_3693_);
lean_dec(v_ifTk_3692_);
lean_dec_ref(v_elseIfs_3691_);
lean_dec(v_val_3690_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_a_3696_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___y_3700_);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_3766_, lean_object* v_val_3767_, lean_object* v_elseIfs_3768_, lean_object* v_ifTk_3769_, lean_object* v_cond_3770_, lean_object* v_thenTk_3771_, lean_object* v_thenBody_3772_, lean_object* v_a_3773_, lean_object* v_____r_3774_, lean_object* v_elseBody_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_3766_, v_val_3767_, v_elseIfs_3768_, v_ifTk_3769_, v_cond_3770_, v_thenTk_3771_, v_thenBody_3772_, v_a_3773_, v_____r_3774_, v_elseBody_3775_, v___y_3776_, v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_3793_, lean_object* v_a_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___y_3798_; lean_object* v_elseTk_x3f_3822_; 
v_elseTk_x3f_3822_ = lean_ctor_get(v_a_3794_, 5);
if (lean_obj_tag(v_elseTk_x3f_3822_) == 1)
{
lean_object* v_elseBody_x3f_3823_; 
v_elseBody_x3f_3823_ = lean_ctor_get(v_a_3794_, 6);
if (lean_obj_tag(v_elseBody_x3f_3823_) == 1)
{
lean_object* v_ifTk_3824_; lean_object* v_cond_3825_; lean_object* v_thenTk_3826_; lean_object* v_thenBody_3827_; lean_object* v_elseIfs_3828_; lean_object* v_val_3829_; lean_object* v_val_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v_ifTk_3824_ = lean_ctor_get(v_a_3794_, 0);
lean_inc(v_ifTk_3824_);
v_cond_3825_ = lean_ctor_get(v_a_3794_, 1);
lean_inc_ref(v_cond_3825_);
v_thenTk_3826_ = lean_ctor_get(v_a_3794_, 2);
lean_inc(v_thenTk_3826_);
v_thenBody_3827_ = lean_ctor_get(v_a_3794_, 3);
lean_inc(v_thenBody_3827_);
v_elseIfs_3828_ = lean_ctor_get(v_a_3794_, 4);
lean_inc_ref(v_elseIfs_3828_);
v_val_3829_ = lean_ctor_get(v_elseTk_x3f_3822_, 0);
lean_inc(v_val_3829_);
v_val_3830_ = lean_ctor_get(v_elseBody_x3f_3823_, 0);
v___x_3831_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_3830_);
v___x_3832_ = l_Lean_Syntax_isOfKind(v_val_3830_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_inc(v_val_3830_);
v___x_3833_ = lean_box(0);
lean_inc_ref(v___x_3793_);
v___x_3834_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_3793_, v_val_3829_, v_elseIfs_3828_, v_ifTk_3824_, v_cond_3825_, v_thenTk_3826_, v_thenBody_3827_, v_a_3794_, v___x_3833_, v_val_3830_, v___y_3795_, v___y_3796_);
v___y_3798_ = v___x_3834_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = l_Lean_Syntax_getArg(v_val_3830_, v___x_3835_);
v___x_3837_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_3836_);
v___x_3838_ = l_Lean_Syntax_isOfKind(v___x_3836_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_inc(v_val_3830_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
lean_inc_ref(v___x_3793_);
v___x_3840_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_3793_, v_val_3829_, v_elseIfs_3828_, v_ifTk_3824_, v_cond_3825_, v_thenTk_3826_, v_thenBody_3827_, v_a_3794_, v___x_3839_, v_val_3830_, v___y_3795_, v___y_3796_);
v___y_3798_ = v___x_3840_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = l_Lean_Syntax_getArg(v___x_3836_, v___x_3835_);
lean_dec(v___x_3836_);
v___x_3842_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3841_);
v___x_3843_ = l_Lean_Syntax_matchesNull(v___x_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_inc(v_val_3830_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
lean_inc_ref(v___x_3793_);
v___x_3845_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_3793_, v_val_3829_, v_elseIfs_3828_, v_ifTk_3824_, v_cond_3825_, v_thenTk_3826_, v_thenBody_3827_, v_a_3794_, v___x_3844_, v_val_3830_, v___y_3795_, v___y_3796_);
v___y_3798_ = v___x_3845_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = l_Lean_Syntax_getArg(v___x_3841_, v___x_3835_);
lean_dec(v___x_3841_);
v___x_3847_ = lean_box(0);
lean_inc_ref(v___x_3793_);
v___x_3848_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_3793_, v_val_3829_, v_elseIfs_3828_, v_ifTk_3824_, v_cond_3825_, v_thenTk_3826_, v_thenBody_3827_, v_a_3794_, v___x_3847_, v___x_3846_, v___y_3795_, v___y_3796_);
v___y_3798_ = v___x_3848_;
goto v___jp_3797_;
}
}
}
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_inc(v_elseBody_x3f_3823_);
lean_inc_ref(v_elseTk_x3f_3822_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v_elseTk_x3f_3822_);
lean_ctor_set(v___x_3849_, 1, v_elseBody_x3f_3823_);
v___x_3850_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_3794_, v___x_3849_, v___y_3795_, v___y_3796_);
lean_dec_ref_known(v___x_3849_, 2);
v___y_3798_ = v___x_3850_;
goto v___jp_3797_;
}
}
else
{
lean_object* v_elseBody_x3f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_elseBody_x3f_3851_ = lean_ctor_get(v_a_3794_, 6);
lean_inc(v_elseBody_x3f_3851_);
lean_inc(v_elseTk_x3f_3822_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v_elseTk_x3f_3822_);
lean_ctor_set(v___x_3852_, 1, v_elseBody_x3f_3851_);
v___x_3853_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_3794_, v___x_3852_, v___y_3795_, v___y_3796_);
lean_dec_ref_known(v___x_3852_, 2);
v___y_3798_ = v___x_3853_;
goto v___jp_3797_;
}
v___jp_3797_:
{
if (lean_obj_tag(v___y_3798_) == 0)
{
lean_object* v_a_3799_; 
v_a_3799_ = lean_ctor_get(v___y_3798_, 0);
lean_inc(v_a_3799_);
if (lean_obj_tag(v_a_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v___x_3793_);
v_a_3800_ = lean_ctor_get(v___y_3798_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___y_3798_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v___y_3798_, 0);
lean_dec(v_unused_3809_);
v___x_3802_ = v___y_3798_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___y_3798_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_a_3804_; lean_object* v___x_3806_; 
v_a_3804_ = lean_ctor_get(v_a_3799_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v_a_3799_, 1);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_a_3804_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3804_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_a_3800_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v_a_3811_; 
v_a_3810_ = lean_ctor_get(v___y_3798_, 1);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___y_3798_, 2);
v_a_3811_ = lean_ctor_get(v_a_3799_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v_a_3799_, 1);
v_a_3794_ = v_a_3811_;
v___y_3796_ = v_a_3810_;
goto _start;
}
}
else
{
lean_object* v_a_3813_; lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v___x_3793_);
v_a_3813_ = lean_ctor_get(v___y_3798_, 0);
v_a_3814_ = lean_ctor_get(v___y_3798_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___y_3798_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___y_3798_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_inc(v_a_3813_);
lean_dec(v___y_3798_);
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
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3813_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3814_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_3854_, lean_object* v_a_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_3854_, v_a_3855_, v___y_3856_, v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_3859_, lean_object* v_stx_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
uint8_t v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; uint8_t v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v_env_3890_; lean_object* v___x_3891_; 
v_env_3890_ = lean_ctor_get(v_a_3861_, 0);
lean_inc_ref(v_a_3861_);
lean_inc(v_stx_3860_);
v___x_3891_ = lean_apply_3(v_initialFmt_3859_, v_stx_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
if (lean_obj_tag(v_a_3892_) == 1)
{
lean_object* v_a_3893_; lean_object* v_val_3894_; lean_object* v___x_3895_; 
v_a_3893_ = lean_ctor_get(v___x_3891_, 1);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3891_, 2);
v_val_3894_ = lean_ctor_get(v_a_3892_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_a_3892_, 1);
v___x_3895_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_3860_, v_a_3861_, v_a_3893_);
lean_dec(v_stx_3860_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v_a_3897_; uint8_t v___y_3899_; uint8_t v___x_3949_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
v_a_3897_ = lean_ctor_get(v___x_3895_, 1);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3895_, 2);
v___x_3949_ = lean_unbox(v_a_3896_);
lean_dec(v_a_3896_);
if (v___x_3949_ == 0)
{
uint8_t v___x_3950_; 
v___x_3950_ = 1;
v___y_3899_ = v___x_3950_;
goto v___jp_3898_;
}
else
{
uint8_t v___x_3951_; 
v___x_3951_ = 0;
v___y_3899_ = v___x_3951_;
goto v___jp_3898_;
}
v___jp_3898_:
{
lean_object* v___x_3900_; 
lean_inc_ref(v_env_3890_);
v___x_3900_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_3890_, v_val_3894_, v_a_3861_, v_a_3897_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v_a_3902_; lean_object* v_ifTk_3903_; lean_object* v_cond_3904_; lean_object* v_thenTk_3905_; lean_object* v_thenBody_3906_; lean_object* v_elseIfs_3907_; lean_object* v_elseTk_x3f_3908_; lean_object* v_elseBody_x3f_3909_; lean_object* v___x_3910_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
v_a_3902_ = lean_ctor_get(v___x_3900_, 1);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3900_, 2);
v_ifTk_3903_ = lean_ctor_get(v_a_3901_, 0);
lean_inc(v_ifTk_3903_);
v_cond_3904_ = lean_ctor_get(v_a_3901_, 1);
lean_inc_ref(v_cond_3904_);
v_thenTk_3905_ = lean_ctor_get(v_a_3901_, 2);
lean_inc(v_thenTk_3905_);
v_thenBody_3906_ = lean_ctor_get(v_a_3901_, 3);
lean_inc(v_thenBody_3906_);
v_elseIfs_3907_ = lean_ctor_get(v_a_3901_, 4);
lean_inc_ref(v_elseIfs_3907_);
v_elseTk_x3f_3908_ = lean_ctor_get(v_a_3901_, 5);
lean_inc(v_elseTk_x3f_3908_);
v_elseBody_x3f_3909_ = lean_ctor_get(v_a_3901_, 6);
lean_inc(v_elseBody_x3f_3909_);
lean_dec(v_a_3901_);
v___x_3910_ = l_Lean_Fmt_fmt(v_ifTk_3903_, v_a_3861_, v_a_3902_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v_a_3912_; lean_object* v___x_3913_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
v_a_3912_ = lean_ctor_get(v___x_3910_, 1);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3910_, 2);
v___x_3913_ = l_Lean_Fmt_fmt(v_thenTk_3905_, v_a_3861_, v_a_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
v_a_3915_ = lean_ctor_get(v___x_3913_, 1);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3913_, 2);
v___x_3916_ = l_Lean_Fmt_fmt(v_thenBody_3906_, v_a_3861_, v_a_3915_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_a_3918_; size_t v_sz_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
v_a_3918_ = lean_ctor_get(v___x_3916_, 1);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3916_, 2);
v_sz_3919_ = lean_array_size(v_elseIfs_3907_);
v___x_3920_ = ((size_t)0ULL);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_3919_, v___x_3920_, v_elseIfs_3907_, v_a_3861_, v_a_3918_);
if (lean_obj_tag(v___x_3921_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_3908_) == 0)
{
lean_object* v_a_3922_; lean_object* v_a_3923_; lean_object* v___x_3924_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
v_a_3923_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3921_, 2);
v___x_3924_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_3876_ = v___y_3899_;
v___y_3877_ = v_a_3914_;
v___y_3878_ = v_a_3922_;
v___y_3879_ = v_a_3923_;
v___y_3880_ = v_a_3917_;
v___y_3881_ = v_cond_3904_;
v___y_3882_ = v_a_3911_;
v___y_3883_ = v_elseBody_x3f_3909_;
v___y_3884_ = v___x_3924_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3925_; lean_object* v_a_3926_; lean_object* v_val_3927_; lean_object* v___x_3928_; 
v_a_3925_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3925_);
v_a_3926_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3921_, 2);
v_val_3927_ = lean_ctor_get(v_elseTk_x3f_3908_, 0);
lean_inc(v_val_3927_);
lean_dec_ref_known(v_elseTk_x3f_3908_, 1);
v___x_3928_ = l_Lean_Fmt_fmt(v_val_3927_, v_a_3861_, v_a_3926_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v_a_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
v_a_3930_ = lean_ctor_get(v___x_3928_, 1);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3928_, 2);
v___y_3876_ = v___y_3899_;
v___y_3877_ = v_a_3914_;
v___y_3878_ = v_a_3925_;
v___y_3879_ = v_a_3930_;
v___y_3880_ = v_a_3917_;
v___y_3881_ = v_cond_3904_;
v___y_3882_ = v_a_3911_;
v___y_3883_ = v_elseBody_x3f_3909_;
v___y_3884_ = v_a_3929_;
goto v___jp_3875_;
}
else
{
lean_dec(v_a_3925_);
lean_dec(v_a_3917_);
lean_dec(v_a_3914_);
lean_dec(v_a_3911_);
lean_dec(v_elseBody_x3f_3909_);
lean_dec_ref(v_cond_3904_);
return v___x_3928_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_a_3917_);
lean_dec(v_a_3914_);
lean_dec(v_a_3911_);
lean_dec(v_elseBody_x3f_3909_);
lean_dec(v_elseTk_x3f_3908_);
lean_dec_ref(v_cond_3904_);
v_a_3931_ = lean_ctor_get(v___x_3921_, 0);
v_a_3932_ = lean_ctor_get(v___x_3921_, 1);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3921_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_inc(v_a_3931_);
lean_dec(v___x_3921_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3931_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_dec(v_a_3914_);
lean_dec(v_a_3911_);
lean_dec(v_elseBody_x3f_3909_);
lean_dec(v_elseTk_x3f_3908_);
lean_dec_ref(v_elseIfs_3907_);
lean_dec_ref(v_cond_3904_);
return v___x_3916_;
}
}
else
{
lean_dec(v_a_3911_);
lean_dec(v_elseBody_x3f_3909_);
lean_dec(v_elseTk_x3f_3908_);
lean_dec_ref(v_elseIfs_3907_);
lean_dec(v_thenBody_3906_);
lean_dec_ref(v_cond_3904_);
return v___x_3913_;
}
}
else
{
lean_dec(v_elseBody_x3f_3909_);
lean_dec(v_elseTk_x3f_3908_);
lean_dec_ref(v_elseIfs_3907_);
lean_dec(v_thenBody_3906_);
lean_dec(v_thenTk_3905_);
lean_dec_ref(v_cond_3904_);
return v___x_3910_;
}
}
else
{
lean_object* v_a_3940_; lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
v_a_3940_ = lean_ctor_get(v___x_3900_, 0);
v_a_3941_ = lean_ctor_get(v___x_3900_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3900_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_inc(v_a_3940_);
lean_dec(v___x_3900_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3940_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v_val_3894_);
v_a_3952_ = lean_ctor_get(v___x_3895_, 0);
v_a_3953_ = lean_ctor_get(v___x_3895_, 1);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3895_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_inc(v_a_3952_);
lean_dec(v___x_3895_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3952_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_a_3892_);
lean_dec(v_stx_3860_);
v_a_3961_ = lean_ctor_get(v___x_3891_, 1);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; 
v_unused_3970_ = lean_ctor_get(v___x_3891_, 0);
lean_dec(v_unused_3970_);
v___x_3963_ = v___x_3891_;
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3891_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3965_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 1);
lean_ctor_set(v___x_3963_, 0, v___x_3965_);
v___x_3967_ = v___x_3963_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_a_3961_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_stx_3860_);
v_a_3971_ = lean_ctor_get(v___x_3891_, 0);
v_a_3972_ = lean_ctor_get(v___x_3891_, 1);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3891_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_inc(v_a_3971_);
lean_dec(v___x_3891_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3971_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
v___jp_3863_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = l_Lean_Fmt_Layouts_conditional(v___y_3869_, v___y_3868_, v___y_3865_, v___y_3867_, v___y_3866_, v___y_3870_, v___y_3872_, v___y_3864_);
lean_dec_ref(v___y_3866_);
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___y_3871_);
return v___x_3874_;
}
v___jp_3875_:
{
if (lean_obj_tag(v___y_3883_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_3864_ = v___y_3876_;
v___y_3865_ = v___y_3877_;
v___y_3866_ = v___y_3878_;
v___y_3867_ = v___y_3880_;
v___y_3868_ = v___y_3881_;
v___y_3869_ = v___y_3882_;
v___y_3870_ = v___y_3884_;
v___y_3871_ = v___y_3879_;
v___y_3872_ = v___x_3885_;
goto v___jp_3863_;
}
else
{
lean_object* v_val_3886_; lean_object* v___x_3887_; 
v_val_3886_ = lean_ctor_get(v___y_3883_, 0);
lean_inc(v_val_3886_);
lean_dec_ref_known(v___y_3883_, 1);
v___x_3887_ = l_Lean_Fmt_fmt(v_val_3886_, v_a_3861_, v___y_3879_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v_a_3889_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
v_a_3889_ = lean_ctor_get(v___x_3887_, 1);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3887_, 2);
v___y_3864_ = v___y_3876_;
v___y_3865_ = v___y_3877_;
v___y_3866_ = v___y_3878_;
v___y_3867_ = v___y_3880_;
v___y_3868_ = v___y_3881_;
v___y_3869_ = v___y_3882_;
v___y_3870_ = v___y_3884_;
v___y_3871_ = v_a_3889_;
v___y_3872_ = v_a_3888_;
goto v___jp_3863_;
}
else
{
lean_dec_ref(v___y_3884_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v___x_3887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_3980_, lean_object* v_stx_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_Fmt_fmtConditional(v_initialFmt_3980_, v_stx_3981_, v_a_3982_, v_a_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_3985_, lean_object* v_inst_3986_, lean_object* v_a_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_3985_, v_a_3987_, v___y_3988_, v___y_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_3991_, lean_object* v_inst_3992_, lean_object* v_a_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_3991_, v_inst_3992_, v_a_3993_, v___y_3994_, v___y_3995_);
lean_dec_ref(v___y_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_3997_, size_t v_i_3998_, lean_object* v_bs_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
uint8_t v___x_4002_; 
v___x_4002_ = lean_usize_dec_lt(v_i_3998_, v_sz_3997_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v_bs_3999_);
lean_ctor_set(v___x_4003_, 1, v___y_4001_);
return v___x_4003_;
}
else
{
lean_object* v_v_4004_; size_t v_sz_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v_v_4004_ = lean_array_uget_borrowed(v_bs_3999_, v_i_3998_);
v_sz_4005_ = lean_array_size(v_v_4004_);
v___x_4006_ = ((size_t)0ULL);
lean_inc(v_v_4004_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_4005_, v___x_4006_, v_v_4004_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v_bs_x27_4011_; size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
v_a_4009_ = lean_ctor_get(v___x_4007_, 1);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4007_, 2);
v___x_4010_ = lean_unsigned_to_nat(0u);
v_bs_x27_4011_ = lean_array_uset(v_bs_3999_, v_i_3998_, v___x_4010_);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3998_, v___x_4012_);
v___x_4014_ = lean_array_uset(v_bs_x27_4011_, v_i_3998_, v_a_4008_);
v_i_3998_ = v___x_4013_;
v_bs_3999_ = v___x_4014_;
v___y_4001_ = v_a_4009_;
goto _start;
}
else
{
lean_dec_ref(v_bs_3999_);
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4016_, lean_object* v_i_4017_, lean_object* v_bs_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
size_t v_sz_boxed_4021_; size_t v_i_boxed_4022_; lean_object* v_res_4023_; 
v_sz_boxed_4021_ = lean_unbox_usize(v_sz_4016_);
lean_dec(v_sz_4016_);
v_i_boxed_4022_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_res_4023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4021_, v_i_boxed_4022_, v_bs_4018_, v___y_4019_, v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
size_t v_sz_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v_sz_4027_ = lean_array_size(v_bgs_4024_);
v___x_4028_ = ((size_t)0ULL);
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4027_, v___x_4028_, v_bgs_4024_, v_a_4025_, v_a_4026_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref(v_a_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4034_, lean_object* v_rhs_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Fmt_fmt(v_lhs_4034_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
v_a_4040_ = lean_ctor_get(v___x_4038_, 1);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4038_, 2);
v___x_4041_ = l_Lean_Fmt_fmt(v_rhs_4035_, v_a_4036_, v_a_4040_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4057_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_a_4043_ = lean_ctor_get(v___x_4041_, 1);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4045_ = v___x_4041_;
v_isShared_4046_ = v_isSharedCheck_4057_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4057_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4047_ = lean_unsigned_to_nat(2u);
v___x_4048_ = lean_mk_empty_array_with_capacity(v___x_4047_);
v___x_4049_ = lean_array_push(v___x_4048_, v_a_4039_);
v___x_4050_ = lean_array_push(v___x_4049_, v_a_4042_);
v___x_4051_ = 1;
v___x_4052_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4050_, v___x_4051_);
lean_dec_ref(v___x_4050_);
v___x_4053_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4052_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4053_);
v___x_4055_ = v___x_4045_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_a_4043_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
else
{
lean_dec(v_a_4039_);
return v___x_4041_;
}
}
else
{
lean_dec(v_rhs_4035_);
return v___x_4038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4058_, lean_object* v_rhs_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4058_, v_rhs_4059_, v_a_4060_, v_a_4061_);
lean_dec_ref(v_a_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_quantifier_4066_; lean_object* v_binders_4067_; lean_object* v_typeAscriptionTk_x3f_4068_; lean_object* v_type_x3f_4069_; lean_object* v_commaTk_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4182_; 
v_quantifier_4066_ = lean_ctor_get(v_head_4063_, 0);
v_binders_4067_ = lean_ctor_get(v_head_4063_, 1);
v_typeAscriptionTk_x3f_4068_ = lean_ctor_get(v_head_4063_, 2);
v_type_x3f_4069_ = lean_ctor_get(v_head_4063_, 3);
v_commaTk_4070_ = lean_ctor_get(v_head_4063_, 4);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_head_4063_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4072_ = v_head_4063_;
v_isShared_4073_ = v_isSharedCheck_4182_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_commaTk_4070_);
lean_inc(v_type_x3f_4069_);
lean_inc(v_typeAscriptionTk_x3f_4068_);
lean_inc(v_binders_4067_);
lean_inc(v_quantifier_4066_);
lean_dec(v_head_4063_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4182_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_Fmt_fmt(v_quantifier_4066_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v_a_4076_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v_binderGroups_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
v_a_4076_ = lean_ctor_get(v___x_4074_, 1);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4074_, 2);
if (lean_obj_tag(v_binders_4067_) == 0)
{
lean_object* v_group_4142_; lean_object* v___x_4143_; 
v_group_4142_ = lean_ctor_get(v_binders_4067_, 0);
lean_inc_ref(v_group_4142_);
lean_dec_ref_known(v_binders_4067_, 1);
v___x_4143_ = l_Lean_Fmt_fmtBinderGroups(v_group_4142_, v_a_4064_, v_a_4076_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v_a_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
v_a_4145_ = lean_ctor_get(v___x_4143_, 1);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4143_, 2);
v_binderGroups_4125_ = v_a_4144_;
v___y_4126_ = v_a_4064_;
v___y_4127_ = v_a_4145_;
goto v___jp_4124_;
}
else
{
lean_object* v_a_4146_; lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_a_4075_);
lean_del_object(v___x_4072_);
lean_dec(v_commaTk_4070_);
lean_dec(v_type_x3f_4069_);
lean_dec(v_typeAscriptionTk_x3f_4068_);
v_a_4146_ = lean_ctor_get(v___x_4143_, 0);
v_a_4147_ = lean_ctor_get(v___x_4143_, 1);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4143_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_inc(v_a_4146_);
lean_dec(v___x_4143_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4146_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_lhs_4155_; lean_object* v_rhs_4156_; lean_object* v___x_4157_; 
v_lhs_4155_ = lean_ctor_get(v_binders_4067_, 0);
lean_inc(v_lhs_4155_);
v_rhs_4156_ = lean_ctor_get(v_binders_4067_, 1);
lean_inc(v_rhs_4156_);
lean_dec_ref_known(v_binders_4067_, 2);
v___x_4157_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4155_, v_rhs_4156_, v_a_4064_, v_a_4076_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v_a_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
v_a_4159_ = lean_ctor_get(v___x_4157_, 1);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4157_, 2);
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_mk_empty_array_with_capacity(v___x_4160_);
lean_inc_ref(v___x_4161_);
v___x_4162_ = lean_array_push(v___x_4161_, v_a_4158_);
v___x_4163_ = lean_array_push(v___x_4161_, v___x_4162_);
v_binderGroups_4125_ = v___x_4163_;
v___y_4126_ = v_a_4064_;
v___y_4127_ = v_a_4159_;
goto v___jp_4124_;
}
else
{
lean_object* v_a_4164_; lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_a_4075_);
lean_del_object(v___x_4072_);
lean_dec(v_commaTk_4070_);
lean_dec(v_type_x3f_4069_);
lean_dec(v_typeAscriptionTk_x3f_4068_);
v_a_4164_ = lean_ctor_get(v___x_4157_, 0);
v_a_4165_ = lean_ctor_get(v___x_4157_, 1);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4157_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_inc(v_a_4164_);
lean_dec(v___x_4157_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4164_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
v___jp_4077_:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Fmt_fmt(v_commaTk_4070_, v___y_4079_, v___y_4081_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4095_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
v_a_4085_ = lean_ctor_get(v___x_4083_, 1);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4087_ = v___x_4083_;
v_isShared_4088_ = v_isSharedCheck_4095_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_inc(v_a_4084_);
lean_dec(v___x_4083_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4095_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 4, v_a_4084_);
lean_ctor_set(v___x_4072_, 3, v___y_4082_);
lean_ctor_set(v___x_4072_, 2, v___y_4078_);
lean_ctor_set(v___x_4072_, 1, v___y_4080_);
lean_ctor_set(v___x_4072_, 0, v_a_4075_);
v___x_4090_ = v___x_4072_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4075_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___y_4080_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v___y_4078_);
lean_ctor_set(v_reuseFailAlloc_4094_, 3, v___y_4082_);
lean_ctor_set(v_reuseFailAlloc_4094_, 4, v_a_4084_);
v___x_4090_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4092_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4090_);
v___x_4092_ = v___x_4087_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_a_4085_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec_ref(v___y_4082_);
lean_dec_ref(v___y_4080_);
lean_dec_ref(v___y_4078_);
lean_dec(v_a_4075_);
lean_del_object(v___x_4072_);
v_a_4096_ = lean_ctor_get(v___x_4083_, 0);
v_a_4097_ = lean_ctor_get(v___x_4083_, 1);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4083_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_inc(v_a_4096_);
lean_dec(v___x_4083_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4096_);
lean_ctor_set(v_reuseFailAlloc_4103_, 1, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
v___jp_4105_:
{
if (lean_obj_tag(v_type_x3f_4069_) == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4108_;
v___y_4081_ = v___y_4107_;
v___y_4082_ = v___x_4110_;
goto v___jp_4077_;
}
else
{
lean_object* v_val_4111_; lean_object* v___x_4112_; 
v_val_4111_ = lean_ctor_get(v_type_x3f_4069_, 0);
lean_inc(v_val_4111_);
lean_dec_ref_known(v_type_x3f_4069_, 1);
v___x_4112_ = l_Lean_Fmt_fmt(v_val_4111_, v___y_4106_, v___y_4107_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_a_4114_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
v_a_4114_ = lean_ctor_get(v___x_4112_, 1);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4112_, 2);
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4108_;
v___y_4081_ = v_a_4114_;
v___y_4082_ = v_a_4113_;
goto v___jp_4077_;
}
else
{
lean_object* v_a_4115_; lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec_ref(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v_a_4075_);
lean_del_object(v___x_4072_);
lean_dec(v_commaTk_4070_);
v_a_4115_ = lean_ctor_get(v___x_4112_, 0);
v_a_4116_ = lean_ctor_get(v___x_4112_, 1);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4112_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_inc(v_a_4115_);
lean_dec(v___x_4112_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4115_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
v___jp_4124_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4068_) == 0)
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v___y_4108_ = v_binderGroups_4125_;
v___y_4109_ = v___x_4128_;
goto v___jp_4105_;
}
else
{
lean_object* v_val_4129_; lean_object* v___x_4130_; 
v_val_4129_ = lean_ctor_get(v_typeAscriptionTk_x3f_4068_, 0);
lean_inc(v_val_4129_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4068_, 1);
v___x_4130_ = l_Lean_Fmt_fmt(v_val_4129_, v___y_4126_, v___y_4127_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v_a_4132_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
v_a_4132_ = lean_ctor_get(v___x_4130_, 1);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4130_, 2);
v___y_4106_ = v___y_4126_;
v___y_4107_ = v_a_4132_;
v___y_4108_ = v_binderGroups_4125_;
v___y_4109_ = v_a_4131_;
goto v___jp_4105_;
}
else
{
lean_object* v_a_4133_; lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v_binderGroups_4125_);
lean_dec(v_a_4075_);
lean_del_object(v___x_4072_);
lean_dec(v_commaTk_4070_);
lean_dec(v_type_x3f_4069_);
v_a_4133_ = lean_ctor_get(v___x_4130_, 0);
v_a_4134_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4130_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_inc(v_a_4133_);
lean_dec(v___x_4130_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4133_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_del_object(v___x_4072_);
lean_dec(v_commaTk_4070_);
lean_dec(v_type_x3f_4069_);
lean_dec(v_typeAscriptionTk_x3f_4068_);
lean_dec_ref(v_binders_4067_);
v_a_4173_ = lean_ctor_get(v___x_4074_, 0);
v_a_4174_ = lean_ctor_get(v___x_4074_, 1);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4074_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_inc(v_a_4173_);
lean_dec(v___x_4074_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4173_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4183_, v_a_4184_, v_a_4185_);
lean_dec_ref(v_a_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4187_, size_t v_i_4188_, lean_object* v_bs_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = lean_usize_dec_lt(v_i_4188_, v_sz_4187_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v_bs_4189_);
lean_ctor_set(v___x_4193_, 1, v___y_4191_);
return v___x_4193_;
}
else
{
lean_object* v_v_4194_; lean_object* v___x_4195_; 
v_v_4194_ = lean_array_uget_borrowed(v_bs_4189_, v_i_4188_);
lean_inc(v_v_4194_);
v___x_4195_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4194_, v___y_4190_, v___y_4191_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v_a_4197_; lean_object* v___x_4198_; lean_object* v_bs_x27_4199_; size_t v___x_4200_; size_t v___x_4201_; lean_object* v___x_4202_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
v_a_4197_ = lean_ctor_get(v___x_4195_, 1);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4195_, 2);
v___x_4198_ = lean_unsigned_to_nat(0u);
v_bs_x27_4199_ = lean_array_uset(v_bs_4189_, v_i_4188_, v___x_4198_);
v___x_4200_ = ((size_t)1ULL);
v___x_4201_ = lean_usize_add(v_i_4188_, v___x_4200_);
v___x_4202_ = lean_array_uset(v_bs_x27_4199_, v_i_4188_, v_a_4196_);
v_i_4188_ = v___x_4201_;
v_bs_4189_ = v___x_4202_;
v___y_4191_ = v_a_4197_;
goto _start;
}
else
{
lean_object* v_a_4204_; lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_bs_4189_);
v_a_4204_ = lean_ctor_get(v___x_4195_, 0);
v_a_4205_ = lean_ctor_get(v___x_4195_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4195_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_inc(v_a_4204_);
lean_dec(v___x_4195_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4204_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4213_, lean_object* v_i_4214_, lean_object* v_bs_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
size_t v_sz_boxed_4218_; size_t v_i_boxed_4219_; lean_object* v_res_4220_; 
v_sz_boxed_4218_ = lean_unbox_usize(v_sz_4213_);
lean_dec(v_sz_4213_);
v_i_boxed_4219_ = lean_unbox_usize(v_i_4214_);
lean_dec(v_i_4214_);
v_res_4220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4218_, v_i_boxed_4219_, v_bs_4215_, v___y_4216_, v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4221_, lean_object* v_stx_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v_env_4225_; lean_object* v___x_4226_; lean_object* v_quantifiers_4227_; lean_object* v_body_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4264_; 
v_env_4225_ = lean_ctor_get(v_a_4223_, 0);
lean_inc_ref(v_env_4225_);
v___x_4226_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4225_, v_deconstructQuantifier_x3f_4221_, v_stx_4222_);
v_quantifiers_4227_ = lean_ctor_get(v___x_4226_, 0);
v_body_4228_ = lean_ctor_get(v___x_4226_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4230_ = v___x_4226_;
v_isShared_4231_ = v_isSharedCheck_4264_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_body_4228_);
lean_inc(v_quantifiers_4227_);
lean_dec(v___x_4226_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4264_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v___x_4232_ = lean_array_get_size(v_quantifiers_4227_);
v___x_4233_ = lean_unsigned_to_nat(0u);
v___x_4234_ = lean_nat_dec_eq(v___x_4232_, v___x_4233_);
if (v___x_4234_ == 0)
{
size_t v_sz_4235_; size_t v___x_4236_; lean_object* v___x_4237_; 
lean_del_object(v___x_4230_);
v_sz_4235_ = lean_array_size(v_quantifiers_4227_);
v___x_4236_ = ((size_t)0ULL);
v___x_4237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4235_, v___x_4236_, v_quantifiers_4227_, v_a_4223_, v_a_4224_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v_a_4239_; lean_object* v___x_4240_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
v_a_4239_ = lean_ctor_get(v___x_4237_, 1);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4237_, 2);
v___x_4240_ = l_Lean_Fmt_fmt(v_body_4228_, v_a_4223_, v_a_4239_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4250_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_a_4242_ = lean_ctor_get(v___x_4240_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4244_ = v___x_4240_;
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4246_ = l_Lean_Fmt_Layouts_quantified(v_a_4238_, v_a_4241_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4246_);
v___x_4248_ = v___x_4244_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_a_4242_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_dec(v_a_4238_);
return v___x_4240_;
}
}
else
{
lean_object* v_a_4251_; lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_body_4228_);
v_a_4251_ = lean_ctor_get(v___x_4237_, 0);
v_a_4252_ = lean_ctor_get(v___x_4237_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4237_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_inc(v_a_4251_);
lean_dec(v___x_4237_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4251_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_dec(v_body_4228_);
lean_dec_ref(v_quantifiers_4227_);
v___x_4260_ = ((lean_object*)(l_Lean_Fmt_getStxArg_x21___redArg___closed__1));
if (v_isShared_4231_ == 0)
{
lean_ctor_set_tag(v___x_4230_, 1);
lean_ctor_set(v___x_4230_, 1, v_a_4224_);
lean_ctor_set(v___x_4230_, 0, v___x_4260_);
v___x_4262_ = v___x_4230_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_a_4224_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4265_, lean_object* v_stx_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4265_, v_stx_4266_, v_a_4267_, v_a_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
uint8_t v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = 0;
v___x_4274_ = l_Lean_Fmt_fmtRaw(v___x_4273_, v_a_4270_, v_a_4271_, v_a_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_Fmt_fmtAtomic(v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec_ref(v_a_4276_);
return v_res_4278_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4286_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v___x_4285_);
return v___x_4287_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4290_){
_start:
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__2));
v___x_4292_ = lean_name_eq(v_kind_4290_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_box(0);
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4295_);
lean_dec(v_kind_4295_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4297_, lean_object* v_x_4298_, lean_object* v_kind_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4301_, lean_object* v_x_4302_, lean_object* v_kind_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4301_, v_x_4302_, v_kind_4303_);
lean_dec(v_kind_4303_);
lean_dec_ref(v_x_4302_);
lean_dec_ref(v_x_4301_);
return v_res_4304_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4310_){
_start:
{
if (lean_obj_tag(v_x_4310_) == 1)
{
lean_object* v_pre_4311_; lean_object* v_str_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v_pre_4311_ = lean_ctor_get(v_x_4310_, 0);
v_str_4312_ = lean_ctor_get(v_x_4310_, 1);
v___x_4313_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4314_ = lean_string_dec_eq(v_str_4312_, v___x_4313_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4316_ = lean_string_dec_eq(v_str_4312_, v___x_4315_);
if (v___x_4316_ == 0)
{
lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4317_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4318_ = lean_string_dec_eq(v_str_4312_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4319_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4320_ = lean_string_dec_eq(v_str_4312_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4322_ = lean_string_dec_eq(v_str_4312_, v___x_4321_);
if (v___x_4322_ == 0)
{
return v___x_4322_;
}
else
{
if (lean_obj_tag(v_pre_4311_) == 0)
{
return v___x_4322_;
}
else
{
return v___x_4320_;
}
}
}
else
{
return v___x_4320_;
}
}
else
{
return v___x_4318_;
}
}
else
{
return v___x_4316_;
}
}
else
{
return v___x_4314_;
}
}
else
{
uint8_t v___x_4323_; 
v___x_4323_ = 0;
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4324_){
_start:
{
uint8_t v_res_4325_; lean_object* v_r_4326_; 
v_res_4325_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4324_);
lean_dec(v_x_4324_);
v_r_4326_ = lean_box(v_res_4325_);
return v_r_4326_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4333_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4332_);
return v___x_4334_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4337_){
_start:
{
uint8_t v___x_4338_; 
v___x_4338_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_box(0);
return v___x_4339_;
}
else
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4341_);
lean_dec(v_kind_4341_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4343_, lean_object* v_x_4344_, lean_object* v_kind_4345_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v_kind_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4347_, v_x_4348_, v_kind_4349_);
lean_dec(v_kind_4349_);
lean_dec_ref(v_x_4348_);
lean_dec_ref(v_x_4347_);
return v_res_4350_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4362_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set(v___x_4363_, 1, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4372_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
lean_ctor_set(v___x_4373_, 1, v___x_4371_);
return v___x_4373_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4376_, lean_object* v_opts_4377_, lean_object* v_kind_4378_){
_start:
{
lean_object* v___x_4379_; 
lean_inc(v_kind_4378_);
lean_inc_ref(v_env_4376_);
v___x_4379_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4376_, v_opts_4377_, v_kind_4378_);
if (lean_obj_tag(v___x_4379_) == 1)
{
lean_object* v_val_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_kind_4378_);
lean_dec_ref(v_env_4376_);
v_val_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4394_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_val_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4394_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint8_t v_assoc_4384_; lean_object* v_extendedChainKinds_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
v_assoc_4384_ = lean_ctor_get_uint8(v_val_4380_, sizeof(void*)*1);
v_extendedChainKinds_4385_ = lean_ctor_get(v_val_4380_, 0);
lean_inc_ref(v_extendedChainKinds_4385_);
lean_dec(v_val_4380_);
v___x_4386_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4387_ = lean_box(v_assoc_4384_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4387_);
v___x_4389_ = v___x_4382_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 5, 2);
lean_closure_set(v___x_4390_, 0, v___x_4389_);
lean_closure_set(v___x_4390_, 1, v_extendedChainKinds_4385_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4386_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4391_);
return v___x_4392_;
}
}
}
else
{
uint8_t v___x_4395_; 
lean_dec(v___x_4379_);
lean_inc(v_kind_4378_);
lean_inc_ref(v_env_4376_);
v___x_4395_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4376_, v_opts_4377_, v_kind_4378_);
if (v___x_4395_ == 0)
{
uint8_t v___x_4396_; 
v___x_4396_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4376_, v_opts_4377_, v_kind_4378_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_box(0);
return v___x_4397_;
}
else
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4398_;
}
}
else
{
lean_object* v___x_4399_; 
lean_dec(v_kind_4378_);
lean_dec_ref(v_env_4376_);
v___x_4399_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4400_, lean_object* v_opts_4401_, lean_object* v_kind_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4400_, v_opts_4401_, v_kind_4402_);
lean_dec_ref(v_opts_4401_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4404_, lean_object* v_opts_4405_, lean_object* v_kind_4406_){
_start:
{
uint8_t v___x_4407_; 
v___x_4407_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4404_, v_opts_4405_, v_kind_4406_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_box(0);
return v___x_4408_;
}
else
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4410_, lean_object* v_opts_4411_, lean_object* v_kind_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4410_, v_opts_4411_, v_kind_4412_);
lean_dec_ref(v_opts_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4418_; 
lean_inc_ref(v___y_4416_);
v___x_4418_ = lean_apply_3(v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(lean_object* v_op_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
uint8_t v_assoc_4428_; lean_object* v_extendedChainKinds_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v_assoc_4428_ = lean_ctor_get_uint8(v_op_4424_, sizeof(void*)*1);
v_extendedChainKinds_4429_ = lean_ctor_get(v_op_4424_, 0);
lean_inc_ref(v_extendedChainKinds_4429_);
lean_dec_ref(v_op_4424_);
v___x_4430_ = lean_box(v_assoc_4428_);
v___x_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
v___x_4432_ = l_Lean_Fmt_fmtInfixOperator(v___x_4431_, v_extendedChainKinds_4429_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec_ref_known(v___x_4431_, 1);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object* v_op_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(v_op_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec_ref(v___y_4435_);
return v_res_4437_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___f_4439_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_));
v___x_4440_ = l_Lean_Fmt_fmtAttribute;
v___x_4441_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4441_, 0, lean_box(0));
lean_closure_set(v___x_4441_, 1, v___x_4440_);
lean_closure_set(v___x_4441_, 2, v___f_4439_);
return v___x_4441_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___f_4443_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_));
v___x_4444_ = l_Lean_Fmt_infixFmtAttribute;
v___x_4445_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4445_, 0, lean_box(0));
lean_closure_set(v___x_4445_, 1, v___x_4444_);
lean_closure_set(v___x_4445_, 2, v___f_4443_);
return v___x_4445_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_));
v___x_4448_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_4449_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4449_, 0, lean_box(0));
lean_closure_set(v___x_4449_, 1, v___x_4448_);
lean_closure_set(v___x_4449_, 2, v___x_4447_);
return v___x_4449_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_));
v___x_4452_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_4453_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4453_, 0, lean_box(0));
lean_closure_set(v___x_4453_, 1, v___x_4452_);
lean_closure_set(v___x_4453_, 2, v___x_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = lean_unsigned_to_nat(1100u);
v___x_4456_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_4457_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4455_, v___x_4456_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_dec_ref_known(v___x_4457_, 1);
v___x_4458_ = lean_unsigned_to_nat(1000u);
v___x_4459_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_);
v___x_4460_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4458_, v___x_4459_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_dec_ref_known(v___x_4460_, 1);
v___x_4461_ = lean_unsigned_to_nat(900u);
v___x_4462_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_4463_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4461_, v___x_4462_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_dec_ref_known(v___x_4463_, 1);
v___x_4464_ = lean_unsigned_to_nat(800u);
v___x_4465_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_);
v___x_4466_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4464_, v___x_4465_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref_known(v___x_4466_, 1);
v___x_4467_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_);
v___x_4468_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4464_, v___x_4467_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4468_, 1);
v___x_4469_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_);
v___x_4470_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4464_, v___x_4469_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref_known(v___x_4470_, 1);
v___x_4471_ = lean_unsigned_to_nat(600u);
v___x_4472_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_4473_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4471_, v___x_4472_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_dec_ref_known(v___x_4473_, 1);
v___x_4474_ = lean_unsigned_to_nat(400u);
v___x_4475_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_4476_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4474_, v___x_4475_);
return v___x_4476_;
}
else
{
return v___x_4473_;
}
}
else
{
return v___x_4470_;
}
}
else
{
return v___x_4468_;
}
}
else
{
return v___x_4466_;
}
}
else
{
return v___x_4463_;
}
}
else
{
return v___x_4460_;
}
}
else
{
return v___x_4457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2____boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_();
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
if (lean_obj_tag(v_stx_x3f_4479_) == 1)
{
lean_object* v_val_4482_; lean_object* v___x_4483_; 
v_val_4482_ = lean_ctor_get(v_stx_x3f_4479_, 0);
lean_inc(v_val_4482_);
lean_dec_ref_known(v_stx_x3f_4479_, 1);
v___x_4483_ = l_Lean_Fmt_fmt(v_val_4482_, v_a_4480_, v_a_4481_);
return v___x_4483_;
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
lean_dec(v_stx_x3f_4479_);
v___x_4484_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v_a_4481_);
return v___x_4485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_4486_, v_a_4487_, v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_4490_, lean_object* v_formatterName_4491_, lean_object* v_stx_x3f_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
if (lean_obj_tag(v_stx_x3f_4492_) == 1)
{
lean_object* v_val_4495_; lean_object* v___x_4496_; 
v_val_4495_ = lean_ctor_get(v_stx_x3f_4492_, 0);
lean_inc(v_val_4495_);
lean_dec_ref_known(v_stx_x3f_4492_, 1);
v___x_4496_ = l_Lean_Fmt_fmtWith(v_f_4490_, v_formatterName_4491_, v_val_4495_, v_a_4493_, v_a_4494_);
return v___x_4496_;
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec(v_stx_x3f_4492_);
lean_dec(v_formatterName_4491_);
lean_dec_ref(v_f_4490_);
v___x_4497_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v_a_4494_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_4499_, lean_object* v_formatterName_4500_, lean_object* v_stx_x3f_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Fmt_fmtWith_x3f(v_f_4499_, v_formatterName_4500_, v_stx_x3f_4501_, v_a_4502_, v_a_4503_);
lean_dec_ref(v_a_4502_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
size_t v_sz_4508_; size_t v___x_4509_; lean_object* v___x_4510_; 
v_sz_4508_ = lean_array_size(v_array_4505_);
v___x_4509_ = ((size_t)0ULL);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_4508_, v___x_4509_, v_array_4505_, v_a_4506_, v_a_4507_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_Fmt_fmtArray___redArg(v_array_4511_, v_a_4512_, v_a_4513_);
lean_dec_ref(v_a_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_4515_, lean_object* v_array_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Lean_Fmt_fmtArray___redArg(v_array_4516_, v_a_4517_, v_a_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_4520_, lean_object* v_array_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Fmt_fmtArray(v_ks_4520_, v_array_4521_, v_a_4522_, v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_ks_4520_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_4525_, lean_object* v_formatterName_4526_, size_t v_sz_4527_, size_t v_i_4528_, lean_object* v_bs_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
uint8_t v___x_4532_; 
v___x_4532_ = lean_usize_dec_lt(v_i_4528_, v_sz_4527_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; 
lean_dec(v_formatterName_4526_);
lean_dec_ref(v_f_4525_);
v___x_4533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4533_, 0, v_bs_4529_);
lean_ctor_set(v___x_4533_, 1, v___y_4531_);
return v___x_4533_;
}
else
{
lean_object* v_v_4534_; lean_object* v___x_4535_; 
v_v_4534_ = lean_array_uget_borrowed(v_bs_4529_, v_i_4528_);
lean_inc(v_v_4534_);
lean_inc(v_formatterName_4526_);
lean_inc_ref(v_f_4525_);
v___x_4535_ = l_Lean_Fmt_fmtWith(v_f_4525_, v_formatterName_4526_, v_v_4534_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v_bs_x27_4539_; size_t v___x_4540_; size_t v___x_4541_; lean_object* v___x_4542_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
v_a_4537_ = lean_ctor_get(v___x_4535_, 1);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4535_, 2);
v___x_4538_ = lean_unsigned_to_nat(0u);
v_bs_x27_4539_ = lean_array_uset(v_bs_4529_, v_i_4528_, v___x_4538_);
v___x_4540_ = ((size_t)1ULL);
v___x_4541_ = lean_usize_add(v_i_4528_, v___x_4540_);
v___x_4542_ = lean_array_uset(v_bs_x27_4539_, v_i_4528_, v_a_4536_);
v_i_4528_ = v___x_4541_;
v_bs_4529_ = v___x_4542_;
v___y_4531_ = v_a_4537_;
goto _start;
}
else
{
lean_object* v_a_4544_; lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v_bs_4529_);
lean_dec(v_formatterName_4526_);
lean_dec_ref(v_f_4525_);
v_a_4544_ = lean_ctor_get(v___x_4535_, 0);
v_a_4545_ = lean_ctor_get(v___x_4535_, 1);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4535_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_inc(v_a_4544_);
lean_dec(v___x_4535_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4544_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_4553_, lean_object* v_formatterName_4554_, lean_object* v_sz_4555_, lean_object* v_i_4556_, lean_object* v_bs_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
size_t v_sz_boxed_4560_; size_t v_i_boxed_4561_; lean_object* v_res_4562_; 
v_sz_boxed_4560_ = lean_unbox_usize(v_sz_4555_);
lean_dec(v_sz_4555_);
v_i_boxed_4561_ = lean_unbox_usize(v_i_4556_);
lean_dec(v_i_4556_);
v_res_4562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_4553_, v_formatterName_4554_, v_sz_boxed_4560_, v_i_boxed_4561_, v_bs_4557_, v___y_4558_, v___y_4559_);
lean_dec_ref(v___y_4558_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_4563_, lean_object* v_formatterName_4564_, lean_object* v_array_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
size_t v_sz_4568_; size_t v___x_4569_; lean_object* v___x_4570_; 
v_sz_4568_ = lean_array_size(v_array_4565_);
v___x_4569_ = ((size_t)0ULL);
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_4563_, v_formatterName_4564_, v_sz_4568_, v___x_4569_, v_array_4565_, v_a_4566_, v_a_4567_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_4571_, lean_object* v_formatterName_4572_, lean_object* v_array_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_4571_, v_formatterName_4572_, v_array_4573_, v_a_4574_, v_a_4575_);
lean_dec_ref(v_a_4574_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_4577_, lean_object* v_f_4578_, lean_object* v_formatterName_4579_, lean_object* v_array_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_4578_, v_formatterName_4579_, v_array_4580_, v_a_4581_, v_a_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_4584_, lean_object* v_f_4585_, lean_object* v_formatterName_4586_, lean_object* v_array_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_Fmt_fmtArrayWith(v_ks_4584_, v_f_4585_, v_formatterName_4586_, v_array_4587_, v_a_4588_, v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_ks_4584_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
size_t v_sz_4594_; size_t v___x_4595_; lean_object* v___x_4596_; 
v_sz_4594_ = lean_array_size(v_sepArray_4591_);
v___x_4595_ = ((size_t)0ULL);
v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_4594_, v___x_4595_, v_sepArray_4591_, v_a_4592_, v_a_4593_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_a_4598_ = lean_ctor_get(v___x_4596_, 1);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4596_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4597_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4606_ = lean_ctor_get(v___x_4596_, 0);
v_a_4607_ = lean_ctor_get(v___x_4596_, 1);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4596_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_inc(v_a_4606_);
lean_dec(v___x_4596_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4606_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_4615_, v_a_4616_, v_a_4617_);
lean_dec_ref(v_a_4616_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_4619_, lean_object* v_sepArray_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_4620_, v_a_4621_, v_a_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_4624_, lean_object* v_sepArray_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Lean_Fmt_fmtSepArray(v_sep_4624_, v_sepArray_4625_, v_a_4626_, v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec_ref(v_sep_4624_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_4629_, lean_object* v_formatterName_4630_, size_t v_sz_4631_, size_t v_i_4632_, lean_object* v_bs_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_usize_dec_lt(v_i_4632_, v_sz_4631_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
lean_dec(v_formatterName_4630_);
lean_dec_ref(v_f_4629_);
v___x_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4637_, 0, v_bs_4633_);
lean_ctor_set(v___x_4637_, 1, v___y_4635_);
return v___x_4637_;
}
else
{
lean_object* v_v_4638_; lean_object* v___x_4639_; lean_object* v_bs_x27_4640_; lean_object* v___y_4642_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v_v_4638_ = lean_array_uget(v_bs_4633_, v_i_4632_);
v___x_4639_ = lean_unsigned_to_nat(0u);
v_bs_x27_4640_ = lean_array_uset(v_bs_4633_, v_i_4632_, v___x_4639_);
v___x_4658_ = lean_usize_to_nat(v_i_4632_);
v___x_4659_ = lean_unsigned_to_nat(2u);
v___x_4660_ = lean_nat_mod(v___x_4658_, v___x_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_nat_dec_eq(v___x_4660_, v___x_4639_);
lean_dec(v___x_4660_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Lean_Fmt_fmt(v_v_4638_, v___y_4634_, v___y_4635_);
v___y_4642_ = v___x_4662_;
goto v___jp_4641_;
}
else
{
lean_object* v___x_4663_; 
lean_inc(v_formatterName_4630_);
lean_inc_ref(v_f_4629_);
v___x_4663_ = l_Lean_Fmt_fmtWith(v_f_4629_, v_formatterName_4630_, v_v_4638_, v___y_4634_, v___y_4635_);
v___y_4642_ = v___x_4663_;
goto v___jp_4641_;
}
v___jp_4641_:
{
if (lean_obj_tag(v___y_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v_a_4644_; size_t v___x_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
v_a_4643_ = lean_ctor_get(v___y_4642_, 0);
lean_inc(v_a_4643_);
v_a_4644_ = lean_ctor_get(v___y_4642_, 1);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___y_4642_, 2);
v___x_4645_ = ((size_t)1ULL);
v___x_4646_ = lean_usize_add(v_i_4632_, v___x_4645_);
v___x_4647_ = lean_array_uset(v_bs_x27_4640_, v_i_4632_, v_a_4643_);
v_i_4632_ = v___x_4646_;
v_bs_4633_ = v___x_4647_;
v___y_4635_ = v_a_4644_;
goto _start;
}
else
{
lean_object* v_a_4649_; lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec_ref(v_bs_x27_4640_);
lean_dec(v_formatterName_4630_);
lean_dec_ref(v_f_4629_);
v_a_4649_ = lean_ctor_get(v___y_4642_, 0);
v_a_4650_ = lean_ctor_get(v___y_4642_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___y_4642_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___y_4642_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_inc(v_a_4649_);
lean_dec(v___y_4642_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4649_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_4664_, lean_object* v_formatterName_4665_, lean_object* v_sz_4666_, lean_object* v_i_4667_, lean_object* v_bs_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
size_t v_sz_boxed_4671_; size_t v_i_boxed_4672_; lean_object* v_res_4673_; 
v_sz_boxed_4671_ = lean_unbox_usize(v_sz_4666_);
lean_dec(v_sz_4666_);
v_i_boxed_4672_ = lean_unbox_usize(v_i_4667_);
lean_dec(v_i_4667_);
v_res_4673_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_4664_, v_formatterName_4665_, v_sz_boxed_4671_, v_i_boxed_4672_, v_bs_4668_, v___y_4669_, v___y_4670_);
lean_dec_ref(v___y_4669_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_4674_, lean_object* v_formatterName_4675_, lean_object* v_sepArray_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
size_t v_sz_4679_; size_t v___x_4680_; lean_object* v___x_4681_; 
v_sz_4679_ = lean_array_size(v_sepArray_4676_);
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_4674_, v_formatterName_4675_, v_sz_4679_, v___x_4680_, v_sepArray_4676_, v_a_4677_, v_a_4678_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_a_4683_ = lean_ctor_get(v___x_4681_, 1);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4681_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4682_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
else
{
lean_object* v_a_4691_; lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
v_a_4691_ = lean_ctor_get(v___x_4681_, 0);
v_a_4692_ = lean_ctor_get(v___x_4681_, 1);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4681_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_inc(v_a_4691_);
lean_dec(v___x_4681_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4691_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_4700_, lean_object* v_formatterName_4701_, lean_object* v_sepArray_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_4700_, v_formatterName_4701_, v_sepArray_4702_, v_a_4703_, v_a_4704_);
lean_dec_ref(v_a_4703_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_4706_, lean_object* v_f_4707_, lean_object* v_formatterName_4708_, lean_object* v_sepArray_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_4707_, v_formatterName_4708_, v_sepArray_4709_, v_a_4710_, v_a_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_4713_, lean_object* v_f_4714_, lean_object* v_formatterName_4715_, lean_object* v_sepArray_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_4713_, v_f_4714_, v_formatterName_4715_, v_sepArray_4716_, v_a_4717_, v_a_4718_);
lean_dec_ref(v_a_4717_);
lean_dec_ref(v_sep_4713_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_4720_, lean_object* v_formatterName_4721_, lean_object* v_as_4722_, size_t v_sz_4723_, size_t v_i_4724_, lean_object* v_bs_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_4720_, v_formatterName_4721_, v_sz_4723_, v_i_4724_, v_bs_4725_, v___y_4726_, v___y_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_4729_, lean_object* v_formatterName_4730_, lean_object* v_as_4731_, lean_object* v_sz_4732_, lean_object* v_i_4733_, lean_object* v_bs_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
size_t v_sz_boxed_4737_; size_t v_i_boxed_4738_; lean_object* v_res_4739_; 
v_sz_boxed_4737_ = lean_unbox_usize(v_sz_4732_);
lean_dec(v_sz_4732_);
v_i_boxed_4738_ = lean_unbox_usize(v_i_4733_);
lean_dec(v_i_4733_);
v_res_4739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_4729_, v_formatterName_4730_, v_as_4731_, v_sz_boxed_4737_, v_i_boxed_4738_, v_bs_4734_, v___y_4735_, v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v_as_4731_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
size_t v_sz_4743_; size_t v___x_4744_; lean_object* v___x_4745_; 
v_sz_4743_ = lean_array_size(v_sepArray_4740_);
v___x_4744_ = ((size_t)0ULL);
v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__0(v_sz_4743_, v___x_4744_, v_sepArray_4740_, v_a_4741_, v_a_4742_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_a_4747_ = lean_ctor_get(v___x_4745_, 1);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4745_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4746_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
v_a_4755_ = lean_ctor_get(v___x_4745_, 0);
v_a_4756_ = lean_ctor_get(v___x_4745_, 1);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4745_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_inc(v_a_4755_);
lean_dec(v___x_4745_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4755_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_4764_, v_a_4765_, v_a_4766_);
lean_dec_ref(v_a_4765_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_4768_, lean_object* v_sep_4769_, lean_object* v_sepArray_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_4770_, v_a_4771_, v_a_4772_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_4774_, lean_object* v_sep_4775_, lean_object* v_sepArray_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_Fmt_fmtTSepArray(v_ks_4774_, v_sep_4775_, v_sepArray_4776_, v_a_4777_, v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec_ref(v_sep_4775_);
lean_dec(v_ks_4774_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_4780_, lean_object* v_formatterName_4781_, lean_object* v_sepArray_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_){
_start:
{
size_t v_sz_4785_; size_t v___x_4786_; lean_object* v___x_4787_; 
v_sz_4785_ = lean_array_size(v_sepArray_4782_);
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_4780_, v_formatterName_4781_, v_sz_4785_, v___x_4786_, v_sepArray_4782_, v_a_4783_, v_a_4784_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_a_4789_ = lean_ctor_get(v___x_4787_, 1);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4787_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4788_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
else
{
lean_object* v_a_4797_; lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_a_4797_ = lean_ctor_get(v___x_4787_, 0);
v_a_4798_ = lean_ctor_get(v___x_4787_, 1);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4787_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_inc(v_a_4797_);
lean_dec(v___x_4787_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4797_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_4806_, lean_object* v_formatterName_4807_, lean_object* v_sepArray_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_4806_, v_formatterName_4807_, v_sepArray_4808_, v_a_4809_, v_a_4810_);
lean_dec_ref(v_a_4809_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_4812_, lean_object* v_sep_4813_, lean_object* v_f_4814_, lean_object* v_formatterName_4815_, lean_object* v_sepArray_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_4814_, v_formatterName_4815_, v_sepArray_4816_, v_a_4817_, v_a_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_4820_, lean_object* v_sep_4821_, lean_object* v_f_4822_, lean_object* v_formatterName_4823_, lean_object* v_sepArray_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_4820_, v_sep_4821_, v_f_4822_, v_formatterName_4823_, v_sepArray_4824_, v_a_4825_, v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec_ref(v_sep_4821_);
lean_dec(v_ks_4820_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(lean_object* v___x_4828_, lean_object* v___x_4829_, lean_object* v___x_4830_, lean_object* v_a_4831_, lean_object* v_b_4832_){
_start:
{
lean_object* v_startInclusive_4833_; lean_object* v_endExclusive_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_startInclusive_4833_ = lean_ctor_get(v___x_4828_, 1);
v_endExclusive_4834_ = lean_ctor_get(v___x_4828_, 2);
v___x_4835_ = lean_nat_sub(v_endExclusive_4834_, v_startInclusive_4833_);
v___x_4836_ = lean_nat_dec_eq(v_a_4831_, v___x_4835_);
lean_dec(v___x_4835_);
if (v___x_4836_ == 0)
{
uint32_t v___x_4837_; lean_object* v___x_4838_; uint32_t v___x_4839_; uint8_t v___x_4840_; 
v___x_4837_ = 10;
v___x_4838_ = lean_nat_add(v___x_4829_, v_a_4831_);
v___x_4839_ = lean_string_utf8_get_fast(v___x_4830_, v___x_4838_);
v___x_4840_ = lean_uint32_dec_eq(v___x_4839_, v___x_4837_);
if (v___x_4840_ == 0)
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec(v_a_4831_);
v___x_4841_ = lean_string_utf8_next_fast(v___x_4830_, v___x_4838_);
lean_dec(v___x_4838_);
v___x_4842_ = lean_nat_sub(v___x_4841_, v___x_4829_);
v_a_4831_ = v___x_4842_;
goto _start;
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4844_ = lean_string_utf8_next_fast(v___x_4830_, v___x_4838_);
v___x_4845_ = lean_nat_sub(v___x_4844_, v___x_4838_);
lean_dec(v___x_4838_);
v___x_4846_ = lean_nat_add(v_a_4831_, v___x_4845_);
lean_dec(v___x_4845_);
lean_dec(v_a_4831_);
v___x_4847_ = lean_unsigned_to_nat(1u);
v___x_4848_ = lean_nat_add(v_b_4832_, v___x_4847_);
lean_dec(v_b_4832_);
v_a_4831_ = v___x_4846_;
v_b_4832_ = v___x_4848_;
goto _start;
}
}
else
{
lean_dec(v_a_4831_);
return v_b_4832_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v___x_4852_, lean_object* v_a_4853_, lean_object* v_b_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_4850_, v___x_4851_, v___x_4852_, v_a_4853_, v_b_4854_);
lean_dec_ref(v___x_4852_);
lean_dec(v___x_4851_);
lean_dec_ref(v___x_4850_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_4858_, lean_object* v_minNewlines_4859_, lean_object* v_leadingTk_4860_, lean_object* v_leading_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v___y_4865_; lean_object* v___y_4872_; lean_object* v___y_4883_; lean_object* v_str_4885_; lean_object* v_startPos_4886_; lean_object* v_stopPos_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4900_; 
v_str_4885_ = lean_ctor_get(v_leading_4861_, 0);
v_startPos_4886_ = lean_ctor_get(v_leading_4861_, 1);
v_stopPos_4887_ = lean_ctor_get(v_leading_4861_, 2);
v_isSharedCheck_4900_ = !lean_is_exclusive(v_leading_4861_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4889_ = v_leading_4861_;
v_isShared_4890_ = v_isSharedCheck_4900_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_stopPos_4887_);
lean_inc(v_startPos_4886_);
lean_inc(v_str_4885_);
lean_dec(v_leading_4861_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4900_;
goto v_resetjp_4888_;
}
v___jp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v_msg_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4866_ = lean_box(0);
v___x_4867_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v_msg_4868_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_4869_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_4869_, 0, v_leadingTk_4860_);
lean_ctor_set(v___x_4869_, 1, v___x_4866_);
lean_ctor_set(v___x_4869_, 2, v___x_4867_);
lean_ctor_set(v___x_4869_, 3, v_msg_4868_);
v___x_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
lean_ctor_set(v___x_4870_, 1, v___y_4865_);
return v___x_4870_;
}
v___jp_4871_:
{
lean_object* v___x_4873_; lean_object* v_nls_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4873_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_4874_ = lean_mk_array(v___y_4872_, v___x_4873_);
v___x_4875_ = l_Lean_Fmt_TaggedDoc_join(v_nls_4874_);
v___x_4876_ = lean_box(0);
v___x_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_unsigned_to_nat(1u);
v___x_4879_ = lean_mk_empty_array_with_capacity(v___x_4878_);
v___x_4880_ = lean_array_push(v___x_4879_, v___x_4877_);
v___x_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set(v___x_4881_, 1, v___y_4863_);
return v___x_4881_;
}
v___jp_4882_:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_nat_dec_le(v___y_4883_, v_maxNewlines_4858_);
if (v___x_4884_ == 0)
{
lean_dec(v___y_4883_);
v___y_4872_ = v_maxNewlines_4858_;
goto v___jp_4871_;
}
else
{
lean_dec(v_maxNewlines_4858_);
v___y_4872_ = v___y_4883_;
goto v___jp_4871_;
}
}
v_resetjp_4888_:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_string_is_valid_pos(v_str_4885_, v_startPos_4886_);
if (v___x_4891_ == 0)
{
lean_del_object(v___x_4889_);
lean_dec(v_stopPos_4887_);
lean_dec(v_startPos_4886_);
lean_dec_ref(v_str_4885_);
lean_dec(v_minNewlines_4859_);
lean_dec(v_maxNewlines_4858_);
v___y_4865_ = v___y_4863_;
goto v___jp_4864_;
}
else
{
uint8_t v___x_4892_; 
v___x_4892_ = lean_string_is_valid_pos(v_str_4885_, v_stopPos_4887_);
if (v___x_4892_ == 0)
{
lean_del_object(v___x_4889_);
lean_dec(v_stopPos_4887_);
lean_dec(v_startPos_4886_);
lean_dec_ref(v_str_4885_);
lean_dec(v_minNewlines_4859_);
lean_dec(v_maxNewlines_4858_);
v___y_4865_ = v___y_4863_;
goto v___jp_4864_;
}
else
{
uint8_t v___x_4893_; 
v___x_4893_ = lean_nat_dec_le(v_startPos_4886_, v_stopPos_4887_);
if (v___x_4893_ == 0)
{
lean_del_object(v___x_4889_);
lean_dec(v_stopPos_4887_);
lean_dec(v_startPos_4886_);
lean_dec_ref(v_str_4885_);
lean_dec(v_minNewlines_4859_);
lean_dec(v_maxNewlines_4858_);
v___y_4865_ = v___y_4863_;
goto v___jp_4864_;
}
else
{
lean_object* v___x_4895_; 
lean_dec(v_leadingTk_4860_);
lean_inc(v_startPos_4886_);
lean_inc_ref(v_str_4885_);
if (v_isShared_4890_ == 0)
{
v___x_4895_ = v___x_4889_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_str_4885_);
lean_ctor_set(v_reuseFailAlloc_4899_, 1, v_startPos_4886_);
lean_ctor_set(v_reuseFailAlloc_4899_, 2, v_stopPos_4887_);
v___x_4895_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v_searcher_4896_; lean_object* v_numNewlines_4897_; uint8_t v___x_4898_; 
v_searcher_4896_ = lean_unsigned_to_nat(0u);
v_numNewlines_4897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_4895_, v_startPos_4886_, v_str_4885_, v_searcher_4896_, v_searcher_4896_);
lean_dec_ref(v_str_4885_);
lean_dec(v_startPos_4886_);
lean_dec_ref(v___x_4895_);
v___x_4898_ = lean_nat_dec_le(v_numNewlines_4897_, v_minNewlines_4859_);
if (v___x_4898_ == 0)
{
lean_dec(v_minNewlines_4859_);
v___y_4883_ = v_numNewlines_4897_;
goto v___jp_4882_;
}
else
{
lean_dec(v_numNewlines_4897_);
v___y_4883_ = v_minNewlines_4859_;
goto v___jp_4882_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_4901_, lean_object* v_minNewlines_4902_, lean_object* v_leadingTk_4903_, lean_object* v_leading_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_4901_, v_minNewlines_4902_, v_leadingTk_4903_, v_leading_4904_, v___y_4905_, v___y_4906_);
lean_dec_ref(v___y_4905_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_4908_, lean_object* v_minNewlines_4909_, lean_object* v_maxNewlines_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v___f_4913_; lean_object* v___x_4914_; 
v___f_4913_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4913_, 0, v_maxNewlines_4910_);
lean_closure_set(v___f_4913_, 1, v_minNewlines_4909_);
v___x_4914_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_4908_, v___f_4913_, v_a_4911_, v_a_4912_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_4915_, lean_object* v_minNewlines_4916_, lean_object* v_maxNewlines_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_4915_, v_minNewlines_4916_, v_maxNewlines_4917_, v_a_4918_, v_a_4919_);
lean_dec_ref(v_a_4918_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v_inst_4924_, lean_object* v_R_4925_, lean_object* v_a_4926_, lean_object* v_b_4927_, lean_object* v_c_4928_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_4921_, v___x_4922_, v___x_4923_, v_a_4926_, v_b_4927_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_4930_, lean_object* v___x_4931_, lean_object* v___x_4932_, lean_object* v_inst_4933_, lean_object* v_R_4934_, lean_object* v_a_4935_, lean_object* v_b_4936_, lean_object* v_c_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_4930_, v___x_4931_, v___x_4932_, v_inst_4933_, v_R_4934_, v_a_4935_, v_b_4936_, v_c_4937_);
lean_dec_ref(v___x_4932_);
lean_dec(v___x_4931_);
lean_dec_ref(v___x_4930_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_4939_, lean_object* v_minNewlines_4940_, lean_object* v_trailingTk_4941_, lean_object* v_trailing_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v___y_4946_; lean_object* v___y_4953_; lean_object* v___y_4964_; lean_object* v_str_4966_; lean_object* v_startPos_4967_; lean_object* v_stopPos_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4981_; 
v_str_4966_ = lean_ctor_get(v_trailing_4942_, 0);
v_startPos_4967_ = lean_ctor_get(v_trailing_4942_, 1);
v_stopPos_4968_ = lean_ctor_get(v_trailing_4942_, 2);
v_isSharedCheck_4981_ = !lean_is_exclusive(v_trailing_4942_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4970_ = v_trailing_4942_;
v_isShared_4971_ = v_isSharedCheck_4981_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_stopPos_4968_);
lean_inc(v_startPos_4967_);
lean_inc(v_str_4966_);
lean_dec(v_trailing_4942_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4981_;
goto v_resetjp_4969_;
}
v___jp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v_msg_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4947_ = lean_box(0);
v___x_4948_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v_msg_4949_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_4950_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_4950_, 0, v_trailingTk_4941_);
lean_ctor_set(v___x_4950_, 1, v___x_4947_);
lean_ctor_set(v___x_4950_, 2, v___x_4948_);
lean_ctor_set(v___x_4950_, 3, v_msg_4949_);
v___x_4951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
lean_ctor_set(v___x_4951_, 1, v___y_4946_);
return v___x_4951_;
}
v___jp_4952_:
{
lean_object* v___x_4954_; lean_object* v_nls_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4954_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_4955_ = lean_mk_array(v___y_4953_, v___x_4954_);
v___x_4956_ = l_Lean_Fmt_TaggedDoc_join(v_nls_4955_);
v___x_4957_ = lean_box(0);
v___x_4958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = lean_unsigned_to_nat(1u);
v___x_4960_ = lean_mk_empty_array_with_capacity(v___x_4959_);
v___x_4961_ = lean_array_push(v___x_4960_, v___x_4958_);
v___x_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4961_);
lean_ctor_set(v___x_4962_, 1, v___y_4944_);
return v___x_4962_;
}
v___jp_4963_:
{
uint8_t v___x_4965_; 
v___x_4965_ = lean_nat_dec_le(v___y_4964_, v_maxNewlines_4939_);
if (v___x_4965_ == 0)
{
lean_dec(v___y_4964_);
v___y_4953_ = v_maxNewlines_4939_;
goto v___jp_4952_;
}
else
{
lean_dec(v_maxNewlines_4939_);
v___y_4953_ = v___y_4964_;
goto v___jp_4952_;
}
}
v_resetjp_4969_:
{
uint8_t v___x_4972_; 
v___x_4972_ = lean_string_is_valid_pos(v_str_4966_, v_startPos_4967_);
if (v___x_4972_ == 0)
{
lean_del_object(v___x_4970_);
lean_dec(v_stopPos_4968_);
lean_dec(v_startPos_4967_);
lean_dec_ref(v_str_4966_);
lean_dec(v_minNewlines_4940_);
lean_dec(v_maxNewlines_4939_);
v___y_4946_ = v___y_4944_;
goto v___jp_4945_;
}
else
{
uint8_t v___x_4973_; 
v___x_4973_ = lean_string_is_valid_pos(v_str_4966_, v_stopPos_4968_);
if (v___x_4973_ == 0)
{
lean_del_object(v___x_4970_);
lean_dec(v_stopPos_4968_);
lean_dec(v_startPos_4967_);
lean_dec_ref(v_str_4966_);
lean_dec(v_minNewlines_4940_);
lean_dec(v_maxNewlines_4939_);
v___y_4946_ = v___y_4944_;
goto v___jp_4945_;
}
else
{
uint8_t v___x_4974_; 
v___x_4974_ = lean_nat_dec_le(v_startPos_4967_, v_stopPos_4968_);
if (v___x_4974_ == 0)
{
lean_del_object(v___x_4970_);
lean_dec(v_stopPos_4968_);
lean_dec(v_startPos_4967_);
lean_dec_ref(v_str_4966_);
lean_dec(v_minNewlines_4940_);
lean_dec(v_maxNewlines_4939_);
v___y_4946_ = v___y_4944_;
goto v___jp_4945_;
}
else
{
lean_object* v___x_4976_; 
lean_dec(v_trailingTk_4941_);
lean_inc(v_startPos_4967_);
lean_inc_ref(v_str_4966_);
if (v_isShared_4971_ == 0)
{
v___x_4976_ = v___x_4970_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_str_4966_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_startPos_4967_);
lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_stopPos_4968_);
v___x_4976_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v_searcher_4977_; lean_object* v_numNewlines_4978_; uint8_t v___x_4979_; 
v_searcher_4977_ = lean_unsigned_to_nat(0u);
v_numNewlines_4978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_4976_, v_startPos_4967_, v_str_4966_, v_searcher_4977_, v_searcher_4977_);
lean_dec_ref(v_str_4966_);
lean_dec(v_startPos_4967_);
lean_dec_ref(v___x_4976_);
v___x_4979_ = lean_nat_dec_le(v_numNewlines_4978_, v_minNewlines_4940_);
if (v___x_4979_ == 0)
{
lean_dec(v_minNewlines_4940_);
v___y_4964_ = v_numNewlines_4978_;
goto v___jp_4963_;
}
else
{
lean_dec(v_numNewlines_4978_);
v___y_4964_ = v_minNewlines_4940_;
goto v___jp_4963_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_4982_, lean_object* v_minNewlines_4983_, lean_object* v_trailingTk_4984_, lean_object* v_trailing_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_4982_, v_minNewlines_4983_, v_trailingTk_4984_, v_trailing_4985_, v___y_4986_, v___y_4987_);
lean_dec_ref(v___y_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_4989_, lean_object* v_minNewlines_4990_, lean_object* v_maxNewlines_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v___f_4994_; lean_object* v___x_4995_; 
v___f_4994_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4994_, 0, v_maxNewlines_4991_);
lean_closure_set(v___f_4994_, 1, v_minNewlines_4990_);
v___x_4995_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_4989_, v___f_4994_, v_a_4992_, v_a_4993_);
return v___x_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_4996_, lean_object* v_minNewlines_4997_, lean_object* v_maxNewlines_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_4996_, v_minNewlines_4997_, v_maxNewlines_4998_, v_a_4999_, v_a_5000_);
lean_dec_ref(v_a_4999_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_a_5002_, lean_object* v_b_5003_, lean_object* v_trailingDoc_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5007_ = l_Lean_Fmt_TaggedDoc_append(v_a_5002_, v_trailingDoc_5004_);
v___x_5008_ = lean_array_push(v_b_5003_, v___x_5007_);
v___x_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
v___x_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v___y_5006_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_a_5011_, lean_object* v_b_5012_, lean_object* v_trailingDoc_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_a_5011_, v_b_5012_, v_trailingDoc_5013_, v___y_5014_, v___y_5015_);
lean_dec_ref(v___y_5014_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5017_, lean_object* v_stxs_5018_, lean_object* v___x_5019_, lean_object* v_a_5020_, lean_object* v_b_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
uint8_t v___x_5024_; 
v___x_5024_ = lean_nat_dec_lt(v_a_5020_, v_upperBound_5017_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; 
lean_dec(v_a_5020_);
v___x_5025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5025_, 0, v_b_5021_);
lean_ctor_set(v___x_5025_, 1, v___y_5023_);
return v___x_5025_;
}
else
{
lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5026_ = lean_array_fget_borrowed(v_stxs_5018_, v_a_5020_);
lean_inc(v___x_5026_);
v___x_5027_ = l_Lean_Fmt_fmt(v___x_5026_, v___y_5022_, v___y_5023_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v_a_5029_; lean_object* v___x_5030_; lean_object* v___y_5032_; lean_object* v___x_5057_; uint8_t v___x_5058_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
v_a_5029_ = lean_ctor_get(v___x_5027_, 1);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5027_, 2);
v___x_5030_ = lean_unsigned_to_nat(1u);
v___x_5057_ = lean_nat_sub(v___x_5019_, v___x_5030_);
v___x_5058_ = lean_nat_dec_lt(v_a_5020_, v___x_5057_);
lean_dec(v___x_5057_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_a_5028_, v_b_5021_, v___x_5059_, v___y_5022_, v_a_5029_);
v___y_5032_ = v___x_5060_;
goto v___jp_5031_;
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5026_);
v___x_5062_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5026_, v___x_5030_, v___x_5061_, v___y_5022_, v_a_5029_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v_a_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
v_a_5064_ = lean_ctor_get(v___x_5062_, 1);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5062_, 2);
v___x_5065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_a_5028_, v_b_5021_, v_a_5063_, v___y_5022_, v_a_5064_);
v___y_5032_ = v___x_5065_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5066_; lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec(v_a_5028_);
lean_dec_ref(v_b_5021_);
lean_dec(v_a_5020_);
v_a_5066_ = lean_ctor_get(v___x_5062_, 0);
v_a_5067_ = lean_ctor_get(v___x_5062_, 1);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_5062_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_inc(v_a_5066_);
lean_dec(v___x_5062_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5066_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
v___jp_5031_:
{
if (lean_obj_tag(v___y_5032_) == 0)
{
lean_object* v_a_5033_; 
v_a_5033_ = lean_ctor_get(v___y_5032_, 0);
lean_inc(v_a_5033_);
if (lean_obj_tag(v_a_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5042_; 
lean_dec(v_a_5020_);
v_a_5034_ = lean_ctor_get(v___y_5032_, 1);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___y_5032_);
if (v_isSharedCheck_5042_ == 0)
{
lean_object* v_unused_5043_; 
v_unused_5043_ = lean_ctor_get(v___y_5032_, 0);
lean_dec(v_unused_5043_);
v___x_5036_ = v___y_5032_;
v_isShared_5037_ = v_isSharedCheck_5042_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___y_5032_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5042_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v_a_5038_; lean_object* v___x_5040_; 
v_a_5038_ = lean_ctor_get(v_a_5033_, 0);
lean_inc(v_a_5038_);
lean_dec_ref_known(v_a_5033_, 1);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 0, v_a_5038_);
v___x_5040_ = v___x_5036_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5038_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v_a_5034_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
else
{
lean_object* v_a_5044_; lean_object* v_a_5045_; lean_object* v___x_5046_; 
v_a_5044_ = lean_ctor_get(v___y_5032_, 1);
lean_inc(v_a_5044_);
lean_dec_ref_known(v___y_5032_, 2);
v_a_5045_ = lean_ctor_get(v_a_5033_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v_a_5033_, 1);
v___x_5046_ = lean_nat_add(v_a_5020_, v___x_5030_);
lean_dec(v_a_5020_);
v_a_5020_ = v___x_5046_;
v_b_5021_ = v_a_5045_;
v___y_5023_ = v_a_5044_;
goto _start;
}
}
else
{
lean_object* v_a_5048_; lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec(v_a_5020_);
v_a_5048_ = lean_ctor_get(v___y_5032_, 0);
v_a_5049_ = lean_ctor_get(v___y_5032_, 1);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___y_5032_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___y_5032_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_inc(v_a_5048_);
lean_dec(v___y_5032_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5048_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec_ref(v_b_5021_);
lean_dec(v_a_5020_);
v_a_5075_ = lean_ctor_get(v___x_5027_, 0);
v_a_5076_ = lean_ctor_get(v___x_5027_, 1);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5027_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_inc(v_a_5075_);
lean_dec(v___x_5027_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5075_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5084_, lean_object* v_stxs_5085_, lean_object* v___x_5086_, lean_object* v_a_5087_, lean_object* v_b_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5084_, v_stxs_5085_, v___x_5086_, v_a_5087_, v_b_5088_, v___y_5089_, v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec(v___x_5086_);
lean_dec_ref(v_stxs_5085_);
lean_dec(v_upperBound_5084_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; 
v___x_5097_ = lean_array_get_size(v_stxs_5094_);
v___x_5098_ = lean_unsigned_to_nat(1u);
v___x_5099_ = lean_nat_dec_eq(v___x_5097_, v___x_5098_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; lean_object* v_acc_5101_; lean_object* v___x_5102_; 
v___x_5100_ = lean_unsigned_to_nat(0u);
v_acc_5101_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5097_, v_stxs_5094_, v___x_5097_, v___x_5100_, v_acc_5101_, v_a_5095_, v_a_5096_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5112_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
v_a_5104_ = lean_ctor_get(v___x_5102_, 1);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5106_ = v___x_5102_;
v_isShared_5107_ = v_isSharedCheck_5112_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_inc(v_a_5103_);
lean_dec(v___x_5102_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5112_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5108_; lean_object* v___x_5110_; 
v___x_5108_ = l_Lean_Fmt_TaggedDoc_join(v_a_5103_);
if (v_isShared_5107_ == 0)
{
lean_ctor_set(v___x_5106_, 0, v___x_5108_);
v___x_5110_ = v___x_5106_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v_a_5104_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
return v___x_5110_;
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_a_5113_ = lean_ctor_get(v___x_5102_, 0);
v_a_5114_ = lean_ctor_get(v___x_5102_, 1);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5102_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_inc(v_a_5113_);
lean_dec(v___x_5102_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5113_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5122_ = lean_box(0);
v___x_5123_ = lean_unsigned_to_nat(0u);
v___x_5124_ = lean_array_get_borrowed(v___x_5122_, v_stxs_5094_, v___x_5123_);
lean_inc(v___x_5124_);
v___x_5125_ = l_Lean_Fmt_fmt(v___x_5124_, v_a_5095_, v_a_5096_);
return v___x_5125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5126_, v_a_5127_, v_a_5128_);
lean_dec_ref(v_a_5127_);
lean_dec_ref(v_stxs_5126_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5130_, lean_object* v_stxs_5131_, lean_object* v___x_5132_, lean_object* v_inst_5133_, lean_object* v_R_5134_, lean_object* v_a_5135_, lean_object* v_b_5136_, lean_object* v_c_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5130_, v_stxs_5131_, v___x_5132_, v_a_5135_, v_b_5136_, v___y_5138_, v___y_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5141_, lean_object* v_stxs_5142_, lean_object* v___x_5143_, lean_object* v_inst_5144_, lean_object* v_R_5145_, lean_object* v_a_5146_, lean_object* v_b_5147_, lean_object* v_c_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5141_, v_stxs_5142_, v___x_5143_, v_inst_5144_, v_R_5145_, v_a_5146_, v_b_5147_, v_c_5148_, v___y_5149_, v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___x_5143_);
lean_dec_ref(v_stxs_5142_);
lean_dec(v_upperBound_5141_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5152_, lean_object* v_out_5153_, lean_object* v_a_5154_){
_start:
{
lean_object* v___x_5155_; uint8_t v___x_5156_; 
v___x_5155_ = lean_array_get_size(v_comments_5152_);
v___x_5156_ = lean_nat_dec_lt(v_a_5154_, v___x_5155_);
if (v___x_5156_ == 0)
{
return v_a_5154_;
}
else
{
lean_object* v___x_5157_; lean_object* v_originalWhitespaceRange_5158_; lean_object* v_stop_5159_; uint8_t v___x_5160_; 
v___x_5157_ = lean_array_fget_borrowed(v_comments_5152_, v_a_5154_);
v_originalWhitespaceRange_5158_ = lean_ctor_get(v___x_5157_, 1);
v_stop_5159_ = lean_ctor_get(v_originalWhitespaceRange_5158_, 1);
v___x_5160_ = lean_nat_dec_lt(v_out_5153_, v_stop_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = lean_unsigned_to_nat(1u);
v___x_5162_ = lean_nat_add(v_a_5154_, v___x_5161_);
lean_dec(v_a_5154_);
v_a_5154_ = v___x_5162_;
goto _start;
}
else
{
return v_a_5154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5164_, lean_object* v_out_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5164_, v_out_5165_, v_a_5166_);
lean_dec(v_out_5165_);
lean_dec_ref(v_comments_5164_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5168_, lean_object* v_x_5169_){
_start:
{
if (lean_obj_tag(v_x_5169_) == 0)
{
return v_x_5168_;
}
else
{
lean_object* v_key_5170_; lean_object* v_value_5171_; lean_object* v_tail_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5195_; 
v_key_5170_ = lean_ctor_get(v_x_5169_, 0);
v_value_5171_ = lean_ctor_get(v_x_5169_, 1);
v_tail_5172_ = lean_ctor_get(v_x_5169_, 2);
v_isSharedCheck_5195_ = !lean_is_exclusive(v_x_5169_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5174_ = v_x_5169_;
v_isShared_5175_ = v_isSharedCheck_5195_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_tail_5172_);
lean_inc(v_value_5171_);
lean_inc(v_key_5170_);
lean_dec(v_x_5169_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5195_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5176_; uint64_t v___x_5177_; uint64_t v___x_5178_; uint64_t v___x_5179_; uint64_t v_fold_5180_; uint64_t v___x_5181_; uint64_t v___x_5182_; uint64_t v___x_5183_; size_t v___x_5184_; size_t v___x_5185_; size_t v___x_5186_; size_t v___x_5187_; size_t v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5191_; 
v___x_5176_ = lean_array_get_size(v_x_5168_);
v___x_5177_ = lean_uint64_of_nat(v_key_5170_);
v___x_5178_ = 32ULL;
v___x_5179_ = lean_uint64_shift_right(v___x_5177_, v___x_5178_);
v_fold_5180_ = lean_uint64_xor(v___x_5177_, v___x_5179_);
v___x_5181_ = 16ULL;
v___x_5182_ = lean_uint64_shift_right(v_fold_5180_, v___x_5181_);
v___x_5183_ = lean_uint64_xor(v_fold_5180_, v___x_5182_);
v___x_5184_ = lean_uint64_to_usize(v___x_5183_);
v___x_5185_ = lean_usize_of_nat(v___x_5176_);
v___x_5186_ = ((size_t)1ULL);
v___x_5187_ = lean_usize_sub(v___x_5185_, v___x_5186_);
v___x_5188_ = lean_usize_land(v___x_5184_, v___x_5187_);
v___x_5189_ = lean_array_uget_borrowed(v_x_5168_, v___x_5188_);
lean_inc(v___x_5189_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set(v___x_5174_, 2, v___x_5189_);
v___x_5191_ = v___x_5174_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_key_5170_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_value_5171_);
lean_ctor_set(v_reuseFailAlloc_5194_, 2, v___x_5189_);
v___x_5191_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5192_; 
v___x_5192_ = lean_array_uset(v_x_5168_, v___x_5188_, v___x_5191_);
v_x_5168_ = v___x_5192_;
v_x_5169_ = v_tail_5172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5196_, lean_object* v_source_5197_, lean_object* v_target_5198_){
_start:
{
lean_object* v___x_5199_; uint8_t v___x_5200_; 
v___x_5199_ = lean_array_get_size(v_source_5197_);
v___x_5200_ = lean_nat_dec_lt(v_i_5196_, v___x_5199_);
if (v___x_5200_ == 0)
{
lean_dec_ref(v_source_5197_);
lean_dec(v_i_5196_);
return v_target_5198_;
}
else
{
lean_object* v_es_5201_; lean_object* v___x_5202_; lean_object* v_source_5203_; lean_object* v_target_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v_es_5201_ = lean_array_fget(v_source_5197_, v_i_5196_);
v___x_5202_ = lean_box(0);
v_source_5203_ = lean_array_fset(v_source_5197_, v_i_5196_, v___x_5202_);
v_target_5204_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5198_, v_es_5201_);
v___x_5205_ = lean_unsigned_to_nat(1u);
v___x_5206_ = lean_nat_add(v_i_5196_, v___x_5205_);
lean_dec(v_i_5196_);
v_i_5196_ = v___x_5206_;
v_source_5197_ = v_source_5203_;
v_target_5198_ = v_target_5204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5208_){
_start:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v_nbuckets_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5209_ = lean_array_get_size(v_data_5208_);
v___x_5210_ = lean_unsigned_to_nat(2u);
v_nbuckets_5211_ = lean_nat_mul(v___x_5209_, v___x_5210_);
v___x_5212_ = lean_unsigned_to_nat(0u);
v___x_5213_ = lean_box(0);
v___x_5214_ = lean_mk_array(v_nbuckets_5211_, v___x_5213_);
v___x_5215_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5212_, v_data_5208_, v___x_5214_);
return v___x_5215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5216_, lean_object* v_x_5217_){
_start:
{
if (lean_obj_tag(v_x_5217_) == 0)
{
uint8_t v___x_5218_; 
v___x_5218_ = 0;
return v___x_5218_;
}
else
{
lean_object* v_key_5219_; lean_object* v_tail_5220_; uint8_t v___x_5221_; 
v_key_5219_ = lean_ctor_get(v_x_5217_, 0);
v_tail_5220_ = lean_ctor_get(v_x_5217_, 2);
v___x_5221_ = lean_nat_dec_eq(v_key_5219_, v_a_5216_);
if (v___x_5221_ == 0)
{
v_x_5217_ = v_tail_5220_;
goto _start;
}
else
{
return v___x_5221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5223_, lean_object* v_x_5224_){
_start:
{
uint8_t v_res_5225_; lean_object* v_r_5226_; 
v_res_5225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5223_, v_x_5224_);
lean_dec(v_x_5224_);
lean_dec(v_a_5223_);
v_r_5226_ = lean_box(v_res_5225_);
return v_r_5226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5229_){
_start:
{
if (lean_obj_tag(v_x_5229_) == 0)
{
lean_object* v___x_5230_; 
v___x_5230_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5230_;
}
else
{
lean_object* v_val_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5240_; 
v_val_5231_ = lean_ctor_get(v_x_5229_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_x_5229_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5233_ = v_x_5229_;
v_isShared_5234_ = v_isSharedCheck_5240_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_val_5231_);
lean_dec(v_x_5229_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5240_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5238_; 
v___x_5235_ = lean_unsigned_to_nat(1u);
v___x_5236_ = lean_nat_add(v_val_5231_, v___x_5235_);
lean_dec(v_val_5231_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5236_);
v___x_5238_ = v___x_5233_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5241_ = lean_box(0);
v___x_5242_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5243_, lean_object* v_x_5244_){
_start:
{
if (lean_obj_tag(v_x_5244_) == 0)
{
lean_object* v___x_5245_; lean_object* v_val_5246_; lean_object* v___x_5247_; 
v___x_5245_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_val_5246_);
v___x_5247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5247_, 0, v_a_5243_);
lean_ctor_set(v___x_5247_, 1, v_val_5246_);
lean_ctor_set(v___x_5247_, 2, v_x_5244_);
return v___x_5247_;
}
else
{
lean_object* v_key_5248_; lean_object* v_value_5249_; lean_object* v_tail_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5265_; 
v_key_5248_ = lean_ctor_get(v_x_5244_, 0);
v_value_5249_ = lean_ctor_get(v_x_5244_, 1);
v_tail_5250_ = lean_ctor_get(v_x_5244_, 2);
v_isSharedCheck_5265_ = !lean_is_exclusive(v_x_5244_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5252_ = v_x_5244_;
v_isShared_5253_ = v_isSharedCheck_5265_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_tail_5250_);
lean_inc(v_value_5249_);
lean_inc(v_key_5248_);
lean_dec(v_x_5244_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5265_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
uint8_t v___x_5254_; 
v___x_5254_ = lean_nat_dec_eq(v_key_5248_, v_a_5243_);
if (v___x_5254_ == 0)
{
lean_object* v_tail_5255_; lean_object* v___x_5257_; 
v_tail_5255_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5243_, v_tail_5250_);
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 2, v_tail_5255_);
v___x_5257_ = v___x_5252_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_key_5248_);
lean_ctor_set(v_reuseFailAlloc_5258_, 1, v_value_5249_);
lean_ctor_set(v_reuseFailAlloc_5258_, 2, v_tail_5255_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v_val_5261_; lean_object* v___x_5263_; 
lean_dec(v_key_5248_);
v___x_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5259_, 0, v_value_5249_);
v___x_5260_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5259_);
v_val_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_val_5261_);
lean_dec(v___x_5260_);
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 1, v_val_5261_);
lean_ctor_set(v___x_5252_, 0, v_a_5243_);
v___x_5263_ = v___x_5252_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5243_);
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v_val_5261_);
lean_ctor_set(v_reuseFailAlloc_5264_, 2, v_tail_5250_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v_size_5268_; lean_object* v_buckets_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5317_; 
v_size_5268_ = lean_ctor_get(v_m_5266_, 0);
v_buckets_5269_ = lean_ctor_get(v_m_5266_, 1);
v_isSharedCheck_5317_ = !lean_is_exclusive(v_m_5266_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5271_ = v_m_5266_;
v_isShared_5272_ = v_isSharedCheck_5317_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_buckets_5269_);
lean_inc(v_size_5268_);
lean_dec(v_m_5266_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5317_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; uint64_t v___x_5274_; uint64_t v___x_5275_; uint64_t v___x_5276_; uint64_t v_fold_5277_; uint64_t v___x_5278_; uint64_t v___x_5279_; uint64_t v___x_5280_; size_t v___x_5281_; size_t v___x_5282_; size_t v___x_5283_; size_t v___x_5284_; size_t v___x_5285_; lean_object* v_bkt_5286_; uint8_t v___x_5287_; 
v___x_5273_ = lean_array_get_size(v_buckets_5269_);
v___x_5274_ = lean_uint64_of_nat(v_a_5267_);
v___x_5275_ = 32ULL;
v___x_5276_ = lean_uint64_shift_right(v___x_5274_, v___x_5275_);
v_fold_5277_ = lean_uint64_xor(v___x_5274_, v___x_5276_);
v___x_5278_ = 16ULL;
v___x_5279_ = lean_uint64_shift_right(v_fold_5277_, v___x_5278_);
v___x_5280_ = lean_uint64_xor(v_fold_5277_, v___x_5279_);
v___x_5281_ = lean_uint64_to_usize(v___x_5280_);
v___x_5282_ = lean_usize_of_nat(v___x_5273_);
v___x_5283_ = ((size_t)1ULL);
v___x_5284_ = lean_usize_sub(v___x_5282_, v___x_5283_);
v___x_5285_ = lean_usize_land(v___x_5281_, v___x_5284_);
v_bkt_5286_ = lean_array_uget_borrowed(v_buckets_5269_, v___x_5285_);
v___x_5287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5267_, v_bkt_5286_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; lean_object* v_size_x27_5289_; lean_object* v___x_5290_; lean_object* v_buckets_x27_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; 
v___x_5288_ = lean_unsigned_to_nat(1u);
v_size_x27_5289_ = lean_nat_add(v_size_5268_, v___x_5288_);
lean_dec(v_size_5268_);
lean_inc(v_bkt_5286_);
v___x_5290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5290_, 0, v_a_5267_);
lean_ctor_set(v___x_5290_, 1, v___x_5288_);
lean_ctor_set(v___x_5290_, 2, v_bkt_5286_);
v_buckets_x27_5291_ = lean_array_uset(v_buckets_5269_, v___x_5285_, v___x_5290_);
v___x_5292_ = lean_unsigned_to_nat(4u);
v___x_5293_ = lean_nat_mul(v_size_x27_5289_, v___x_5292_);
v___x_5294_ = lean_unsigned_to_nat(3u);
v___x_5295_ = lean_nat_div(v___x_5293_, v___x_5294_);
lean_dec(v___x_5293_);
v___x_5296_ = lean_array_get_size(v_buckets_x27_5291_);
v___x_5297_ = lean_nat_dec_le(v___x_5295_, v___x_5296_);
lean_dec(v___x_5295_);
if (v___x_5297_ == 0)
{
lean_object* v_val_5298_; lean_object* v___x_5300_; 
v_val_5298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5291_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 1, v_val_5298_);
lean_ctor_set(v___x_5271_, 0, v_size_x27_5289_);
v___x_5300_ = v___x_5271_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_size_x27_5289_);
lean_ctor_set(v_reuseFailAlloc_5301_, 1, v_val_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
else
{
lean_object* v___x_5303_; 
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 1, v_buckets_x27_5291_);
lean_ctor_set(v___x_5271_, 0, v_size_x27_5289_);
v___x_5303_ = v___x_5271_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_size_x27_5289_);
lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_buckets_x27_5291_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
else
{
lean_object* v___x_5305_; lean_object* v_buckets_x27_5306_; lean_object* v_bkt_x27_5307_; lean_object* v___y_5309_; uint8_t v___x_5314_; 
lean_inc(v_bkt_5286_);
v___x_5305_ = lean_box(0);
v_buckets_x27_5306_ = lean_array_uset(v_buckets_5269_, v___x_5285_, v___x_5305_);
lean_inc(v_a_5267_);
v_bkt_x27_5307_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5267_, v_bkt_5286_);
v___x_5314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5267_, v_bkt_x27_5307_);
lean_dec(v_a_5267_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5315_ = lean_unsigned_to_nat(1u);
v___x_5316_ = lean_nat_sub(v_size_5268_, v___x_5315_);
lean_dec(v_size_5268_);
v___y_5309_ = v___x_5316_;
goto v___jp_5308_;
}
else
{
v___y_5309_ = v_size_5268_;
goto v___jp_5308_;
}
v___jp_5308_:
{
lean_object* v___x_5310_; lean_object* v___x_5312_; 
v___x_5310_ = lean_array_uset(v_buckets_x27_5306_, v___x_5285_, v_bkt_x27_5307_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 1, v___x_5310_);
lean_ctor_set(v___x_5271_, 0, v___y_5309_);
v___x_5312_ = v___x_5271_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___y_5309_);
lean_ctor_set(v_reuseFailAlloc_5313_, 1, v___x_5310_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5318_, lean_object* v___x_5319_, lean_object* v_____r_5320_){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
lean_inc(v___x_5319_);
v___x_5321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5318_, v___x_5319_);
v___x_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5321_);
lean_ctor_set(v___x_5322_, 1, v___x_5319_);
v___x_5323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5322_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5324_, lean_object* v_whitespace_5325_, lean_object* v_a_5326_, lean_object* v_b_5327_){
_start:
{
lean_object* v_str_5328_; lean_object* v_startInclusive_5329_; lean_object* v_endExclusive_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; 
v_str_5328_ = lean_ctor_get(v_whitespace_5325_, 0);
v_startInclusive_5329_ = lean_ctor_get(v_whitespace_5325_, 1);
v_endExclusive_5330_ = lean_ctor_get(v_whitespace_5325_, 2);
v___x_5331_ = lean_nat_sub(v_endExclusive_5330_, v_startInclusive_5329_);
v___x_5332_ = lean_nat_dec_eq(v_a_5326_, v___x_5331_);
lean_dec(v___x_5331_);
if (v___x_5332_ == 0)
{
uint32_t v___x_5333_; lean_object* v___x_5334_; uint32_t v___x_5335_; uint8_t v___x_5336_; 
v___x_5333_ = 10;
v___x_5334_ = lean_nat_add(v_startInclusive_5329_, v_a_5326_);
v___x_5335_ = lean_string_utf8_get_fast(v_str_5328_, v___x_5334_);
v___x_5336_ = lean_uint32_dec_eq(v___x_5335_, v___x_5333_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
lean_dec(v_a_5326_);
v___x_5337_ = lean_string_utf8_next_fast(v_str_5328_, v___x_5334_);
lean_dec(v___x_5334_);
v___x_5338_ = lean_nat_sub(v___x_5337_, v_startInclusive_5329_);
v_a_5326_ = v___x_5338_;
goto _start;
}
else
{
lean_object* v_fst_5340_; lean_object* v_snd_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5367_; 
v_fst_5340_ = lean_ctor_get(v_b_5327_, 0);
v_snd_5341_ = lean_ctor_get(v_b_5327_, 1);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_b_5327_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5343_ = v_b_5327_;
v_isShared_5344_ = v_isSharedCheck_5367_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_snd_5341_);
lean_inc(v_fst_5340_);
lean_dec(v_b_5327_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5367_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v_val_5349_; lean_object* v___x_5353_; lean_object* v___x_5354_; uint8_t v___x_5355_; 
v___x_5345_ = lean_string_utf8_next_fast(v_str_5328_, v___x_5334_);
v___x_5346_ = lean_nat_sub(v___x_5345_, v___x_5334_);
v___x_5347_ = lean_nat_add(v_a_5326_, v___x_5346_);
lean_dec(v___x_5346_);
lean_dec(v_a_5326_);
v___x_5353_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5324_, v___x_5334_, v_snd_5341_);
v___x_5354_ = lean_array_get_size(v_comments_5324_);
v___x_5355_ = lean_nat_dec_lt(v___x_5353_, v___x_5354_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
lean_del_object(v___x_5343_);
lean_dec(v___x_5334_);
v___x_5356_ = lean_box(0);
v___x_5357_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5340_, v___x_5353_, v___x_5356_);
v_val_5349_ = v___x_5357_;
goto v___jp_5348_;
}
else
{
lean_object* v___x_5358_; lean_object* v_originalWhitespaceRange_5359_; uint8_t v___x_5360_; 
v___x_5358_ = lean_array_fget_borrowed(v_comments_5324_, v___x_5353_);
v_originalWhitespaceRange_5359_ = lean_ctor_get(v___x_5358_, 1);
v___x_5360_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_5359_, v___x_5334_, v___x_5332_);
lean_dec(v___x_5334_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_del_object(v___x_5343_);
v___x_5361_ = lean_box(0);
v___x_5362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5340_, v___x_5353_, v___x_5361_);
v_val_5349_ = v___x_5362_;
goto v___jp_5348_;
}
else
{
lean_object* v___x_5364_; 
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 1, v___x_5353_);
v___x_5364_ = v___x_5343_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_fst_5340_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___x_5353_);
v___x_5364_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
v_a_5326_ = v___x_5347_;
v_b_5327_ = v___x_5364_;
goto _start;
}
}
}
v___jp_5348_:
{
if (lean_obj_tag(v_val_5349_) == 0)
{
lean_object* v_a_5350_; 
lean_dec(v___x_5347_);
v_a_5350_ = lean_ctor_get(v_val_5349_, 0);
lean_inc(v_a_5350_);
lean_dec_ref_known(v_val_5349_, 1);
return v_a_5350_;
}
else
{
lean_object* v_a_5351_; 
v_a_5351_ = lean_ctor_get(v_val_5349_, 0);
lean_inc(v_a_5351_);
lean_dec_ref_known(v_val_5349_, 1);
v_a_5326_ = v___x_5347_;
v_b_5327_ = v_a_5351_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5326_);
return v_b_5327_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_5368_, lean_object* v_whitespace_5369_, lean_object* v_a_5370_, lean_object* v_b_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5368_, v_whitespace_5369_, v_a_5370_, v_b_5371_);
lean_dec_ref(v_whitespace_5369_);
lean_dec_ref(v_comments_5368_);
return v_res_5372_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5373_ = lean_box(0);
v___x_5374_ = lean_unsigned_to_nat(16u);
v___x_5375_ = lean_mk_array(v___x_5374_, v___x_5373_);
return v___x_5375_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_5376_; lean_object* v_newlinePositions_5377_; lean_object* v_newlinesBeforeComment_5378_; 
v___x_5376_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_5377_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_5378_, 0, v_newlinePositions_5377_);
lean_ctor_set(v_newlinesBeforeComment_5378_, 1, v___x_5376_);
return v_newlinesBeforeComment_5378_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_5379_; lean_object* v_newlinesBeforeComment_5380_; lean_object* v___x_5381_; 
v_newlinePositions_5379_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5380_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_5381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5381_, 0, v_newlinesBeforeComment_5380_);
lean_ctor_set(v___x_5381_, 1, v_newlinePositions_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_5382_, lean_object* v_whitespace_5383_){
_start:
{
lean_object* v_newlinePositions_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v_fst_5387_; 
v_newlinePositions_5384_ = lean_unsigned_to_nat(0u);
v___x_5385_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_5386_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5382_, v_whitespace_5383_, v_newlinePositions_5384_, v___x_5385_);
v_fst_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_fst_5387_);
lean_dec_ref(v___x_5386_);
return v_fst_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_5388_, lean_object* v_whitespace_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_5388_, v_whitespace_5389_);
lean_dec_ref(v_whitespace_5389_);
lean_dec_ref(v_comments_5388_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_5391_, lean_object* v_out_5392_, lean_object* v_inst_5393_, lean_object* v_a_5394_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5391_, v_out_5392_, v_a_5394_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_5396_, lean_object* v_out_5397_, lean_object* v_inst_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_5396_, v_out_5397_, v_inst_5398_, v_a_5399_);
lean_dec(v_out_5397_);
lean_dec_ref(v_comments_5396_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_5401_, lean_object* v_whitespace_5402_, lean_object* v_inst_5403_, lean_object* v_R_5404_, lean_object* v_a_5405_, lean_object* v_b_5406_, lean_object* v_c_5407_){
_start:
{
lean_object* v___x_5408_; 
v___x_5408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5401_, v_whitespace_5402_, v_a_5405_, v_b_5406_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_5409_, lean_object* v_whitespace_5410_, lean_object* v_inst_5411_, lean_object* v_R_5412_, lean_object* v_a_5413_, lean_object* v_b_5414_, lean_object* v_c_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_5409_, v_whitespace_5410_, v_inst_5411_, v_R_5412_, v_a_5413_, v_b_5414_, v_c_5415_);
lean_dec_ref(v_whitespace_5410_);
lean_dec_ref(v_comments_5409_);
return v_res_5416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_5417_, lean_object* v_a_5418_, lean_object* v_x_5419_){
_start:
{
uint8_t v___x_5420_; 
v___x_5420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5418_, v_x_5419_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5421_, lean_object* v_a_5422_, lean_object* v_x_5423_){
_start:
{
uint8_t v_res_5424_; lean_object* v_r_5425_; 
v_res_5424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_5421_, v_a_5422_, v_x_5423_);
lean_dec(v_x_5423_);
lean_dec(v_a_5422_);
v_r_5425_ = lean_box(v_res_5424_);
return v_r_5425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_5426_, lean_object* v_data_5427_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_5427_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5429_, lean_object* v_i_5430_, lean_object* v_source_5431_, lean_object* v_target_5432_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_5430_, v_source_5431_, v_target_5432_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5434_, lean_object* v_x_5435_, lean_object* v_x_5436_){
_start:
{
lean_object* v___x_5437_; 
v___x_5437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_5435_, v_x_5436_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_5440_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0));
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_5442_);
lean_dec_ref(v_s_5442_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_as_5444_, size_t v_i_5445_, size_t v_stop_5446_, lean_object* v_b_5447_){
_start:
{
lean_object* v___y_5449_; uint8_t v___x_5453_; 
v___x_5453_ = lean_usize_dec_eq(v_i_5445_, v_stop_5446_);
if (v___x_5453_ == 0)
{
lean_object* v___x_5454_; uint8_t v_placement_5455_; 
v___x_5454_ = lean_array_uget_borrowed(v_as_5444_, v_i_5445_);
v_placement_5455_ = lean_ctor_get_uint8(v___x_5454_, sizeof(void*)*3 + 1);
if (v_placement_5455_ == 0)
{
v___y_5449_ = v_b_5447_;
goto v___jp_5448_;
}
else
{
lean_object* v___x_5456_; 
lean_inc(v___x_5454_);
v___x_5456_ = lean_array_push(v_b_5447_, v___x_5454_);
v___y_5449_ = v___x_5456_;
goto v___jp_5448_;
}
}
else
{
return v_b_5447_;
}
v___jp_5448_:
{
size_t v___x_5450_; size_t v___x_5451_; 
v___x_5450_ = ((size_t)1ULL);
v___x_5451_ = lean_usize_add(v_i_5445_, v___x_5450_);
v_i_5445_ = v___x_5451_;
v_b_5447_ = v___y_5449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_as_5457_, lean_object* v_i_5458_, lean_object* v_stop_5459_, lean_object* v_b_5460_){
_start:
{
size_t v_i_boxed_5461_; size_t v_stop_boxed_5462_; lean_object* v_res_5463_; 
v_i_boxed_5461_ = lean_unbox_usize(v_i_5458_);
lean_dec(v_i_5458_);
v_stop_boxed_5462_ = lean_unbox_usize(v_stop_5459_);
lean_dec(v_stop_5459_);
v_res_5463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_as_5457_, v_i_boxed_5461_, v_stop_boxed_5462_, v_b_5460_);
lean_dec_ref(v_as_5457_);
return v_res_5463_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5464_ = lean_box(0);
v___x_5465_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_5466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5465_);
lean_ctor_set(v___x_5466_, 1, v___x_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_5467_, lean_object* v_a_5468_, lean_object* v_b_5469_){
_start:
{
uint8_t v___x_5470_; 
v___x_5470_ = lean_nat_dec_lt(v_a_5468_, v_upperBound_5467_);
if (v___x_5470_ == 0)
{
lean_dec(v_a_5468_);
return v_b_5469_;
}
else
{
lean_object* v_fst_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5484_; 
v_fst_5471_ = lean_ctor_get(v_b_5469_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v_b_5469_);
if (v_isSharedCheck_5484_ == 0)
{
lean_object* v_unused_5485_; 
v_unused_5485_ = lean_ctor_get(v_b_5469_, 1);
lean_dec(v_unused_5485_);
v___x_5473_ = v_b_5469_;
v_isShared_5474_ = v_isSharedCheck_5484_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_fst_5471_);
lean_dec(v_b_5469_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5484_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5479_; 
v___x_5475_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_5476_ = lean_array_push(v_fst_5471_, v___x_5475_);
v___x_5477_ = lean_box(v___x_5470_);
if (v_isShared_5474_ == 0)
{
lean_ctor_set(v___x_5473_, 1, v___x_5477_);
lean_ctor_set(v___x_5473_, 0, v___x_5476_);
v___x_5479_ = v___x_5473_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5480_ = lean_unsigned_to_nat(1u);
v___x_5481_ = lean_nat_add(v_a_5468_, v___x_5480_);
lean_dec(v_a_5468_);
v_a_5468_ = v___x_5481_;
v_b_5469_ = v___x_5479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_5486_, lean_object* v_a_5487_, lean_object* v_b_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_5486_, v_a_5487_, v_b_5488_);
lean_dec(v_upperBound_5486_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_5490_, size_t v_i_5491_, lean_object* v_bs_5492_){
_start:
{
uint8_t v___x_5493_; 
v___x_5493_ = lean_usize_dec_lt(v_i_5491_, v_sz_5490_);
if (v___x_5493_ == 0)
{
return v_bs_5492_;
}
else
{
lean_object* v_v_5494_; lean_object* v_rendered_5495_; lean_object* v___x_5496_; lean_object* v_bs_x27_5497_; size_t v___x_5498_; size_t v___x_5499_; lean_object* v___x_5500_; 
v_v_5494_ = lean_array_uget_borrowed(v_bs_5492_, v_i_5491_);
v_rendered_5495_ = lean_ctor_get(v_v_5494_, 0);
lean_inc_ref(v_rendered_5495_);
v___x_5496_ = lean_unsigned_to_nat(0u);
v_bs_x27_5497_ = lean_array_uset(v_bs_5492_, v_i_5491_, v___x_5496_);
v___x_5498_ = ((size_t)1ULL);
v___x_5499_ = lean_usize_add(v_i_5491_, v___x_5498_);
v___x_5500_ = lean_array_uset(v_bs_x27_5497_, v_i_5491_, v_rendered_5495_);
v_i_5491_ = v___x_5499_;
v_bs_5492_ = v___x_5500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_5502_, lean_object* v_i_5503_, lean_object* v_bs_5504_){
_start:
{
size_t v_sz_boxed_5505_; size_t v_i_boxed_5506_; lean_object* v_res_5507_; 
v_sz_boxed_5505_ = lean_unbox_usize(v_sz_5502_);
lean_dec(v_sz_5502_);
v_i_boxed_5506_ = lean_unbox_usize(v_i_5503_);
lean_dec(v_i_5503_);
v_res_5507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_5505_, v_i_boxed_5506_, v_bs_5504_);
return v_res_5507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_x_5508_, lean_object* v___x_5509_, lean_object* v___x_5510_, lean_object* v_a_5511_, lean_object* v_b_5512_){
_start:
{
lean_object* v_it_5514_; lean_object* v_startInclusive_5515_; lean_object* v_endExclusive_5516_; 
if (lean_obj_tag(v_a_5511_) == 0)
{
lean_object* v_currPos_5522_; lean_object* v_searcher_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5549_; 
v_currPos_5522_ = lean_ctor_get(v_a_5511_, 0);
v_searcher_5523_ = lean_ctor_get(v_a_5511_, 1);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_a_5511_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5525_ = v_a_5511_;
v_isShared_5526_ = v_isSharedCheck_5549_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_searcher_5523_);
lean_inc(v_currPos_5522_);
lean_dec(v_a_5511_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5549_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v_startInclusive_5527_; lean_object* v_endExclusive_5528_; lean_object* v___x_5529_; uint8_t v___x_5530_; 
v_startInclusive_5527_ = lean_ctor_get(v___x_5509_, 1);
v_endExclusive_5528_ = lean_ctor_get(v___x_5509_, 2);
v___x_5529_ = lean_nat_sub(v_endExclusive_5528_, v_startInclusive_5527_);
v___x_5530_ = lean_nat_dec_eq(v_searcher_5523_, v___x_5529_);
lean_dec(v___x_5529_);
if (v___x_5530_ == 0)
{
uint32_t v___x_5531_; uint32_t v___x_5532_; uint8_t v___x_5533_; 
v___x_5531_ = 10;
v___x_5532_ = lean_string_utf8_get_fast(v_x_5508_, v_searcher_5523_);
v___x_5533_ = lean_uint32_dec_eq(v___x_5532_, v___x_5531_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; lean_object* v___x_5536_; 
v___x_5534_ = lean_string_utf8_next_fast(v_x_5508_, v_searcher_5523_);
lean_dec(v_searcher_5523_);
if (v_isShared_5526_ == 0)
{
lean_ctor_set(v___x_5525_, 1, v___x_5534_);
v___x_5536_ = v___x_5525_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_currPos_5522_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
v_a_5511_ = v___x_5536_;
goto _start;
}
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v_slice_5542_; lean_object* v_nextIt_5544_; 
v___x_5539_ = lean_string_utf8_next_fast(v_x_5508_, v_searcher_5523_);
v___x_5540_ = lean_nat_sub(v___x_5539_, v_searcher_5523_);
v___x_5541_ = lean_nat_add(v_searcher_5523_, v___x_5540_);
lean_dec(v___x_5540_);
v_slice_5542_ = l_String_Slice_subslice_x21(v___x_5509_, v_currPos_5522_, v_searcher_5523_);
lean_inc(v___x_5541_);
if (v_isShared_5526_ == 0)
{
lean_ctor_set(v___x_5525_, 1, v___x_5541_);
lean_ctor_set(v___x_5525_, 0, v___x_5541_);
v_nextIt_5544_ = v___x_5525_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v___x_5541_);
v_nextIt_5544_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v_startInclusive_5545_; lean_object* v_endExclusive_5546_; 
v_startInclusive_5545_ = lean_ctor_get(v_slice_5542_, 0);
lean_inc(v_startInclusive_5545_);
v_endExclusive_5546_ = lean_ctor_get(v_slice_5542_, 1);
lean_inc(v_endExclusive_5546_);
lean_dec_ref(v_slice_5542_);
v_it_5514_ = v_nextIt_5544_;
v_startInclusive_5515_ = v_startInclusive_5545_;
v_endExclusive_5516_ = v_endExclusive_5546_;
goto v___jp_5513_;
}
}
}
else
{
lean_object* v___x_5548_; 
lean_del_object(v___x_5525_);
lean_dec(v_searcher_5523_);
v___x_5548_ = lean_box(1);
lean_inc(v___x_5510_);
v_it_5514_ = v___x_5548_;
v_startInclusive_5515_ = v_currPos_5522_;
v_endExclusive_5516_ = v___x_5510_;
goto v___jp_5513_;
}
}
}
else
{
lean_dec(v___x_5510_);
lean_dec_ref(v_x_5508_);
return v_b_5512_;
}
v___jp_5513_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
lean_inc_ref(v_x_5508_);
v___x_5517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5517_, 0, v_x_5508_);
lean_ctor_set(v___x_5517_, 1, v_startInclusive_5515_);
lean_ctor_set(v___x_5517_, 2, v_endExclusive_5516_);
v___x_5518_ = l_String_Slice_toString(v___x_5517_);
lean_dec_ref_known(v___x_5517_, 3);
v___x_5519_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_5518_);
v___x_5520_ = lean_array_push(v_b_5512_, v___x_5519_);
v_a_5511_ = v_it_5514_;
v_b_5512_ = v___x_5520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_x_5550_, lean_object* v___x_5551_, lean_object* v___x_5552_, lean_object* v_a_5553_, lean_object* v_b_5554_){
_start:
{
lean_object* v_res_5555_; 
v_res_5555_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_x_5550_, v___x_5551_, v___x_5552_, v_a_5553_, v_b_5554_);
lean_dec_ref(v___x_5551_);
return v_res_5555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(size_t v_sz_5556_, size_t v_i_5557_, lean_object* v_bs_5558_){
_start:
{
uint8_t v___x_5559_; 
v___x_5559_ = lean_usize_dec_lt(v_i_5557_, v_sz_5556_);
if (v___x_5559_ == 0)
{
return v_bs_5558_;
}
else
{
lean_object* v_v_5560_; lean_object* v___x_5561_; lean_object* v_bs_x27_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; size_t v___x_5571_; size_t v___x_5572_; lean_object* v___x_5573_; 
v_v_5560_ = lean_array_uget(v_bs_5558_, v_i_5557_);
v___x_5561_ = lean_unsigned_to_nat(0u);
v_bs_x27_5562_ = lean_array_uset(v_bs_5558_, v_i_5557_, v___x_5561_);
v___x_5563_ = lean_string_utf8_byte_size(v_v_5560_);
lean_inc(v_v_5560_);
v___x_5564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5564_, 0, v_v_5560_);
lean_ctor_set(v___x_5564_, 1, v___x_5561_);
lean_ctor_set(v___x_5564_, 2, v___x_5563_);
v___x_5565_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v___x_5564_);
v___x_5566_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_5567_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_5560_, v___x_5564_, v___x_5563_, v___x_5565_, v___x_5566_);
lean_dec_ref_known(v___x_5564_, 3);
v___x_5568_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_5569_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_5568_, v___x_5567_);
v___x_5570_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5569_);
v___x_5571_ = ((size_t)1ULL);
v___x_5572_ = lean_usize_add(v_i_5557_, v___x_5571_);
v___x_5573_ = lean_array_uset(v_bs_x27_5562_, v_i_5557_, v___x_5570_);
v_i_5557_ = v___x_5572_;
v_bs_5558_ = v___x_5573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_sz_5575_, lean_object* v_i_5576_, lean_object* v_bs_5577_){
_start:
{
size_t v_sz_boxed_5578_; size_t v_i_boxed_5579_; lean_object* v_res_5580_; 
v_sz_boxed_5578_ = lean_unbox_usize(v_sz_5575_);
lean_dec(v_sz_5575_);
v_i_boxed_5579_ = lean_unbox_usize(v_i_5576_);
lean_dec(v_i_5576_);
v_res_5580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_sz_boxed_5578_, v_i_boxed_5579_, v_bs_5577_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0(lean_object* v___x_5581_, lean_object* v_fst_5582_, lean_object* v_____r_5583_, uint8_t v_insertedAnyNewlines_5584_, lean_object* v_d_5585_){
_start:
{
lean_object* v_originalWhitespaceRange_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v_originalWhitespaceRange_5586_ = lean_ctor_get(v___x_5581_, 1);
lean_inc_ref(v_originalWhitespaceRange_5586_);
v___x_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5587_, 0, v_originalWhitespaceRange_5586_);
v___x_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5588_, 0, v_d_5585_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = lean_array_push(v_fst_5582_, v___x_5588_);
v___x_5590_ = lean_box(v_insertedAnyNewlines_5584_);
v___x_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5589_);
lean_ctor_set(v___x_5591_, 1, v___x_5590_);
v___x_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5591_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0___boxed(lean_object* v___x_5593_, lean_object* v_fst_5594_, lean_object* v_____r_5595_, lean_object* v_insertedAnyNewlines_5596_, lean_object* v_d_5597_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_5598_; lean_object* v_res_5599_; 
v_insertedAnyNewlines_boxed_5598_ = lean_unbox(v_insertedAnyNewlines_5596_);
v_res_5599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0(v___x_5593_, v_fst_5594_, v_____r_5595_, v_insertedAnyNewlines_boxed_5598_, v_d_5597_);
lean_dec_ref(v___x_5593_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_5600_, lean_object* v_x_5601_){
_start:
{
if (lean_obj_tag(v_x_5601_) == 0)
{
lean_object* v___x_5602_; 
v___x_5602_ = lean_box(0);
return v___x_5602_;
}
else
{
lean_object* v_key_5603_; lean_object* v_value_5604_; lean_object* v_tail_5605_; uint8_t v___x_5606_; 
v_key_5603_ = lean_ctor_get(v_x_5601_, 0);
v_value_5604_ = lean_ctor_get(v_x_5601_, 1);
v_tail_5605_ = lean_ctor_get(v_x_5601_, 2);
v___x_5606_ = lean_nat_dec_eq(v_key_5603_, v_a_5600_);
if (v___x_5606_ == 0)
{
v_x_5601_ = v_tail_5605_;
goto _start;
}
else
{
lean_object* v___x_5608_; 
lean_inc(v_value_5604_);
v___x_5608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5608_, 0, v_value_5604_);
return v___x_5608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_5609_, lean_object* v_x_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_5609_, v_x_5610_);
lean_dec(v_x_5610_);
lean_dec(v_a_5609_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_buckets_5614_; lean_object* v___x_5615_; uint64_t v___x_5616_; uint64_t v___x_5617_; uint64_t v___x_5618_; uint64_t v_fold_5619_; uint64_t v___x_5620_; uint64_t v___x_5621_; uint64_t v___x_5622_; size_t v___x_5623_; size_t v___x_5624_; size_t v___x_5625_; size_t v___x_5626_; size_t v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; 
v_buckets_5614_ = lean_ctor_get(v_m_5612_, 1);
v___x_5615_ = lean_array_get_size(v_buckets_5614_);
v___x_5616_ = lean_uint64_of_nat(v_a_5613_);
v___x_5617_ = 32ULL;
v___x_5618_ = lean_uint64_shift_right(v___x_5616_, v___x_5617_);
v_fold_5619_ = lean_uint64_xor(v___x_5616_, v___x_5618_);
v___x_5620_ = 16ULL;
v___x_5621_ = lean_uint64_shift_right(v_fold_5619_, v___x_5620_);
v___x_5622_ = lean_uint64_xor(v_fold_5619_, v___x_5621_);
v___x_5623_ = lean_uint64_to_usize(v___x_5622_);
v___x_5624_ = lean_usize_of_nat(v___x_5615_);
v___x_5625_ = ((size_t)1ULL);
v___x_5626_ = lean_usize_sub(v___x_5624_, v___x_5625_);
v___x_5627_ = lean_usize_land(v___x_5623_, v___x_5626_);
v___x_5628_ = lean_array_uget_borrowed(v_buckets_5614_, v___x_5627_);
v___x_5629_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_5613_, v___x_5628_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_5630_, v_a_5631_);
lean_dec(v_a_5631_);
lean_dec_ref(v_m_5630_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_5633_, lean_object* v_comments_5634_, lean_object* v_numNewlinesBeforeComments_5635_, lean_object* v_a_5636_, lean_object* v_b_5637_){
_start:
{
lean_object* v___y_5639_; uint8_t v___x_5645_; 
v___x_5645_ = lean_nat_dec_lt(v_a_5636_, v_upperBound_5633_);
if (v___x_5645_ == 0)
{
lean_dec(v_a_5636_);
return v_b_5637_;
}
else
{
lean_object* v_fst_5646_; lean_object* v_snd_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5704_; 
v_fst_5646_ = lean_ctor_get(v_b_5637_, 0);
v_snd_5647_ = lean_ctor_get(v_b_5637_, 1);
v_isSharedCheck_5704_ = !lean_is_exclusive(v_b_5637_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5649_ = v_b_5637_;
v_isShared_5650_ = v_isSharedCheck_5704_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_snd_5647_);
lean_inc(v_fst_5646_);
lean_dec(v_b_5637_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5704_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5651_; lean_object* v___y_5653_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5682_; uint8_t v___y_5685_; lean_object* v___y_5686_; uint8_t v___y_5690_; lean_object* v___y_5691_; uint8_t v___y_5695_; uint8_t v_insertedAnyNewlines_5698_; uint8_t v___x_5699_; 
v___x_5651_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_5698_ = 0;
v___x_5699_ = lean_nat_dec_eq(v_a_5636_, v___x_5651_);
if (v___x_5699_ == 0)
{
lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; uint8_t v_kind_5703_; 
v___x_5700_ = lean_unsigned_to_nat(1u);
v___x_5701_ = lean_nat_sub(v_a_5636_, v___x_5700_);
v___x_5702_ = lean_array_fget_borrowed(v_comments_5634_, v___x_5701_);
lean_dec(v___x_5701_);
v_kind_5703_ = lean_ctor_get_uint8(v___x_5702_, sizeof(void*)*3);
if (v_kind_5703_ == 1)
{
v___y_5695_ = v___x_5645_;
goto v___jp_5694_;
}
else
{
v___y_5695_ = v_insertedAnyNewlines_5698_;
goto v___jp_5694_;
}
}
else
{
v___y_5695_ = v_insertedAnyNewlines_5698_;
goto v___jp_5694_;
}
v___jp_5652_:
{
lean_object* v___x_5655_; 
if (v_isShared_5650_ == 0)
{
v___x_5655_ = v___x_5649_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_fst_5646_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v_snd_5647_);
v___x_5655_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5656_; lean_object* v_fst_5657_; lean_object* v_snd_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; size_t v_sz_5661_; uint8_t v_kind_5662_; size_t v___x_5663_; lean_object* v___x_5664_; size_t v_sz_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_5656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_5653_, v___x_5651_, v___x_5655_);
lean_dec(v___y_5653_);
v_fst_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_fst_5657_);
v_snd_5658_ = lean_ctor_get(v___x_5656_, 1);
lean_inc(v_snd_5658_);
lean_dec_ref(v___x_5656_);
v___x_5659_ = lean_array_fget_borrowed(v_comments_5634_, v_a_5636_);
lean_inc(v___x_5659_);
v___x_5660_ = l_Lean_Fmt_Comment_render(v___x_5659_);
v_sz_5661_ = lean_array_size(v___x_5660_);
v_kind_5662_ = lean_ctor_get_uint8(v___x_5659_, sizeof(void*)*3);
v___x_5663_ = ((size_t)0ULL);
v___x_5664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_5661_, v___x_5663_, v___x_5660_);
v_sz_5665_ = lean_array_size(v___x_5664_);
v___x_5666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_sz_5665_, v___x_5663_, v___x_5664_);
v___x_5667_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5666_);
v___x_5668_ = l_Lean_Fmt_TaggedDoc_free(v___x_5667_);
if (v_kind_5662_ == 0)
{
lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; 
lean_dec(v_snd_5658_);
v___x_5669_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_5670_ = l_Lean_Fmt_TaggedDoc_append(v___x_5668_, v___x_5669_);
v___x_5671_ = lean_box(0);
v___x_5672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0(v___x_5659_, v_fst_5657_, v___x_5671_, v___x_5645_, v___x_5670_);
v___y_5639_ = v___x_5672_;
goto v___jp_5638_;
}
else
{
lean_object* v___x_5673_; uint8_t v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = lean_box(0);
v___x_5674_ = lean_unbox(v_snd_5658_);
lean_dec(v_snd_5658_);
v___x_5675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___lam__0(v___x_5659_, v_fst_5657_, v___x_5673_, v___x_5674_, v___x_5668_);
v___y_5639_ = v___x_5675_;
goto v___jp_5638_;
}
}
}
v___jp_5677_:
{
uint8_t v___x_5680_; 
v___x_5680_ = lean_nat_dec_le(v___y_5678_, v___y_5679_);
if (v___x_5680_ == 0)
{
lean_dec(v___y_5678_);
v___y_5653_ = v___y_5679_;
goto v___jp_5652_;
}
else
{
lean_dec(v___y_5679_);
v___y_5653_ = v___y_5678_;
goto v___jp_5652_;
}
}
v___jp_5681_:
{
lean_object* v___x_5683_; 
v___x_5683_ = lean_unsigned_to_nat(2u);
v___y_5678_ = v___y_5682_;
v___y_5679_ = v___x_5683_;
goto v___jp_5677_;
}
v___jp_5684_:
{
uint8_t v___x_5687_; 
v___x_5687_ = lean_nat_dec_eq(v_a_5636_, v___x_5651_);
if (v___x_5687_ == 0)
{
if (v___y_5685_ == 0)
{
lean_object* v___x_5688_; 
v___x_5688_ = lean_unsigned_to_nat(1u);
v___y_5678_ = v___y_5686_;
v___y_5679_ = v___x_5688_;
goto v___jp_5677_;
}
else
{
v___y_5682_ = v___y_5686_;
goto v___jp_5681_;
}
}
else
{
v___y_5682_ = v___y_5686_;
goto v___jp_5681_;
}
}
v___jp_5689_:
{
if (v___y_5690_ == 0)
{
v___y_5685_ = v___y_5690_;
v___y_5686_ = v___y_5691_;
goto v___jp_5684_;
}
else
{
lean_object* v___x_5692_; uint8_t v___x_5693_; 
v___x_5692_ = lean_unsigned_to_nat(1u);
v___x_5693_ = lean_nat_dec_le(v___y_5691_, v___x_5692_);
if (v___x_5693_ == 0)
{
v___y_5685_ = v___y_5690_;
v___y_5686_ = v___y_5691_;
goto v___jp_5684_;
}
else
{
lean_dec(v___y_5691_);
v___y_5685_ = v___y_5690_;
v___y_5686_ = v___x_5692_;
goto v___jp_5684_;
}
}
}
v___jp_5694_:
{
lean_object* v___x_5696_; 
v___x_5696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_5635_, v_a_5636_);
if (lean_obj_tag(v___x_5696_) == 0)
{
v___y_5690_ = v___y_5695_;
v___y_5691_ = v___x_5651_;
goto v___jp_5689_;
}
else
{
lean_object* v_val_5697_; 
v_val_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_val_5697_);
lean_dec_ref_known(v___x_5696_, 1);
v___y_5690_ = v___y_5695_;
v___y_5691_ = v_val_5697_;
goto v___jp_5689_;
}
}
}
}
v___jp_5638_:
{
if (lean_obj_tag(v___y_5639_) == 0)
{
lean_object* v_a_5640_; 
lean_dec(v_a_5636_);
v_a_5640_ = lean_ctor_get(v___y_5639_, 0);
lean_inc(v_a_5640_);
lean_dec_ref_known(v___y_5639_, 1);
return v_a_5640_;
}
else
{
lean_object* v_a_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; 
v_a_5641_ = lean_ctor_get(v___y_5639_, 0);
lean_inc(v_a_5641_);
lean_dec_ref_known(v___y_5639_, 1);
v___x_5642_ = lean_unsigned_to_nat(1u);
v___x_5643_ = lean_nat_add(v_a_5636_, v___x_5642_);
lean_dec(v_a_5636_);
v_a_5636_ = v___x_5643_;
v_b_5637_ = v_a_5641_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_5705_, lean_object* v_comments_5706_, lean_object* v_numNewlinesBeforeComments_5707_, lean_object* v_a_5708_, lean_object* v_b_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_5705_, v_comments_5706_, v_numNewlinesBeforeComments_5707_, v_a_5708_, v_b_5709_);
lean_dec_ref(v_numNewlinesBeforeComments_5707_);
lean_dec_ref(v_comments_5706_);
lean_dec(v_upperBound_5705_);
return v_res_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_5717_, lean_object* v_whitespace_5718_, uint8_t v_isLeading_5719_){
_start:
{
lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___x_5748_; lean_object* v___y_5750_; lean_object* v___y_5751_; uint8_t v___y_5752_; lean_object* v___y_5753_; lean_object* v___y_5759_; lean_object* v___y_5760_; uint8_t v___y_5761_; lean_object* v___y_5762_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; uint8_t v___y_5769_; lean_object* v___y_5773_; lean_object* v___x_5786_; uint8_t v___x_5787_; 
v___x_5720_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_5721_ = lean_unsigned_to_nat(0u);
v___x_5748_ = lean_array_get_size(v_comments_5717_);
v___x_5786_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_5787_ = lean_nat_dec_lt(v___x_5721_, v___x_5748_);
if (v___x_5787_ == 0)
{
v___y_5773_ = v___x_5786_;
goto v___jp_5772_;
}
else
{
uint8_t v___x_5788_; 
v___x_5788_ = lean_nat_dec_le(v___x_5748_, v___x_5748_);
if (v___x_5788_ == 0)
{
if (v___x_5787_ == 0)
{
v___y_5773_ = v___x_5786_;
goto v___jp_5772_;
}
else
{
size_t v___x_5789_; size_t v___x_5790_; lean_object* v___x_5791_; 
v___x_5789_ = ((size_t)0ULL);
v___x_5790_ = lean_usize_of_nat(v___x_5748_);
v___x_5791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_comments_5717_, v___x_5789_, v___x_5790_, v___x_5786_);
v___y_5773_ = v___x_5791_;
goto v___jp_5772_;
}
}
else
{
size_t v___x_5792_; size_t v___x_5793_; lean_object* v___x_5794_; 
v___x_5792_ = ((size_t)0ULL);
v___x_5793_ = lean_usize_of_nat(v___x_5748_);
v___x_5794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_comments_5717_, v___x_5792_, v___x_5793_, v___x_5786_);
v___y_5773_ = v___x_5794_;
goto v___jp_5772_;
}
}
v___jp_5722_:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v_fst_5728_; lean_object* v_snd_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
v___x_5726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___y_5723_);
lean_ctor_set(v___x_5726_, 1, v___y_5724_);
v___x_5727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_5725_, v___x_5721_, v___x_5726_);
lean_dec(v___y_5725_);
v_fst_5728_ = lean_ctor_get(v___x_5727_, 0);
v_snd_5729_ = lean_ctor_get(v___x_5727_, 1);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5727_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5731_ = v___x_5727_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_snd_5729_);
lean_inc(v_fst_5728_);
lean_dec(v___x_5727_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_fst_5728_);
lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_snd_5729_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
v___jp_5737_:
{
uint8_t v___x_5742_; 
v___x_5742_ = lean_nat_dec_le(v___y_5740_, v___y_5741_);
if (v___x_5742_ == 0)
{
lean_dec(v___y_5740_);
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5739_;
v___y_5725_ = v___y_5741_;
goto v___jp_5722_;
}
else
{
lean_dec(v___y_5741_);
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5739_;
v___y_5725_ = v___y_5740_;
goto v___jp_5722_;
}
}
v___jp_5743_:
{
lean_object* v___x_5747_; 
v___x_5747_ = lean_unsigned_to_nat(2u);
v___y_5738_ = v___y_5744_;
v___y_5739_ = v___y_5745_;
v___y_5740_ = v___y_5746_;
v___y_5741_ = v___x_5747_;
goto v___jp_5737_;
}
v___jp_5749_:
{
if (v_isLeading_5719_ == 0)
{
uint8_t v___x_5754_; 
v___x_5754_ = lean_nat_dec_eq(v___x_5748_, v___x_5721_);
if (v___x_5754_ == 0)
{
if (v___y_5752_ == 0)
{
lean_object* v___x_5755_; 
v___x_5755_ = lean_unsigned_to_nat(1u);
v___y_5738_ = v___y_5750_;
v___y_5739_ = v___y_5751_;
v___y_5740_ = v___y_5753_;
v___y_5741_ = v___x_5755_;
goto v___jp_5737_;
}
else
{
v___y_5744_ = v___y_5750_;
v___y_5745_ = v___y_5751_;
v___y_5746_ = v___y_5753_;
goto v___jp_5743_;
}
}
else
{
v___y_5744_ = v___y_5750_;
v___y_5745_ = v___y_5751_;
v___y_5746_ = v___y_5753_;
goto v___jp_5743_;
}
}
else
{
uint8_t v___x_5756_; 
v___x_5756_ = lean_nat_dec_lt(v___x_5721_, v___x_5748_);
if (v___x_5756_ == 0)
{
v___y_5738_ = v___y_5750_;
v___y_5739_ = v___y_5751_;
v___y_5740_ = v___y_5753_;
v___y_5741_ = v___x_5721_;
goto v___jp_5737_;
}
else
{
lean_object* v___x_5757_; 
v___x_5757_ = lean_unsigned_to_nat(2u);
v___y_5738_ = v___y_5750_;
v___y_5739_ = v___y_5751_;
v___y_5740_ = v___y_5753_;
v___y_5741_ = v___x_5757_;
goto v___jp_5737_;
}
}
}
v___jp_5758_:
{
if (v___y_5761_ == 0)
{
v___y_5750_ = v___y_5759_;
v___y_5751_ = v___y_5760_;
v___y_5752_ = v___y_5761_;
v___y_5753_ = v___y_5762_;
goto v___jp_5749_;
}
else
{
lean_object* v___x_5763_; uint8_t v___x_5764_; 
v___x_5763_ = lean_unsigned_to_nat(1u);
v___x_5764_ = lean_nat_dec_le(v___y_5762_, v___x_5763_);
if (v___x_5764_ == 0)
{
v___y_5750_ = v___y_5759_;
v___y_5751_ = v___y_5760_;
v___y_5752_ = v___y_5761_;
v___y_5753_ = v___y_5762_;
goto v___jp_5749_;
}
else
{
lean_dec(v___y_5762_);
v___y_5750_ = v___y_5759_;
v___y_5751_ = v___y_5760_;
v___y_5752_ = v___y_5761_;
v___y_5753_ = v___x_5763_;
goto v___jp_5749_;
}
}
}
v___jp_5765_:
{
lean_object* v___x_5770_; 
v___x_5770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_5767_, v___x_5748_);
lean_dec_ref(v___y_5767_);
if (lean_obj_tag(v___x_5770_) == 0)
{
v___y_5759_ = v___y_5766_;
v___y_5760_ = v___y_5768_;
v___y_5761_ = v___y_5769_;
v___y_5762_ = v___x_5721_;
goto v___jp_5758_;
}
else
{
lean_object* v_val_5771_; 
v_val_5771_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_val_5771_);
lean_dec_ref_known(v___x_5770_, 1);
v___y_5759_ = v___y_5766_;
v___y_5760_ = v___y_5768_;
v___y_5761_ = v___y_5769_;
v___y_5762_ = v_val_5771_;
goto v___jp_5758_;
}
}
v___jp_5772_:
{
lean_object* v_numNewlinesBeforeComments_5774_; uint8_t v_insertedAnyNewlines_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v_fst_5778_; lean_object* v_snd_5779_; uint8_t v___x_5780_; 
v_numNewlinesBeforeComments_5774_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_5773_, v_whitespace_5718_);
lean_dec_ref(v___y_5773_);
v_insertedAnyNewlines_5775_ = 0;
v___x_5776_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_5777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___x_5748_, v_comments_5717_, v_numNewlinesBeforeComments_5774_, v___x_5721_, v___x_5776_);
v_fst_5778_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_fst_5778_);
v_snd_5779_ = lean_ctor_get(v___x_5777_, 1);
lean_inc(v_snd_5779_);
lean_dec_ref(v___x_5777_);
v___x_5780_ = lean_nat_dec_eq(v___x_5748_, v___x_5721_);
if (v___x_5780_ == 0)
{
lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; uint8_t v_kind_5784_; 
v___x_5781_ = lean_unsigned_to_nat(1u);
v___x_5782_ = lean_nat_sub(v___x_5748_, v___x_5781_);
v___x_5783_ = lean_array_get_borrowed(v___x_5720_, v_comments_5717_, v___x_5782_);
lean_dec(v___x_5782_);
v_kind_5784_ = lean_ctor_get_uint8(v___x_5783_, sizeof(void*)*3);
if (v_kind_5784_ == 1)
{
uint8_t v___x_5785_; 
v___x_5785_ = 1;
v___y_5766_ = v_fst_5778_;
v___y_5767_ = v_numNewlinesBeforeComments_5774_;
v___y_5768_ = v_snd_5779_;
v___y_5769_ = v___x_5785_;
goto v___jp_5765_;
}
else
{
v___y_5766_ = v_fst_5778_;
v___y_5767_ = v_numNewlinesBeforeComments_5774_;
v___y_5768_ = v_snd_5779_;
v___y_5769_ = v_insertedAnyNewlines_5775_;
goto v___jp_5765_;
}
}
else
{
v___y_5766_ = v_fst_5778_;
v___y_5767_ = v_numNewlinesBeforeComments_5774_;
v___y_5768_ = v_snd_5779_;
v___y_5769_ = v_insertedAnyNewlines_5775_;
goto v___jp_5765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_5795_, lean_object* v_whitespace_5796_, lean_object* v_isLeading_5797_){
_start:
{
uint8_t v_isLeading_boxed_5798_; lean_object* v_res_5799_; 
v_isLeading_boxed_5798_ = lean_unbox(v_isLeading_5797_);
v_res_5799_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_5795_, v_whitespace_5796_, v_isLeading_boxed_5798_);
lean_dec_ref(v_whitespace_5796_);
lean_dec_ref(v_comments_5795_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_x_5800_, lean_object* v___x_5801_, lean_object* v___x_5802_, lean_object* v_inst_5803_, lean_object* v_R_5804_, lean_object* v_a_5805_, lean_object* v_b_5806_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_x_5800_, v___x_5801_, v___x_5802_, v_a_5805_, v_b_5806_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_x_5808_, lean_object* v___x_5809_, lean_object* v___x_5810_, lean_object* v_inst_5811_, lean_object* v_R_5812_, lean_object* v_a_5813_, lean_object* v_b_5814_){
_start:
{
lean_object* v_res_5815_; 
v_res_5815_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_x_5808_, v___x_5809_, v___x_5810_, v_inst_5811_, v_R_5812_, v_a_5813_, v_b_5814_);
lean_dec_ref(v___x_5809_);
return v_res_5815_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_5816_, lean_object* v_inst_5817_, lean_object* v_R_5818_, lean_object* v_a_5819_, lean_object* v_b_5820_, lean_object* v_c_5821_){
_start:
{
lean_object* v___x_5822_; 
v___x_5822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_5816_, v_a_5819_, v_b_5820_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_5823_, lean_object* v_inst_5824_, lean_object* v_R_5825_, lean_object* v_a_5826_, lean_object* v_b_5827_, lean_object* v_c_5828_){
_start:
{
lean_object* v_res_5829_; 
v_res_5829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_5823_, v_inst_5824_, v_R_5825_, v_a_5826_, v_b_5827_, v_c_5828_);
lean_dec(v_upperBound_5823_);
return v_res_5829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_5830_, lean_object* v_m_5831_, lean_object* v_a_5832_){
_start:
{
lean_object* v___x_5833_; 
v___x_5833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_5831_, v_a_5832_);
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_5834_, lean_object* v_m_5835_, lean_object* v_a_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_5834_, v_m_5835_, v_a_5836_);
lean_dec(v_a_5836_);
lean_dec_ref(v_m_5835_);
return v_res_5837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_5838_, lean_object* v_comments_5839_, lean_object* v_numNewlinesBeforeComments_5840_, lean_object* v_inst_5841_, lean_object* v_R_5842_, lean_object* v_a_5843_, lean_object* v_b_5844_, lean_object* v_c_5845_){
_start:
{
lean_object* v___x_5846_; 
v___x_5846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_5838_, v_comments_5839_, v_numNewlinesBeforeComments_5840_, v_a_5843_, v_b_5844_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_5847_, lean_object* v_comments_5848_, lean_object* v_numNewlinesBeforeComments_5849_, lean_object* v_inst_5850_, lean_object* v_R_5851_, lean_object* v_a_5852_, lean_object* v_b_5853_, lean_object* v_c_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_5847_, v_comments_5848_, v_numNewlinesBeforeComments_5849_, v_inst_5850_, v_R_5851_, v_a_5852_, v_b_5853_, v_c_5854_);
lean_dec_ref(v_numNewlinesBeforeComments_5849_);
lean_dec_ref(v_comments_5848_);
lean_dec(v_upperBound_5847_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_5856_, lean_object* v_a_5857_, lean_object* v_x_5858_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_5857_, v_x_5858_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_5860_, lean_object* v_a_5861_, lean_object* v_x_5862_){
_start:
{
lean_object* v_res_5863_; 
v_res_5863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_5860_, v_a_5861_, v_x_5862_);
lean_dec(v_x_5862_);
lean_dec(v_a_5861_);
return v_res_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_5866_, lean_object* v_leading_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_){
_start:
{
lean_object* v___y_5871_; uint8_t v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = 0;
v___x_5878_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_5866_, v___x_5877_);
if (lean_obj_tag(v___x_5878_) == 1)
{
lean_object* v_val_5879_; lean_object* v_str_5880_; lean_object* v_startPos_5881_; lean_object* v_stopPos_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5905_; 
v_val_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_val_5879_);
lean_dec_ref_known(v___x_5878_, 1);
v_str_5880_ = lean_ctor_get(v_leading_5867_, 0);
v_startPos_5881_ = lean_ctor_get(v_leading_5867_, 1);
v_stopPos_5882_ = lean_ctor_get(v_leading_5867_, 2);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_leading_5867_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5884_ = v_leading_5867_;
v_isShared_5885_ = v_isSharedCheck_5905_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_stopPos_5882_);
lean_inc(v_startPos_5881_);
lean_inc(v_str_5880_);
lean_dec(v_leading_5867_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5905_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
uint8_t v___x_5886_; 
v___x_5886_ = lean_string_is_valid_pos(v_str_5880_, v_startPos_5881_);
if (v___x_5886_ == 0)
{
lean_del_object(v___x_5884_);
lean_dec(v_stopPos_5882_);
lean_dec(v_startPos_5881_);
lean_dec_ref(v_str_5880_);
lean_dec(v_val_5879_);
v___y_5871_ = v___y_5869_;
goto v___jp_5870_;
}
else
{
uint8_t v___x_5887_; 
v___x_5887_ = lean_string_is_valid_pos(v_str_5880_, v_stopPos_5882_);
if (v___x_5887_ == 0)
{
lean_del_object(v___x_5884_);
lean_dec(v_stopPos_5882_);
lean_dec(v_startPos_5881_);
lean_dec_ref(v_str_5880_);
lean_dec(v_val_5879_);
v___y_5871_ = v___y_5869_;
goto v___jp_5870_;
}
else
{
uint8_t v___x_5888_; 
v___x_5888_ = lean_nat_dec_le(v_startPos_5881_, v_stopPos_5882_);
if (v___x_5888_ == 0)
{
lean_del_object(v___x_5884_);
lean_dec(v_stopPos_5882_);
lean_dec(v_startPos_5881_);
lean_dec_ref(v_str_5880_);
lean_dec(v_val_5879_);
v___y_5871_ = v___y_5869_;
goto v___jp_5870_;
}
else
{
lean_object* v_lineInfos_5889_; lean_object* v___x_5891_; 
lean_dec(v_leadingTk_5866_);
v_lineInfos_5889_ = lean_ctor_get(v___y_5868_, 4);
if (v_isShared_5885_ == 0)
{
v___x_5891_ = v___x_5884_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_str_5880_);
lean_ctor_set(v_reuseFailAlloc_5904_, 1, v_startPos_5881_);
lean_ctor_set(v_reuseFailAlloc_5904_, 2, v_stopPos_5882_);
v___x_5891_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
uint8_t v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v_fst_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
v___x_5892_ = 0;
lean_inc_ref(v___x_5891_);
v___x_5893_ = l_Lean_Fmt_parseComments(v_lineInfos_5889_, v_val_5879_, v___x_5892_, v___x_5891_);
v___x_5894_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_5893_, v___x_5891_, v___x_5888_);
lean_dec_ref(v___x_5891_);
lean_dec_ref(v___x_5893_);
v_fst_5895_ = lean_ctor_get(v___x_5894_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5894_);
if (v_isSharedCheck_5902_ == 0)
{
lean_object* v_unused_5903_; 
v_unused_5903_ = lean_ctor_get(v___x_5894_, 1);
lean_dec(v_unused_5903_);
v___x_5897_ = v___x_5894_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_fst_5895_);
lean_dec(v___x_5894_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
lean_ctor_set(v___x_5897_, 1, v___y_5869_);
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_fst_5895_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v___y_5869_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
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
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v_msg_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_dec(v___x_5878_);
lean_dec_ref(v_leading_5867_);
v___x_5906_ = lean_box(0);
v___x_5907_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v_msg_5908_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_5909_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_5909_, 0, v_leadingTk_5866_);
lean_ctor_set(v___x_5909_, 1, v___x_5906_);
lean_ctor_set(v___x_5909_, 2, v___x_5907_);
lean_ctor_set(v___x_5909_, 3, v_msg_5908_);
v___x_5910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
lean_ctor_set(v___x_5910_, 1, v___y_5869_);
return v___x_5910_;
}
v___jp_5870_:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v_msg_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5872_ = lean_box(0);
v___x_5873_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v_msg_5874_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5875_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_5875_, 0, v_leadingTk_5866_);
lean_ctor_set(v___x_5875_, 1, v___x_5872_);
lean_ctor_set(v___x_5875_, 2, v___x_5873_);
lean_ctor_set(v___x_5875_, 3, v_msg_5874_);
v___x_5876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5875_);
lean_ctor_set(v___x_5876_, 1, v___y_5871_);
return v___x_5876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_5911_, lean_object* v_leading_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_){
_start:
{
lean_object* v_res_5915_; 
v_res_5915_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_5911_, v_leading_5912_, v___y_5913_, v___y_5914_);
lean_dec_ref(v___y_5913_);
return v_res_5915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_){
_start:
{
lean_object* v___f_5920_; lean_object* v___x_5921_; 
v___f_5920_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_5921_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5917_, v___f_5920_, v_a_5918_, v_a_5919_);
return v___x_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_5922_, v_a_5923_, v_a_5924_);
lean_dec_ref(v_a_5923_);
return v_res_5925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_5926_, lean_object* v_trailingTk_5927_, lean_object* v_trailing_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_){
_start:
{
lean_object* v___y_5932_; uint8_t v___x_5938_; lean_object* v___x_5939_; 
v___x_5938_ = 0;
v___x_5939_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_5927_, v___x_5938_);
if (lean_obj_tag(v___x_5939_) == 1)
{
lean_object* v_val_5940_; lean_object* v_str_5941_; lean_object* v_startPos_5942_; lean_object* v_stopPos_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_6001_; 
v_val_5940_ = lean_ctor_get(v___x_5939_, 0);
lean_inc(v_val_5940_);
lean_dec_ref_known(v___x_5939_, 1);
v_str_5941_ = lean_ctor_get(v_trailing_5928_, 0);
v_startPos_5942_ = lean_ctor_get(v_trailing_5928_, 1);
v_stopPos_5943_ = lean_ctor_get(v_trailing_5928_, 2);
v_isSharedCheck_6001_ = !lean_is_exclusive(v_trailing_5928_);
if (v_isSharedCheck_6001_ == 0)
{
v___x_5945_ = v_trailing_5928_;
v_isShared_5946_ = v_isSharedCheck_6001_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_stopPos_5943_);
lean_inc(v_startPos_5942_);
lean_inc(v_str_5941_);
lean_dec(v_trailing_5928_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_6001_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
uint8_t v___x_5947_; 
v___x_5947_ = lean_string_is_valid_pos(v_str_5941_, v_startPos_5942_);
if (v___x_5947_ == 0)
{
lean_del_object(v___x_5945_);
lean_dec(v_stopPos_5943_);
lean_dec(v_startPos_5942_);
lean_dec_ref(v_str_5941_);
lean_dec(v_val_5940_);
v___y_5932_ = v___y_5930_;
goto v___jp_5931_;
}
else
{
uint8_t v___x_5948_; 
v___x_5948_ = lean_string_is_valid_pos(v_str_5941_, v_stopPos_5943_);
if (v___x_5948_ == 0)
{
lean_del_object(v___x_5945_);
lean_dec(v_stopPos_5943_);
lean_dec(v_startPos_5942_);
lean_dec_ref(v_str_5941_);
lean_dec(v_val_5940_);
v___y_5932_ = v___y_5930_;
goto v___jp_5931_;
}
else
{
uint8_t v___x_5949_; 
v___x_5949_ = lean_nat_dec_le(v_startPos_5942_, v_stopPos_5943_);
if (v___x_5949_ == 0)
{
lean_del_object(v___x_5945_);
lean_dec(v_stopPos_5943_);
lean_dec(v_startPos_5942_);
lean_dec_ref(v_str_5941_);
lean_dec(v_val_5940_);
v___y_5932_ = v___y_5930_;
goto v___jp_5931_;
}
else
{
lean_object* v_lineInfos_5950_; lean_object* v___x_5952_; 
lean_dec(v_trailingTk_5927_);
v_lineInfos_5950_ = lean_ctor_get(v___y_5929_, 4);
if (v_isShared_5946_ == 0)
{
v___x_5952_ = v___x_5945_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_str_5941_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_startPos_5942_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_stopPos_5943_);
v___x_5952_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
lean_object* v___y_5954_; uint8_t v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; uint8_t v___x_5992_; 
v___x_5987_ = 1;
lean_inc_ref(v___x_5952_);
v___x_5988_ = l_Lean_Fmt_parseComments(v_lineInfos_5950_, v_val_5940_, v___x_5987_, v___x_5952_);
v___x_5989_ = lean_unsigned_to_nat(0u);
v___x_5990_ = lean_array_get_size(v___x_5988_);
v___x_5991_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_5992_ = lean_nat_dec_lt(v___x_5989_, v___x_5990_);
if (v___x_5992_ == 0)
{
lean_dec_ref(v___x_5988_);
v___y_5954_ = v___x_5991_;
goto v___jp_5953_;
}
else
{
uint8_t v___x_5993_; 
v___x_5993_ = lean_nat_dec_le(v___x_5990_, v___x_5990_);
if (v___x_5993_ == 0)
{
if (v___x_5992_ == 0)
{
lean_dec_ref(v___x_5988_);
v___y_5954_ = v___x_5991_;
goto v___jp_5953_;
}
else
{
size_t v___x_5994_; size_t v___x_5995_; lean_object* v___x_5996_; 
v___x_5994_ = ((size_t)0ULL);
v___x_5995_ = lean_usize_of_nat(v___x_5990_);
v___x_5996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v___x_5988_, v___x_5994_, v___x_5995_, v___x_5991_);
lean_dec_ref(v___x_5988_);
v___y_5954_ = v___x_5996_;
goto v___jp_5953_;
}
}
else
{
size_t v___x_5997_; size_t v___x_5998_; lean_object* v___x_5999_; 
v___x_5997_ = ((size_t)0ULL);
v___x_5998_ = lean_usize_of_nat(v___x_5990_);
v___x_5999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v___x_5988_, v___x_5997_, v___x_5998_, v___x_5991_);
lean_dec_ref(v___x_5988_);
v___y_5954_ = v___x_5999_;
goto v___jp_5953_;
}
}
v___jp_5953_:
{
lean_object* v___x_5955_; lean_object* v_snd_5956_; uint8_t v___x_5957_; 
v___x_5955_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_5954_, v___x_5952_, v___x_5938_);
lean_dec_ref(v___x_5952_);
lean_dec_ref(v___y_5954_);
v_snd_5956_ = lean_ctor_get(v___x_5955_, 1);
lean_inc(v_snd_5956_);
v___x_5957_ = lean_unbox(v_snd_5956_);
lean_dec(v_snd_5956_);
if (v___x_5957_ == 0)
{
if (v_atleastOneNewline_5926_ == 0)
{
lean_object* v_fst_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5965_; 
v_fst_5958_ = lean_ctor_get(v___x_5955_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5955_);
if (v_isSharedCheck_5965_ == 0)
{
lean_object* v_unused_5966_; 
v_unused_5966_ = lean_ctor_get(v___x_5955_, 1);
lean_dec(v_unused_5966_);
v___x_5960_ = v___x_5955_;
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_fst_5958_);
lean_dec(v___x_5955_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5963_; 
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___y_5930_);
v___x_5963_ = v___x_5960_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_fst_5958_);
lean_ctor_set(v_reuseFailAlloc_5964_, 1, v___y_5930_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
return v___x_5963_;
}
}
}
else
{
lean_object* v_fst_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5976_; 
v_fst_5967_ = lean_ctor_get(v___x_5955_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v___x_5955_);
if (v_isSharedCheck_5976_ == 0)
{
lean_object* v_unused_5977_; 
v_unused_5977_ = lean_ctor_get(v___x_5955_, 1);
lean_dec(v_unused_5977_);
v___x_5969_ = v___x_5955_;
v_isShared_5970_ = v_isSharedCheck_5976_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_fst_5967_);
lean_dec(v___x_5955_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5976_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5971_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_5972_ = lean_array_push(v_fst_5967_, v___x_5971_);
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v___y_5930_);
lean_ctor_set(v___x_5969_, 0, v___x_5972_);
v___x_5974_ = v___x_5969_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___y_5930_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
}
}
else
{
lean_object* v_fst_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5985_; 
v_fst_5978_ = lean_ctor_get(v___x_5955_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5955_);
if (v_isSharedCheck_5985_ == 0)
{
lean_object* v_unused_5986_; 
v_unused_5986_ = lean_ctor_get(v___x_5955_, 1);
lean_dec(v_unused_5986_);
v___x_5980_ = v___x_5955_;
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_fst_5978_);
lean_dec(v___x_5955_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v___x_5983_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v___y_5930_);
v___x_5983_ = v___x_5980_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_fst_5978_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___y_5930_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
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
lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v_msg_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; 
lean_dec(v___x_5939_);
lean_dec_ref(v_trailing_5928_);
v___x_6002_ = lean_box(0);
v___x_6003_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v_msg_6004_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6005_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_6005_, 0, v_trailingTk_5927_);
lean_ctor_set(v___x_6005_, 1, v___x_6002_);
lean_ctor_set(v___x_6005_, 2, v___x_6003_);
lean_ctor_set(v___x_6005_, 3, v_msg_6004_);
v___x_6006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___y_5930_);
return v___x_6006_;
}
v___jp_5931_:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v_msg_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
v___x_5933_ = lean_box(0);
v___x_5934_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v_msg_5935_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5936_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_5936_, 0, v_trailingTk_5927_);
lean_ctor_set(v___x_5936_, 1, v___x_5933_);
lean_ctor_set(v___x_5936_, 2, v___x_5934_);
lean_ctor_set(v___x_5936_, 3, v_msg_5935_);
v___x_5937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
lean_ctor_set(v___x_5937_, 1, v___y_5932_);
return v___x_5937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6007_, lean_object* v_trailingTk_6008_, lean_object* v_trailing_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6012_; lean_object* v_res_6013_; 
v_atleastOneNewline_boxed_6012_ = lean_unbox(v_atleastOneNewline_6007_);
v_res_6013_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6012_, v_trailingTk_6008_, v_trailing_6009_, v___y_6010_, v___y_6011_);
lean_dec_ref(v___y_6010_);
return v_res_6013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6014_, uint8_t v_atleastOneNewline_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_){
_start:
{
lean_object* v___x_6018_; lean_object* v___f_6019_; lean_object* v___x_6020_; 
v___x_6018_ = lean_box(v_atleastOneNewline_6015_);
v___f_6019_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6019_, 0, v___x_6018_);
v___x_6020_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6014_, v___f_6019_, v_a_6016_, v_a_6017_);
return v___x_6020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6021_, lean_object* v_atleastOneNewline_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6025_; lean_object* v_res_6026_; 
v_atleastOneNewline_boxed_6025_ = lean_unbox(v_atleastOneNewline_6022_);
v_res_6026_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6021_, v_atleastOneNewline_boxed_6025_, v_a_6023_, v_a_6024_);
lean_dec_ref(v_a_6023_);
return v_res_6026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6027_, lean_object* v_stxs_6028_, lean_object* v_f_6029_, lean_object* v___x_6030_, lean_object* v_a_6031_, lean_object* v_b_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_){
_start:
{
uint8_t v___x_6035_; 
v___x_6035_ = lean_nat_dec_lt(v_a_6031_, v_upperBound_6027_);
if (v___x_6035_ == 0)
{
lean_object* v___x_6036_; 
lean_dec(v_a_6031_);
lean_dec_ref(v_f_6029_);
v___x_6036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6036_, 0, v_b_6032_);
lean_ctor_set(v___x_6036_, 1, v___y_6034_);
return v___x_6036_;
}
else
{
lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6037_ = lean_array_fget_borrowed(v_stxs_6028_, v_a_6031_);
lean_inc_ref(v_f_6029_);
lean_inc_ref(v___y_6033_);
lean_inc(v___x_6037_);
v___x_6038_ = lean_apply_3(v_f_6029_, v___x_6037_, v___y_6033_, v___y_6034_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; lean_object* v_a_6040_; lean_object* v___x_6041_; lean_object* v___y_6043_; lean_object* v___x_6068_; uint8_t v___x_6069_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6039_);
v_a_6040_ = lean_ctor_get(v___x_6038_, 1);
lean_inc(v_a_6040_);
lean_dec_ref_known(v___x_6038_, 2);
v___x_6041_ = lean_unsigned_to_nat(1u);
v___x_6068_ = lean_nat_sub(v___x_6030_, v___x_6041_);
v___x_6069_ = lean_nat_dec_lt(v_a_6031_, v___x_6068_);
lean_dec(v___x_6068_);
if (v___x_6069_ == 0)
{
lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6070_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_a_6039_, v_b_6032_, v___x_6070_, v___y_6033_, v_a_6040_);
v___y_6043_ = v___x_6071_;
goto v___jp_6042_;
}
else
{
lean_object* v___x_6072_; 
lean_inc(v___x_6037_);
v___x_6072_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6037_, v___x_6069_, v___y_6033_, v_a_6040_);
if (lean_obj_tag(v___x_6072_) == 0)
{
lean_object* v_a_6073_; lean_object* v_a_6074_; lean_object* v___x_6075_; 
v_a_6073_ = lean_ctor_get(v___x_6072_, 0);
lean_inc(v_a_6073_);
v_a_6074_ = lean_ctor_get(v___x_6072_, 1);
lean_inc(v_a_6074_);
lean_dec_ref_known(v___x_6072_, 2);
v___x_6075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_a_6039_, v_b_6032_, v_a_6073_, v___y_6033_, v_a_6074_);
v___y_6043_ = v___x_6075_;
goto v___jp_6042_;
}
else
{
lean_object* v_a_6076_; lean_object* v_a_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6084_; 
lean_dec(v_a_6039_);
lean_dec_ref(v_b_6032_);
lean_dec(v_a_6031_);
lean_dec_ref(v_f_6029_);
v_a_6076_ = lean_ctor_get(v___x_6072_, 0);
v_a_6077_ = lean_ctor_get(v___x_6072_, 1);
v_isSharedCheck_6084_ = !lean_is_exclusive(v___x_6072_);
if (v_isSharedCheck_6084_ == 0)
{
v___x_6079_ = v___x_6072_;
v_isShared_6080_ = v_isSharedCheck_6084_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_a_6077_);
lean_inc(v_a_6076_);
lean_dec(v___x_6072_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6084_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6082_; 
if (v_isShared_6080_ == 0)
{
v___x_6082_ = v___x_6079_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6083_; 
v_reuseFailAlloc_6083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6083_, 0, v_a_6076_);
lean_ctor_set(v_reuseFailAlloc_6083_, 1, v_a_6077_);
v___x_6082_ = v_reuseFailAlloc_6083_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
return v___x_6082_;
}
}
}
}
v___jp_6042_:
{
if (lean_obj_tag(v___y_6043_) == 0)
{
lean_object* v_a_6044_; 
v_a_6044_ = lean_ctor_get(v___y_6043_, 0);
lean_inc(v_a_6044_);
if (lean_obj_tag(v_a_6044_) == 0)
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6053_; 
lean_dec(v_a_6031_);
lean_dec_ref(v_f_6029_);
v_a_6045_ = lean_ctor_get(v___y_6043_, 1);
v_isSharedCheck_6053_ = !lean_is_exclusive(v___y_6043_);
if (v_isSharedCheck_6053_ == 0)
{
lean_object* v_unused_6054_; 
v_unused_6054_ = lean_ctor_get(v___y_6043_, 0);
lean_dec(v_unused_6054_);
v___x_6047_ = v___y_6043_;
v_isShared_6048_ = v_isSharedCheck_6053_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v___y_6043_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6053_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v_a_6049_; lean_object* v___x_6051_; 
v_a_6049_ = lean_ctor_get(v_a_6044_, 0);
lean_inc(v_a_6049_);
lean_dec_ref_known(v_a_6044_, 1);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 0, v_a_6049_);
v___x_6051_ = v___x_6047_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6049_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v_a_6045_);
v___x_6051_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
return v___x_6051_;
}
}
}
else
{
lean_object* v_a_6055_; lean_object* v_a_6056_; lean_object* v___x_6057_; 
v_a_6055_ = lean_ctor_get(v___y_6043_, 1);
lean_inc(v_a_6055_);
lean_dec_ref_known(v___y_6043_, 2);
v_a_6056_ = lean_ctor_get(v_a_6044_, 0);
lean_inc(v_a_6056_);
lean_dec_ref_known(v_a_6044_, 1);
v___x_6057_ = lean_nat_add(v_a_6031_, v___x_6041_);
lean_dec(v_a_6031_);
v_a_6031_ = v___x_6057_;
v_b_6032_ = v_a_6056_;
v___y_6034_ = v_a_6055_;
goto _start;
}
}
else
{
lean_object* v_a_6059_; lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
lean_dec(v_a_6031_);
lean_dec_ref(v_f_6029_);
v_a_6059_ = lean_ctor_get(v___y_6043_, 0);
v_a_6060_ = lean_ctor_get(v___y_6043_, 1);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___y_6043_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6062_ = v___y_6043_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_inc(v_a_6059_);
lean_dec(v___y_6043_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6059_);
lean_ctor_set(v_reuseFailAlloc_6066_, 1, v_a_6060_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
}
}
else
{
lean_object* v_a_6085_; lean_object* v_a_6086_; lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6093_; 
lean_dec_ref(v_b_6032_);
lean_dec(v_a_6031_);
lean_dec_ref(v_f_6029_);
v_a_6085_ = lean_ctor_get(v___x_6038_, 0);
v_a_6086_ = lean_ctor_get(v___x_6038_, 1);
v_isSharedCheck_6093_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6093_ == 0)
{
v___x_6088_ = v___x_6038_;
v_isShared_6089_ = v_isSharedCheck_6093_;
goto v_resetjp_6087_;
}
else
{
lean_inc(v_a_6086_);
lean_inc(v_a_6085_);
lean_dec(v___x_6038_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6093_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v___x_6091_; 
if (v_isShared_6089_ == 0)
{
v___x_6091_ = v___x_6088_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v_a_6085_);
lean_ctor_set(v_reuseFailAlloc_6092_, 1, v_a_6086_);
v___x_6091_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
return v___x_6091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6094_, lean_object* v_stxs_6095_, lean_object* v_f_6096_, lean_object* v___x_6097_, lean_object* v_a_6098_, lean_object* v_b_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v_res_6102_; 
v_res_6102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6094_, v_stxs_6095_, v_f_6096_, v___x_6097_, v_a_6098_, v_b_6099_, v___y_6100_, v___y_6101_);
lean_dec_ref(v___y_6100_);
lean_dec(v___x_6097_);
lean_dec_ref(v_stxs_6095_);
lean_dec(v_upperBound_6094_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6103_, lean_object* v_stxs_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_){
_start:
{
lean_object* v___x_6107_; lean_object* v___x_6108_; uint8_t v___x_6109_; 
v___x_6107_ = lean_array_get_size(v_stxs_6104_);
v___x_6108_ = lean_unsigned_to_nat(1u);
v___x_6109_ = lean_nat_dec_eq(v___x_6107_, v___x_6108_);
if (v___x_6109_ == 0)
{
lean_object* v___x_6110_; lean_object* v_acc_6111_; lean_object* v___x_6112_; 
v___x_6110_ = lean_unsigned_to_nat(0u);
v_acc_6111_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6107_, v_stxs_6104_, v_f_6103_, v___x_6107_, v___x_6110_, v_acc_6111_, v_a_6105_, v_a_6106_);
if (lean_obj_tag(v___x_6112_) == 0)
{
lean_object* v_a_6113_; lean_object* v_a_6114_; lean_object* v___x_6116_; uint8_t v_isShared_6117_; uint8_t v_isSharedCheck_6122_; 
v_a_6113_ = lean_ctor_get(v___x_6112_, 0);
v_a_6114_ = lean_ctor_get(v___x_6112_, 1);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6116_ = v___x_6112_;
v_isShared_6117_ = v_isSharedCheck_6122_;
goto v_resetjp_6115_;
}
else
{
lean_inc(v_a_6114_);
lean_inc(v_a_6113_);
lean_dec(v___x_6112_);
v___x_6116_ = lean_box(0);
v_isShared_6117_ = v_isSharedCheck_6122_;
goto v_resetjp_6115_;
}
v_resetjp_6115_:
{
lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6118_ = l_Lean_Fmt_TaggedDoc_join(v_a_6113_);
if (v_isShared_6117_ == 0)
{
lean_ctor_set(v___x_6116_, 0, v___x_6118_);
v___x_6120_ = v___x_6116_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6118_);
lean_ctor_set(v_reuseFailAlloc_6121_, 1, v_a_6114_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
else
{
lean_object* v_a_6123_; lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
v_a_6123_ = lean_ctor_get(v___x_6112_, 0);
v_a_6124_ = lean_ctor_get(v___x_6112_, 1);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6112_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_inc(v_a_6123_);
lean_dec(v___x_6112_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6123_);
lean_ctor_set(v_reuseFailAlloc_6130_, 1, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
else
{
lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6132_ = lean_box(0);
v___x_6133_ = lean_unsigned_to_nat(0u);
v___x_6134_ = lean_array_get_borrowed(v___x_6132_, v_stxs_6104_, v___x_6133_);
lean_inc_ref(v_a_6105_);
lean_inc(v___x_6134_);
v___x_6135_ = lean_apply_3(v_f_6103_, v___x_6134_, v_a_6105_, v_a_6106_);
return v___x_6135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6136_, lean_object* v_stxs_6137_, lean_object* v_a_6138_, lean_object* v_a_6139_){
_start:
{
lean_object* v_res_6140_; 
v_res_6140_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6136_, v_stxs_6137_, v_a_6138_, v_a_6139_);
lean_dec_ref(v_a_6138_);
lean_dec_ref(v_stxs_6137_);
return v_res_6140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6141_, lean_object* v_stxs_6142_, lean_object* v_f_6143_, lean_object* v___x_6144_, lean_object* v_inst_6145_, lean_object* v_R_6146_, lean_object* v_a_6147_, lean_object* v_b_6148_, lean_object* v_c_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_){
_start:
{
lean_object* v___x_6152_; 
v___x_6152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6141_, v_stxs_6142_, v_f_6143_, v___x_6144_, v_a_6147_, v_b_6148_, v___y_6150_, v___y_6151_);
return v___x_6152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6153_, lean_object* v_stxs_6154_, lean_object* v_f_6155_, lean_object* v___x_6156_, lean_object* v_inst_6157_, lean_object* v_R_6158_, lean_object* v_a_6159_, lean_object* v_b_6160_, lean_object* v_c_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_){
_start:
{
lean_object* v_res_6164_; 
v_res_6164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6153_, v_stxs_6154_, v_f_6155_, v___x_6156_, v_inst_6157_, v_R_6158_, v_a_6159_, v_b_6160_, v_c_6161_, v___y_6162_, v___y_6163_);
lean_dec_ref(v___y_6162_);
lean_dec(v___x_6156_);
lean_dec_ref(v_stxs_6154_);
lean_dec(v_upperBound_6153_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6169_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6168_, v_stxs_6165_, v_a_6166_, v_a_6167_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6170_, lean_object* v_a_6171_, lean_object* v_a_6172_){
_start:
{
lean_object* v_res_6173_; 
v_res_6173_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6170_, v_a_6171_, v_a_6172_);
lean_dec_ref(v_a_6171_);
lean_dec_ref(v_stxs_6170_);
return v_res_6173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg(lean_object* v_x_6174_){
_start:
{
if (lean_obj_tag(v_x_6174_) == 0)
{
lean_object* v___x_6175_; 
v___x_6175_ = lean_unsigned_to_nat(0u);
return v___x_6175_;
}
else
{
lean_object* v___x_6176_; 
v___x_6176_ = lean_unsigned_to_nat(1u);
return v___x_6176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg___boxed(lean_object* v_x_6177_){
_start:
{
lean_object* v_res_6178_; 
v_res_6178_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg(v_x_6177_);
lean_dec_ref(v_x_6177_);
return v_res_6178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx(lean_object* v_sep_6179_, lean_object* v_x_6180_){
_start:
{
lean_object* v___x_6181_; 
v___x_6181_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___redArg(v_x_6180_);
return v___x_6181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx___boxed(lean_object* v_sep_6182_, lean_object* v_x_6183_){
_start:
{
lean_object* v_res_6184_; 
v_res_6184_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorIdx(v_sep_6182_, v_x_6183_);
lean_dec_ref(v_x_6183_);
lean_dec_ref(v_sep_6182_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6185_, lean_object* v_k_6186_){
_start:
{
lean_object* v_g_6187_; lean_object* v___x_6188_; 
v_g_6187_ = lean_ctor_get(v_t_6185_, 0);
lean_inc_ref(v_g_6187_);
lean_dec_ref(v_t_6185_);
v___x_6188_ = lean_apply_1(v_k_6186_, v_g_6187_);
return v___x_6188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6189_, lean_object* v_motive_6190_, lean_object* v_ctorIdx_6191_, lean_object* v_t_6192_, lean_object* v_h_6193_, lean_object* v_k_6194_){
_start:
{
lean_object* v___x_6195_; 
v___x_6195_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6192_, v_k_6194_);
return v___x_6195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6196_, lean_object* v_motive_6197_, lean_object* v_ctorIdx_6198_, lean_object* v_t_6199_, lean_object* v_h_6200_, lean_object* v_k_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim(v_sep_6196_, v_motive_6197_, v_ctorIdx_6198_, v_t_6199_, v_h_6200_, v_k_6201_);
lean_dec(v_ctorIdx_6198_);
lean_dec_ref(v_sep_6196_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6203_, lean_object* v_group_6204_){
_start:
{
lean_object* v___x_6205_; 
v___x_6205_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6203_, v_group_6204_);
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6206_, lean_object* v_motive_6207_, lean_object* v_t_6208_, lean_object* v_h_6209_, lean_object* v_group_6210_){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6208_, v_group_6210_);
return v___x_6211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6212_, lean_object* v_motive_6213_, lean_object* v_t_6214_, lean_object* v_h_6215_, lean_object* v_group_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_group_elim(v_sep_6212_, v_motive_6213_, v_t_6214_, v_h_6215_, v_group_6216_);
lean_dec_ref(v_sep_6212_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6218_, lean_object* v_trailing_6219_){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6218_, v_trailing_6219_);
return v___x_6220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6221_, lean_object* v_motive_6222_, lean_object* v_t_6223_, lean_object* v_h_6224_, lean_object* v_trailing_6225_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6223_, v_trailing_6225_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6227_, lean_object* v_motive_6228_, lean_object* v_t_6229_, lean_object* v_h_6230_, lean_object* v_trailing_6231_){
_start:
{
lean_object* v_res_6232_; 
v_res_6232_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6227_, v_motive_6228_, v_t_6229_, v_h_6230_, v_trailing_6231_);
lean_dec_ref(v_sep_6227_);
return v_res_6232_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6233_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6233_);
return v___x_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6235_){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6237_){
_start:
{
lean_object* v_res_6238_; 
v_res_6238_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6237_);
lean_dec_ref(v_sep_6237_);
return v_res_6238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6239_){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_a_6239_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6241_){
_start:
{
lean_object* v_res_6242_; 
v_res_6242_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedTrailingGroup(v_a_6241_);
lean_dec_ref(v_a_6241_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6243_, lean_object* v_elemsAndSeps_6244_, lean_object* v_pendingGroup_6245_, lean_object* v___x_6246_, lean_object* v_a_6247_, lean_object* v_b_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_){
_start:
{
lean_object* v_a_6252_; lean_object* v_a_6253_; uint8_t v___x_6257_; 
v___x_6257_ = lean_nat_dec_lt(v_a_6247_, v_upperBound_6243_);
if (v___x_6257_ == 0)
{
lean_object* v___x_6258_; 
lean_dec(v_a_6247_);
lean_dec_ref(v_pendingGroup_6245_);
v___x_6258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6258_, 0, v_b_6248_);
lean_ctor_set(v___x_6258_, 1, v___y_6250_);
return v___x_6258_;
}
else
{
lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6259_ = lean_array_fget_borrowed(v_elemsAndSeps_6244_, v_a_6247_);
lean_inc(v___x_6259_);
v___x_6260_ = l_Lean_Fmt_fmt(v___x_6259_, v___y_6249_, v___y_6250_);
if (lean_obj_tag(v___x_6260_) == 0)
{
lean_object* v_a_6261_; lean_object* v_a_6262_; lean_object* v_fst_6263_; lean_object* v_snd_6264_; lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6313_; 
v_a_6261_ = lean_ctor_get(v___x_6260_, 0);
lean_inc(v_a_6261_);
v_a_6262_ = lean_ctor_get(v___x_6260_, 1);
lean_inc(v_a_6262_);
lean_dec_ref_known(v___x_6260_, 2);
v_fst_6263_ = lean_ctor_get(v_b_6248_, 0);
v_snd_6264_ = lean_ctor_get(v_b_6248_, 1);
v_isSharedCheck_6313_ = !lean_is_exclusive(v_b_6248_);
if (v_isSharedCheck_6313_ == 0)
{
v___x_6266_ = v_b_6248_;
v_isShared_6267_ = v_isSharedCheck_6313_;
goto v_resetjp_6265_;
}
else
{
lean_inc(v_snd_6264_);
lean_inc(v_fst_6263_);
lean_dec(v_b_6248_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6313_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___y_6271_; lean_object* v___y_6297_; uint8_t v___y_6298_; uint8_t v___y_6305_; lean_object* v___x_6309_; lean_object* v___x_6310_; uint8_t v___x_6311_; 
v___x_6268_ = lean_unsigned_to_nat(0u);
v___x_6269_ = lean_array_push(v_snd_6264_, v_a_6261_);
v___x_6309_ = lean_unsigned_to_nat(2u);
v___x_6310_ = lean_nat_mod(v_a_6247_, v___x_6309_);
v___x_6311_ = lean_nat_dec_eq(v___x_6310_, v___x_6268_);
lean_dec(v___x_6310_);
if (v___x_6311_ == 0)
{
v___y_6305_ = v___x_6257_;
goto v___jp_6304_;
}
else
{
uint8_t v___x_6312_; 
v___x_6312_ = 0;
v___y_6305_ = v___x_6312_;
goto v___jp_6304_;
}
v___jp_6270_:
{
uint8_t v___x_6272_; lean_object* v___x_6273_; 
v___x_6272_ = 0;
v___x_6273_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_6271_, v___x_6272_, v___y_6249_, v_a_6262_);
if (lean_obj_tag(v___x_6273_) == 0)
{
lean_object* v_a_6274_; lean_object* v_a_6275_; uint8_t v___x_6276_; 
v_a_6274_ = lean_ctor_get(v___x_6273_, 0);
lean_inc(v_a_6274_);
v_a_6275_ = lean_ctor_get(v___x_6273_, 1);
lean_inc(v_a_6275_);
lean_dec_ref_known(v___x_6273_, 2);
v___x_6276_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_6274_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6282_; 
v___x_6277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6277_, 0, v___x_6269_);
v___x_6278_ = lean_array_push(v_fst_6263_, v___x_6277_);
v___x_6279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6279_, 0, v_a_6274_);
v___x_6280_ = lean_array_push(v___x_6278_, v___x_6279_);
lean_inc_ref(v_pendingGroup_6245_);
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 1, v_pendingGroup_6245_);
lean_ctor_set(v___x_6266_, 0, v___x_6280_);
v___x_6282_ = v___x_6266_;
goto v_reusejp_6281_;
}
else
{
lean_object* v_reuseFailAlloc_6283_; 
v_reuseFailAlloc_6283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6283_, 0, v___x_6280_);
lean_ctor_set(v_reuseFailAlloc_6283_, 1, v_pendingGroup_6245_);
v___x_6282_ = v_reuseFailAlloc_6283_;
goto v_reusejp_6281_;
}
v_reusejp_6281_:
{
v_a_6252_ = v___x_6282_;
v_a_6253_ = v_a_6275_;
goto v___jp_6251_;
}
}
else
{
lean_object* v___x_6285_; 
lean_dec(v_a_6274_);
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 1, v___x_6269_);
v___x_6285_ = v___x_6266_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v_fst_6263_);
lean_ctor_set(v_reuseFailAlloc_6286_, 1, v___x_6269_);
v___x_6285_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
v_a_6252_ = v___x_6285_;
v_a_6253_ = v_a_6275_;
goto v___jp_6251_;
}
}
}
else
{
lean_object* v_a_6287_; lean_object* v_a_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6295_; 
lean_dec_ref(v___x_6269_);
lean_del_object(v___x_6266_);
lean_dec(v_fst_6263_);
lean_dec(v_a_6247_);
lean_dec_ref(v_pendingGroup_6245_);
v_a_6287_ = lean_ctor_get(v___x_6273_, 0);
v_a_6288_ = lean_ctor_get(v___x_6273_, 1);
v_isSharedCheck_6295_ = !lean_is_exclusive(v___x_6273_);
if (v_isSharedCheck_6295_ == 0)
{
v___x_6290_ = v___x_6273_;
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
else
{
lean_inc(v_a_6288_);
lean_inc(v_a_6287_);
lean_dec(v___x_6273_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6293_; 
if (v_isShared_6291_ == 0)
{
v___x_6293_ = v___x_6290_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_a_6287_);
lean_ctor_set(v_reuseFailAlloc_6294_, 1, v_a_6288_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
}
}
v___jp_6296_:
{
if (v___y_6298_ == 0)
{
lean_object* v___x_6299_; 
lean_del_object(v___x_6266_);
v___x_6299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6299_, 0, v_fst_6263_);
lean_ctor_set(v___x_6299_, 1, v___x_6269_);
v_a_6252_ = v___x_6299_;
v_a_6253_ = v_a_6262_;
goto v___jp_6251_;
}
else
{
uint8_t v___x_6300_; 
lean_inc(v___x_6259_);
v___x_6300_ = l_Lean_Syntax_matchesNull(v___x_6259_, v___x_6268_);
if (v___x_6300_ == 0)
{
lean_inc(v___x_6259_);
v___y_6271_ = v___x_6259_;
goto v___jp_6270_;
}
else
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6301_ = lean_box(0);
v___x_6302_ = lean_nat_sub(v_a_6247_, v___y_6297_);
v___x_6303_ = lean_array_get_borrowed(v___x_6301_, v_elemsAndSeps_6244_, v___x_6302_);
lean_dec(v___x_6302_);
lean_inc(v___x_6303_);
v___y_6271_ = v___x_6303_;
goto v___jp_6270_;
}
}
}
v___jp_6304_:
{
lean_object* v___x_6306_; lean_object* v___x_6307_; uint8_t v___x_6308_; 
v___x_6306_ = lean_unsigned_to_nat(1u);
v___x_6307_ = lean_nat_sub(v___x_6246_, v___x_6306_);
v___x_6308_ = lean_nat_dec_lt(v_a_6247_, v___x_6307_);
lean_dec(v___x_6307_);
if (v___x_6308_ == 0)
{
v___y_6297_ = v___x_6306_;
v___y_6298_ = v___x_6308_;
goto v___jp_6296_;
}
else
{
v___y_6297_ = v___x_6306_;
v___y_6298_ = v___y_6305_;
goto v___jp_6296_;
}
}
}
}
else
{
lean_object* v_a_6314_; lean_object* v_a_6315_; lean_object* v___x_6317_; uint8_t v_isShared_6318_; uint8_t v_isSharedCheck_6322_; 
lean_dec_ref(v_b_6248_);
lean_dec(v_a_6247_);
lean_dec_ref(v_pendingGroup_6245_);
v_a_6314_ = lean_ctor_get(v___x_6260_, 0);
v_a_6315_ = lean_ctor_get(v___x_6260_, 1);
v_isSharedCheck_6322_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6322_ == 0)
{
v___x_6317_ = v___x_6260_;
v_isShared_6318_ = v_isSharedCheck_6322_;
goto v_resetjp_6316_;
}
else
{
lean_inc(v_a_6315_);
lean_inc(v_a_6314_);
lean_dec(v___x_6260_);
v___x_6317_ = lean_box(0);
v_isShared_6318_ = v_isSharedCheck_6322_;
goto v_resetjp_6316_;
}
v_resetjp_6316_:
{
lean_object* v___x_6320_; 
if (v_isShared_6318_ == 0)
{
v___x_6320_ = v___x_6317_;
goto v_reusejp_6319_;
}
else
{
lean_object* v_reuseFailAlloc_6321_; 
v_reuseFailAlloc_6321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6321_, 0, v_a_6314_);
lean_ctor_set(v_reuseFailAlloc_6321_, 1, v_a_6315_);
v___x_6320_ = v_reuseFailAlloc_6321_;
goto v_reusejp_6319_;
}
v_reusejp_6319_:
{
return v___x_6320_;
}
}
}
}
v___jp_6251_:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6254_ = lean_unsigned_to_nat(1u);
v___x_6255_ = lean_nat_add(v_a_6247_, v___x_6254_);
lean_dec(v_a_6247_);
v_a_6247_ = v___x_6255_;
v_b_6248_ = v_a_6252_;
v___y_6250_ = v_a_6253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_6323_, lean_object* v_elemsAndSeps_6324_, lean_object* v_pendingGroup_6325_, lean_object* v___x_6326_, lean_object* v_a_6327_, lean_object* v_b_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_){
_start:
{
lean_object* v_res_6331_; 
v_res_6331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_6323_, v_elemsAndSeps_6324_, v_pendingGroup_6325_, v___x_6326_, v_a_6327_, v_b_6328_, v___y_6329_, v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec(v___x_6326_);
lean_dec_ref(v_elemsAndSeps_6324_);
lean_dec(v_upperBound_6323_);
return v_res_6331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_6336_, lean_object* v_stxs_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v_acc_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6340_ = lean_unsigned_to_nat(0u);
v___x_6341_ = lean_array_get_size(v_stxs_6337_);
v_acc_6342_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_6343_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_6344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_6341_, v_stxs_6337_, v_acc_6342_, v___x_6341_, v___x_6340_, v___x_6343_, v_a_6338_, v_a_6339_);
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; lean_object* v_a_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6362_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
v_a_6346_ = lean_ctor_get(v___x_6344_, 1);
v_isSharedCheck_6362_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6362_ == 0)
{
v___x_6348_ = v___x_6344_;
v_isShared_6349_ = v_isSharedCheck_6362_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_a_6346_);
lean_inc(v_a_6345_);
lean_dec(v___x_6344_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6362_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v_fst_6350_; lean_object* v_snd_6351_; lean_object* v___x_6352_; uint8_t v___x_6353_; 
v_fst_6350_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_fst_6350_);
v_snd_6351_ = lean_ctor_get(v_a_6345_, 1);
lean_inc(v_snd_6351_);
lean_dec(v_a_6345_);
v___x_6352_ = lean_array_get_size(v_snd_6351_);
v___x_6353_ = lean_nat_dec_eq(v___x_6352_, v___x_6340_);
if (v___x_6353_ == 0)
{
lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6357_; 
v___x_6354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6354_, 0, v_snd_6351_);
v___x_6355_ = lean_array_push(v_fst_6350_, v___x_6354_);
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 0, v___x_6355_);
v___x_6357_ = v___x_6348_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6358_; 
v_reuseFailAlloc_6358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6358_, 0, v___x_6355_);
lean_ctor_set(v_reuseFailAlloc_6358_, 1, v_a_6346_);
v___x_6357_ = v_reuseFailAlloc_6358_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
return v___x_6357_;
}
}
else
{
lean_object* v___x_6360_; 
lean_dec(v_snd_6351_);
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 0, v_fst_6350_);
v___x_6360_ = v___x_6348_;
goto v_reusejp_6359_;
}
else
{
lean_object* v_reuseFailAlloc_6361_; 
v_reuseFailAlloc_6361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_fst_6350_);
lean_ctor_set(v_reuseFailAlloc_6361_, 1, v_a_6346_);
v___x_6360_ = v_reuseFailAlloc_6361_;
goto v_reusejp_6359_;
}
v_reusejp_6359_:
{
return v___x_6360_;
}
}
}
}
else
{
lean_object* v_a_6363_; lean_object* v_a_6364_; lean_object* v___x_6366_; uint8_t v_isShared_6367_; uint8_t v_isSharedCheck_6371_; 
v_a_6363_ = lean_ctor_get(v___x_6344_, 0);
v_a_6364_ = lean_ctor_get(v___x_6344_, 1);
v_isSharedCheck_6371_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6371_ == 0)
{
v___x_6366_ = v___x_6344_;
v_isShared_6367_ = v_isSharedCheck_6371_;
goto v_resetjp_6365_;
}
else
{
lean_inc(v_a_6364_);
lean_inc(v_a_6363_);
lean_dec(v___x_6344_);
v___x_6366_ = lean_box(0);
v_isShared_6367_ = v_isSharedCheck_6371_;
goto v_resetjp_6365_;
}
v_resetjp_6365_:
{
lean_object* v___x_6369_; 
if (v_isShared_6367_ == 0)
{
v___x_6369_ = v___x_6366_;
goto v_reusejp_6368_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v_a_6363_);
lean_ctor_set(v_reuseFailAlloc_6370_, 1, v_a_6364_);
v___x_6369_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6368_;
}
v_reusejp_6368_:
{
return v___x_6369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_6372_, lean_object* v_stxs_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_){
_start:
{
lean_object* v_res_6376_; 
v_res_6376_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6372_, v_stxs_6373_, v_a_6374_, v_a_6375_);
lean_dec_ref(v_a_6374_);
lean_dec_ref(v_stxs_6373_);
lean_dec_ref(v_sep_6372_);
return v_res_6376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_6377_, lean_object* v_sep_6378_, lean_object* v_stxs_6379_, lean_object* v_a_6380_, lean_object* v_a_6381_){
_start:
{
lean_object* v___x_6382_; 
v___x_6382_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6378_, v_stxs_6379_, v_a_6380_, v_a_6381_);
return v___x_6382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_6383_, lean_object* v_sep_6384_, lean_object* v_stxs_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_6383_, v_sep_6384_, v_stxs_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref(v_a_6386_);
lean_dec_ref(v_stxs_6385_);
lean_dec_ref(v_sep_6384_);
lean_dec(v_ks_6383_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_6389_, lean_object* v_elemsAndSeps_6390_, lean_object* v_sep_6391_, lean_object* v_pendingGroup_6392_, lean_object* v___x_6393_, lean_object* v_inst_6394_, lean_object* v_R_6395_, lean_object* v_a_6396_, lean_object* v_b_6397_, lean_object* v_c_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_){
_start:
{
lean_object* v___x_6401_; 
v___x_6401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_6389_, v_elemsAndSeps_6390_, v_pendingGroup_6392_, v___x_6393_, v_a_6396_, v_b_6397_, v___y_6399_, v___y_6400_);
return v___x_6401_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_6402_, lean_object* v_elemsAndSeps_6403_, lean_object* v_sep_6404_, lean_object* v_pendingGroup_6405_, lean_object* v___x_6406_, lean_object* v_inst_6407_, lean_object* v_R_6408_, lean_object* v_a_6409_, lean_object* v_b_6410_, lean_object* v_c_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_){
_start:
{
lean_object* v_res_6414_; 
v_res_6414_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_6402_, v_elemsAndSeps_6403_, v_sep_6404_, v_pendingGroup_6405_, v___x_6406_, v_inst_6407_, v_R_6408_, v_a_6409_, v_b_6410_, v_c_6411_, v___y_6412_, v___y_6413_);
lean_dec_ref(v___y_6412_);
lean_dec(v___x_6406_);
lean_dec_ref(v_sep_6404_);
lean_dec_ref(v_elemsAndSeps_6403_);
lean_dec(v_upperBound_6402_);
return v_res_6414_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6415_ = l_Lean_Fmt_TaggedDoc_space;
v___x_6416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6416_, 0, v___x_6415_);
return v___x_6416_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1(void){
_start:
{
uint8_t v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; 
v___x_6417_ = 2;
v___x_6418_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0);
v___x_6419_ = lean_box(0);
v___x_6420_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_6420_, 0, v___x_6419_);
lean_ctor_set(v___x_6420_, 1, v___x_6418_);
lean_ctor_set_uint8(v___x_6420_, sizeof(void*)*2, v___x_6417_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_6421_, size_t v_sz_6422_, size_t v_i_6423_, lean_object* v_bs_6424_){
_start:
{
uint8_t v___x_6425_; 
v___x_6425_ = lean_usize_dec_lt(v_i_6423_, v_sz_6422_);
if (v___x_6425_ == 0)
{
lean_dec_ref(v_sep_6421_);
return v_bs_6424_;
}
else
{
lean_object* v_v_6426_; lean_object* v___x_6427_; lean_object* v_bs_x27_6428_; lean_object* v___y_6430_; 
v_v_6426_ = lean_array_uget(v_bs_6424_, v_i_6423_);
v___x_6427_ = lean_unsigned_to_nat(0u);
v_bs_x27_6428_ = lean_array_uset(v_bs_6424_, v_i_6423_, v___x_6427_);
if (lean_obj_tag(v_v_6426_) == 0)
{
lean_object* v_g_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v_g_6435_ = lean_ctor_get(v_v_6426_, 0);
lean_inc_ref(v_g_6435_);
lean_dec_ref_known(v_v_6426_, 1);
v___x_6436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1);
lean_inc_ref(v_sep_6421_);
v___x_6437_ = l_Lean_Fmt_Layouts_sepArray(v_sep_6421_, v_g_6435_, v___x_6436_);
lean_dec_ref(v_g_6435_);
v___y_6430_ = v___x_6437_;
goto v___jp_6429_;
}
else
{
lean_object* v_t_6438_; 
v_t_6438_ = lean_ctor_get(v_v_6426_, 0);
lean_inc_ref(v_t_6438_);
lean_dec_ref_known(v_v_6426_, 1);
v___y_6430_ = v_t_6438_;
goto v___jp_6429_;
}
v___jp_6429_:
{
size_t v___x_6431_; size_t v___x_6432_; lean_object* v___x_6433_; 
v___x_6431_ = ((size_t)1ULL);
v___x_6432_ = lean_usize_add(v_i_6423_, v___x_6431_);
v___x_6433_ = lean_array_uset(v_bs_x27_6428_, v_i_6423_, v___y_6430_);
v_i_6423_ = v___x_6432_;
v_bs_6424_ = v___x_6433_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_6439_, lean_object* v_sz_6440_, lean_object* v_i_6441_, lean_object* v_bs_6442_){
_start:
{
size_t v_sz_boxed_6443_; size_t v_i_boxed_6444_; lean_object* v_res_6445_; 
v_sz_boxed_6443_ = lean_unbox_usize(v_sz_6440_);
lean_dec(v_sz_6440_);
v_i_boxed_6444_ = lean_unbox_usize(v_i_6441_);
lean_dec(v_i_6441_);
v_res_6445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_6439_, v_sz_boxed_6443_, v_i_boxed_6444_, v_bs_6442_);
return v_res_6445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_6446_, lean_object* v_stxs_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_){
_start:
{
lean_object* v___x_6450_; 
v___x_6450_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6446_, v_stxs_6447_, v_a_6448_, v_a_6449_);
if (lean_obj_tag(v___x_6450_) == 0)
{
lean_object* v_a_6451_; lean_object* v_a_6452_; lean_object* v___x_6454_; uint8_t v_isShared_6455_; uint8_t v_isSharedCheck_6463_; 
v_a_6451_ = lean_ctor_get(v___x_6450_, 0);
v_a_6452_ = lean_ctor_get(v___x_6450_, 1);
v_isSharedCheck_6463_ = !lean_is_exclusive(v___x_6450_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6454_ = v___x_6450_;
v_isShared_6455_ = v_isSharedCheck_6463_;
goto v_resetjp_6453_;
}
else
{
lean_inc(v_a_6452_);
lean_inc(v_a_6451_);
lean_dec(v___x_6450_);
v___x_6454_ = lean_box(0);
v_isShared_6455_ = v_isSharedCheck_6463_;
goto v_resetjp_6453_;
}
v_resetjp_6453_:
{
size_t v_sz_6456_; size_t v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6461_; 
v_sz_6456_ = lean_array_size(v_a_6451_);
v___x_6457_ = ((size_t)0ULL);
v___x_6458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_6446_, v_sz_6456_, v___x_6457_, v_a_6451_);
v___x_6459_ = l_Lean_Fmt_TaggedDoc_join(v___x_6458_);
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 0, v___x_6459_);
v___x_6461_ = v___x_6454_;
goto v_reusejp_6460_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6459_);
lean_ctor_set(v_reuseFailAlloc_6462_, 1, v_a_6452_);
v___x_6461_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6460_;
}
v_reusejp_6460_:
{
return v___x_6461_;
}
}
}
else
{
lean_object* v_a_6464_; lean_object* v_a_6465_; lean_object* v___x_6467_; uint8_t v_isShared_6468_; uint8_t v_isSharedCheck_6472_; 
lean_dec_ref(v_sep_6446_);
v_a_6464_ = lean_ctor_get(v___x_6450_, 0);
v_a_6465_ = lean_ctor_get(v___x_6450_, 1);
v_isSharedCheck_6472_ = !lean_is_exclusive(v___x_6450_);
if (v_isSharedCheck_6472_ == 0)
{
v___x_6467_ = v___x_6450_;
v_isShared_6468_ = v_isSharedCheck_6472_;
goto v_resetjp_6466_;
}
else
{
lean_inc(v_a_6465_);
lean_inc(v_a_6464_);
lean_dec(v___x_6450_);
v___x_6467_ = lean_box(0);
v_isShared_6468_ = v_isSharedCheck_6472_;
goto v_resetjp_6466_;
}
v_resetjp_6466_:
{
lean_object* v___x_6470_; 
if (v_isShared_6468_ == 0)
{
v___x_6470_ = v___x_6467_;
goto v_reusejp_6469_;
}
else
{
lean_object* v_reuseFailAlloc_6471_; 
v_reuseFailAlloc_6471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_a_6464_);
lean_ctor_set(v_reuseFailAlloc_6471_, 1, v_a_6465_);
v___x_6470_ = v_reuseFailAlloc_6471_;
goto v_reusejp_6469_;
}
v_reusejp_6469_:
{
return v___x_6470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_6473_, lean_object* v_stxs_6474_, lean_object* v_a_6475_, lean_object* v_a_6476_){
_start:
{
lean_object* v_res_6477_; 
v_res_6477_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_6473_, v_stxs_6474_, v_a_6475_, v_a_6476_);
lean_dec_ref(v_a_6475_);
lean_dec_ref(v_stxs_6474_);
return v_res_6477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_6478_, lean_object* v_sep_6479_, lean_object* v_stxs_6480_, lean_object* v_a_6481_, lean_object* v_a_6482_){
_start:
{
lean_object* v___x_6483_; 
v___x_6483_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_6479_, v_stxs_6480_, v_a_6481_, v_a_6482_);
return v___x_6483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_6484_, lean_object* v_sep_6485_, lean_object* v_stxs_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_){
_start:
{
lean_object* v_res_6489_; 
v_res_6489_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_6484_, v_sep_6485_, v_stxs_6486_, v_a_6487_, v_a_6488_);
lean_dec_ref(v_a_6487_);
lean_dec_ref(v_stxs_6486_);
lean_dec(v_ks_6484_);
return v_res_6489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0(size_t v_sz_6491_, size_t v_i_6492_, lean_object* v_bs_6493_){
_start:
{
uint8_t v___x_6494_; 
v___x_6494_ = lean_usize_dec_lt(v_i_6492_, v_sz_6491_);
if (v___x_6494_ == 0)
{
return v_bs_6493_;
}
else
{
lean_object* v_v_6495_; lean_object* v___x_6496_; lean_object* v_bs_x27_6497_; lean_object* v___y_6499_; 
v_v_6495_ = lean_array_uget(v_bs_6493_, v_i_6492_);
v___x_6496_ = lean_unsigned_to_nat(0u);
v_bs_x27_6497_ = lean_array_uset(v_bs_6493_, v_i_6492_, v___x_6496_);
if (lean_obj_tag(v_v_6495_) == 0)
{
lean_object* v_g_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; 
v_g_6504_ = lean_ctor_get(v_v_6495_, 0);
lean_inc_ref(v_g_6504_);
lean_dec_ref_known(v_v_6495_, 1);
v___x_6505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___closed__0));
v___x_6506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__1);
v___x_6507_ = l_Lean_Fmt_Layouts_sepArray(v___x_6505_, v_g_6504_, v___x_6506_);
lean_dec_ref(v_g_6504_);
v___y_6499_ = v___x_6507_;
goto v___jp_6498_;
}
else
{
lean_object* v_t_6508_; 
v_t_6508_ = lean_ctor_get(v_v_6495_, 0);
lean_inc_ref(v_t_6508_);
lean_dec_ref_known(v_v_6495_, 1);
v___y_6499_ = v_t_6508_;
goto v___jp_6498_;
}
v___jp_6498_:
{
size_t v___x_6500_; size_t v___x_6501_; lean_object* v___x_6502_; 
v___x_6500_ = ((size_t)1ULL);
v___x_6501_ = lean_usize_add(v_i_6492_, v___x_6500_);
v___x_6502_ = lean_array_uset(v_bs_x27_6497_, v_i_6492_, v___y_6499_);
v_i_6492_ = v___x_6501_;
v_bs_6493_ = v___x_6502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___boxed(lean_object* v_sz_6509_, lean_object* v_i_6510_, lean_object* v_bs_6511_){
_start:
{
size_t v_sz_boxed_6512_; size_t v_i_boxed_6513_; lean_object* v_res_6514_; 
v_sz_boxed_6512_ = lean_unbox_usize(v_sz_6509_);
lean_dec(v_sz_6509_);
v_i_boxed_6513_ = lean_unbox_usize(v_i_6510_);
lean_dec(v_i_6510_);
v_res_6514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0(v_sz_boxed_6512_, v_i_boxed_6513_, v_bs_6511_);
return v_res_6514_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtArrayLit___redArg___closed__0(void){
_start:
{
uint8_t v___x_6515_; uint8_t v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; 
v___x_6515_ = 0;
v___x_6516_ = 1;
v___x_6517_ = l_Lean_Fmt_TaggedDoc_break;
v___x_6518_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_6518_, 0, v___x_6517_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*1, v___x_6516_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*1 + 1, v___x_6515_);
return v___x_6518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object* v_lbTk_6519_, lean_object* v_elems_6520_, lean_object* v_rbTk_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_){
_start:
{
lean_object* v___x_6524_; 
v___x_6524_ = l_Lean_Fmt_fmt(v_lbTk_6519_, v_a_6522_, v_a_6523_);
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_object* v_a_6525_; lean_object* v_a_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; 
v_a_6525_ = lean_ctor_get(v___x_6524_, 0);
lean_inc(v_a_6525_);
v_a_6526_ = lean_ctor_get(v___x_6524_, 1);
lean_inc(v_a_6526_);
lean_dec_ref_known(v___x_6524_, 2);
v___x_6527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0___closed__0));
v___x_6528_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v___x_6527_, v_elems_6520_, v_a_6522_, v_a_6526_);
if (lean_obj_tag(v___x_6528_) == 0)
{
lean_object* v_a_6529_; lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6566_; 
v_a_6529_ = lean_ctor_get(v___x_6528_, 0);
v_a_6530_ = lean_ctor_get(v___x_6528_, 1);
v_isSharedCheck_6566_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6566_ == 0)
{
v___x_6532_ = v___x_6528_;
v_isShared_6533_ = v_isSharedCheck_6566_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_inc(v_a_6529_);
lean_dec(v___x_6528_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6566_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6534_; 
v___x_6534_ = l_Lean_Fmt_fmt(v_rbTk_6521_, v_a_6522_, v_a_6530_);
if (lean_obj_tag(v___x_6534_) == 0)
{
lean_object* v_a_6535_; lean_object* v_a_6536_; lean_object* v___x_6538_; uint8_t v_isShared_6539_; uint8_t v_isSharedCheck_6565_; 
v_a_6535_ = lean_ctor_get(v___x_6534_, 0);
v_a_6536_ = lean_ctor_get(v___x_6534_, 1);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6534_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6538_ = v___x_6534_;
v_isShared_6539_ = v_isSharedCheck_6565_;
goto v_resetjp_6537_;
}
else
{
lean_inc(v_a_6536_);
lean_inc(v_a_6535_);
lean_dec(v___x_6534_);
v___x_6538_ = lean_box(0);
v_isShared_6539_ = v_isSharedCheck_6565_;
goto v_resetjp_6537_;
}
v_resetjp_6537_:
{
lean_object* v___x_6550_; lean_object* v___x_6551_; uint8_t v___x_6552_; 
v___x_6550_ = lean_array_get_size(v_a_6529_);
v___x_6551_ = lean_unsigned_to_nat(1u);
v___x_6552_ = lean_nat_dec_eq(v___x_6550_, v___x_6551_);
if (v___x_6552_ == 0)
{
lean_del_object(v___x_6532_);
goto v___jp_6540_;
}
else
{
lean_object* v___x_6553_; lean_object* v___x_6554_; 
v___x_6553_ = lean_unsigned_to_nat(0u);
v___x_6554_ = lean_array_fget_borrowed(v_a_6529_, v___x_6553_);
if (lean_obj_tag(v___x_6554_) == 0)
{
lean_object* v_g_6555_; lean_object* v___x_6556_; uint8_t v___x_6557_; 
v_g_6555_ = lean_ctor_get(v___x_6554_, 0);
v___x_6556_ = lean_array_get_size(v_g_6555_);
v___x_6557_ = lean_nat_dec_eq(v___x_6556_, v___x_6551_);
if (v___x_6557_ == 0)
{
lean_del_object(v___x_6532_);
goto v___jp_6540_;
}
else
{
lean_object* v___x_6558_; uint8_t v___x_6559_; 
v___x_6558_ = lean_array_fget_borrowed(v_g_6555_, v___x_6553_);
lean_inc(v___x_6558_);
v___x_6559_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v___x_6558_);
if (v___x_6559_ == 0)
{
lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6563_; 
lean_inc(v___x_6558_);
lean_del_object(v___x_6538_);
lean_dec(v_a_6529_);
v___x_6560_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_6560_, 0, v___x_6559_);
v___x_6561_ = l_Lean_Fmt_Layouts_bracketed(v_a_6525_, v___x_6558_, v_a_6535_, v___x_6560_);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 1, v_a_6536_);
lean_ctor_set(v___x_6532_, 0, v___x_6561_);
v___x_6563_ = v___x_6532_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v___x_6561_);
lean_ctor_set(v_reuseFailAlloc_6564_, 1, v_a_6536_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
return v___x_6563_;
}
}
else
{
lean_del_object(v___x_6532_);
goto v___jp_6540_;
}
}
}
else
{
lean_del_object(v___x_6532_);
goto v___jp_6540_;
}
}
v___jp_6540_:
{
size_t v_sz_6541_; size_t v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6548_; 
v_sz_6541_ = lean_array_size(v_a_6529_);
v___x_6542_ = ((size_t)0ULL);
v___x_6543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayLit_spec__0(v_sz_6541_, v___x_6542_, v_a_6529_);
v___x_6544_ = l_Lean_Fmt_TaggedDoc_join(v___x_6543_);
v___x_6545_ = lean_obj_once(&l_Lean_Fmt_fmtArrayLit___redArg___closed__0, &l_Lean_Fmt_fmtArrayLit___redArg___closed__0_once, _init_l_Lean_Fmt_fmtArrayLit___redArg___closed__0);
v___x_6546_ = l_Lean_Fmt_Layouts_bracketed(v_a_6525_, v___x_6544_, v_a_6535_, v___x_6545_);
if (v_isShared_6539_ == 0)
{
lean_ctor_set(v___x_6538_, 0, v___x_6546_);
v___x_6548_ = v___x_6538_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v___x_6546_);
lean_ctor_set(v_reuseFailAlloc_6549_, 1, v_a_6536_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
}
else
{
lean_del_object(v___x_6532_);
lean_dec(v_a_6529_);
lean_dec(v_a_6525_);
return v___x_6534_;
}
}
}
else
{
lean_object* v_a_6567_; lean_object* v_a_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6575_; 
lean_dec(v_a_6525_);
lean_dec(v_rbTk_6521_);
v_a_6567_ = lean_ctor_get(v___x_6528_, 0);
v_a_6568_ = lean_ctor_get(v___x_6528_, 1);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6570_ = v___x_6528_;
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_a_6568_);
lean_inc(v_a_6567_);
lean_dec(v___x_6528_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v___x_6573_; 
if (v_isShared_6571_ == 0)
{
v___x_6573_ = v___x_6570_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v_a_6567_);
lean_ctor_set(v_reuseFailAlloc_6574_, 1, v_a_6568_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
}
else
{
lean_dec(v_rbTk_6521_);
return v___x_6524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___redArg___boxed(lean_object* v_lbTk_6576_, lean_object* v_elems_6577_, lean_object* v_rbTk_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_){
_start:
{
lean_object* v_res_6581_; 
v_res_6581_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_6576_, v_elems_6577_, v_rbTk_6578_, v_a_6579_, v_a_6580_);
lean_dec_ref(v_a_6579_);
lean_dec_ref(v_elems_6577_);
return v_res_6581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit(lean_object* v_ks_6582_, lean_object* v_lbTk_6583_, lean_object* v_elems_6584_, lean_object* v_rbTk_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_){
_start:
{
lean_object* v___x_6588_; 
v___x_6588_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_6583_, v_elems_6584_, v_rbTk_6585_, v_a_6586_, v_a_6587_);
return v___x_6588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayLit___boxed(lean_object* v_ks_6589_, lean_object* v_lbTk_6590_, lean_object* v_elems_6591_, lean_object* v_rbTk_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Lean_Fmt_fmtArrayLit(v_ks_6589_, v_lbTk_6590_, v_elems_6591_, v_rbTk_6592_, v_a_6593_, v_a_6594_);
lean_dec_ref(v_a_6593_);
lean_dec_ref(v_elems_6591_);
lean_dec(v_ks_6589_);
return v_res_6595_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0(lean_object* v_sep_6596_, lean_object* v_msg_6597_){
_start:
{
lean_object* v___x_6598_; lean_object* v___x_6599_; 
v___x_6598_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6596_);
v___x_6599_ = lean_panic_fn_borrowed(v___x_6598_, v_msg_6597_);
lean_dec_ref(v___x_6598_);
return v___x_6599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0___boxed(lean_object* v_sep_6600_, lean_object* v_msg_6601_){
_start:
{
lean_object* v_res_6602_; 
v_res_6602_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0(v_sep_6600_, v_msg_6601_);
lean_dec_ref(v_sep_6600_);
return v_res_6602_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; 
v___x_6607_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_6608_ = lean_unsigned_to_nat(15u);
v___x_6609_ = lean_unsigned_to_nat(928u);
v___x_6610_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__1));
v___x_6611_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_6612_ = l_mkPanicMessageWithDecl(v___x_6611_, v___x_6610_, v___x_6609_, v___x_6608_, v___x_6607_);
return v___x_6612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg(lean_object* v_upperBound_6613_, lean_object* v___x_6614_, lean_object* v_sep_6615_, lean_object* v_groups_6616_, lean_object* v_a_6617_, lean_object* v_b_6618_){
_start:
{
uint8_t v___x_6619_; 
v___x_6619_ = lean_nat_dec_lt(v_a_6617_, v_upperBound_6613_);
if (v___x_6619_ == 0)
{
lean_dec(v_a_6617_);
lean_dec_ref(v_groups_6616_);
lean_inc_ref(v_b_6618_);
return v_b_6618_;
}
else
{
lean_object* v___x_6620_; lean_object* v___y_6622_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___y_6631_; lean_object* v___y_6632_; lean_object* v___x_6634_; 
v___x_6620_ = lean_box(0);
v___x_6625_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6615_);
v___x_6626_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__0));
v___x_6627_ = lean_nat_sub(v___x_6614_, v_a_6617_);
v___x_6628_ = lean_unsigned_to_nat(1u);
v___x_6629_ = lean_nat_sub(v___x_6627_, v___x_6628_);
lean_dec(v___x_6627_);
v___x_6634_ = lean_array_get(v___x_6625_, v_groups_6616_, v___x_6629_);
lean_dec_ref(v___x_6625_);
if (lean_obj_tag(v___x_6634_) == 0)
{
lean_object* v_g_6635_; lean_object* v___x_6636_; lean_object* v___y_6638_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; uint8_t v___x_6661_; 
lean_dec(v_a_6617_);
v_g_6635_ = lean_ctor_get(v___x_6634_, 0);
lean_inc_ref(v_g_6635_);
lean_dec_ref_known(v___x_6634_, 1);
v___x_6636_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6657_ = lean_unsigned_to_nat(0u);
v___x_6658_ = lean_array_get_size(v_g_6635_);
v___x_6659_ = lean_unsigned_to_nat(2u);
v___x_6660_ = lean_nat_mod(v___x_6658_, v___x_6659_);
v___x_6661_ = lean_nat_dec_eq(v___x_6660_, v___x_6657_);
lean_dec(v___x_6660_);
if (v___x_6661_ == 0)
{
lean_object* v___x_6662_; 
v___x_6662_ = lean_nat_sub(v___x_6658_, v___x_6628_);
v___y_6638_ = v___x_6662_;
goto v___jp_6637_;
}
else
{
lean_object* v___x_6663_; 
v___x_6663_ = lean_nat_sub(v___x_6658_, v___x_6659_);
v___y_6638_ = v___x_6663_;
goto v___jp_6637_;
}
v___jp_6637_:
{
lean_object* v___x_6639_; lean_object* v___x_6640_; 
v___x_6639_ = lean_array_get(v___x_6636_, v_g_6635_, v___y_6638_);
lean_dec_ref(v_g_6635_);
v___x_6640_ = l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(v___x_6639_);
if (lean_obj_tag(v___x_6640_) == 1)
{
lean_object* v_val_6641_; lean_object* v___x_6642_; uint8_t v___x_6643_; 
v_val_6641_ = lean_ctor_get(v___x_6640_, 0);
lean_inc(v_val_6641_);
lean_dec_ref_known(v___x_6640_, 1);
v___x_6642_ = lean_array_get_size(v_groups_6616_);
v___x_6643_ = lean_nat_dec_lt(v___x_6629_, v___x_6642_);
if (v___x_6643_ == 0)
{
lean_dec(v_val_6641_);
lean_dec(v___y_6638_);
lean_dec(v___x_6629_);
v___y_6622_ = v_groups_6616_;
goto v___jp_6621_;
}
else
{
lean_object* v_v_6644_; lean_object* v_xs_x27_6645_; 
v_v_6644_ = lean_array_fget(v_groups_6616_, v___x_6629_);
v_xs_x27_6645_ = lean_array_fset(v_groups_6616_, v___x_6629_, v___x_6620_);
if (lean_obj_tag(v_v_6644_) == 0)
{
lean_object* v_g_6646_; lean_object* v___x_6648_; uint8_t v_isShared_6649_; uint8_t v_isSharedCheck_6654_; 
v_g_6646_ = lean_ctor_get(v_v_6644_, 0);
v_isSharedCheck_6654_ = !lean_is_exclusive(v_v_6644_);
if (v_isSharedCheck_6654_ == 0)
{
v___x_6648_ = v_v_6644_;
v_isShared_6649_ = v_isSharedCheck_6654_;
goto v_resetjp_6647_;
}
else
{
lean_inc(v_g_6646_);
lean_dec(v_v_6644_);
v___x_6648_ = lean_box(0);
v_isShared_6649_ = v_isSharedCheck_6654_;
goto v_resetjp_6647_;
}
v_resetjp_6647_:
{
lean_object* v___x_6650_; lean_object* v___x_6652_; 
v___x_6650_ = lean_array_set(v_g_6646_, v___y_6638_, v_val_6641_);
lean_dec(v___y_6638_);
if (v_isShared_6649_ == 0)
{
lean_ctor_set(v___x_6648_, 0, v___x_6650_);
v___x_6652_ = v___x_6648_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6650_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
v___y_6631_ = v_xs_x27_6645_;
v___y_6632_ = v___x_6652_;
goto v___jp_6630_;
}
}
}
else
{
lean_object* v___x_6655_; lean_object* v___x_6656_; 
lean_dec(v_v_6644_);
lean_dec(v_val_6641_);
lean_dec(v___y_6638_);
v___x_6655_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__2);
v___x_6656_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__0(v_sep_6615_, v___x_6655_);
v___y_6631_ = v_xs_x27_6645_;
v___y_6632_ = v___x_6656_;
goto v___jp_6630_;
}
}
}
else
{
lean_dec(v___x_6640_);
lean_dec(v___y_6638_);
lean_dec(v___x_6629_);
lean_dec_ref(v_groups_6616_);
return v___x_6626_;
}
}
}
else
{
lean_object* v___x_6664_; 
lean_dec(v___x_6634_);
lean_dec(v___x_6629_);
v___x_6664_ = lean_nat_add(v_a_6617_, v___x_6628_);
lean_dec(v_a_6617_);
v_a_6617_ = v___x_6664_;
v_b_6618_ = v___x_6626_;
goto _start;
}
v___jp_6621_:
{
lean_object* v___x_6623_; lean_object* v___x_6624_; 
v___x_6623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6623_, 0, v___y_6622_);
v___x_6624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6623_);
lean_ctor_set(v___x_6624_, 1, v___x_6620_);
return v___x_6624_;
}
v___jp_6630_:
{
lean_object* v___x_6633_; 
v___x_6633_ = lean_array_fset(v___y_6631_, v___x_6629_, v___y_6632_);
lean_dec(v___x_6629_);
v___y_6622_ = v___x_6633_;
goto v___jp_6621_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___boxed(lean_object* v_upperBound_6666_, lean_object* v___x_6667_, lean_object* v_sep_6668_, lean_object* v_groups_6669_, lean_object* v_a_6670_, lean_object* v_b_6671_){
_start:
{
lean_object* v_res_6672_; 
v_res_6672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg(v_upperBound_6666_, v___x_6667_, v_sep_6668_, v_groups_6669_, v_a_6670_, v_b_6671_);
lean_dec_ref(v_b_6671_);
lean_dec_ref(v_sep_6668_);
lean_dec(v___x_6667_);
lean_dec(v_upperBound_6666_);
return v_res_6672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented(lean_object* v_sep_6673_, lean_object* v_groups_6674_){
_start:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v_fst_6679_; 
v___x_6675_ = lean_unsigned_to_nat(0u);
v___x_6676_ = lean_array_get_size(v_groups_6674_);
v___x_6677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg___closed__0));
lean_inc_ref(v_groups_6674_);
v___x_6678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg(v___x_6676_, v___x_6676_, v_sep_6673_, v_groups_6674_, v___x_6675_, v___x_6677_);
v_fst_6679_ = lean_ctor_get(v___x_6678_, 0);
lean_inc(v_fst_6679_);
lean_dec_ref(v___x_6678_);
if (lean_obj_tag(v_fst_6679_) == 0)
{
return v_groups_6674_;
}
else
{
lean_object* v_val_6680_; 
lean_dec_ref(v_groups_6674_);
v_val_6680_ = lean_ctor_get(v_fst_6679_, 0);
lean_inc(v_val_6680_);
lean_dec_ref_known(v_fst_6679_, 1);
return v_val_6680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented___boxed(lean_object* v_sep_6681_, lean_object* v_groups_6682_){
_start:
{
lean_object* v_res_6683_; 
v_res_6683_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented(v_sep_6681_, v_groups_6682_);
lean_dec_ref(v_sep_6681_);
return v_res_6683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1(lean_object* v_upperBound_6684_, lean_object* v___x_6685_, lean_object* v_sep_6686_, lean_object* v_groups_6687_, lean_object* v_inst_6688_, lean_object* v_R_6689_, lean_object* v_a_6690_, lean_object* v_b_6691_, lean_object* v_c_6692_){
_start:
{
lean_object* v___x_6693_; 
v___x_6693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___redArg(v_upperBound_6684_, v___x_6685_, v_sep_6686_, v_groups_6687_, v_a_6690_, v_b_6691_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1___boxed(lean_object* v_upperBound_6694_, lean_object* v___x_6695_, lean_object* v_sep_6696_, lean_object* v_groups_6697_, lean_object* v_inst_6698_, lean_object* v_R_6699_, lean_object* v_a_6700_, lean_object* v_b_6701_, lean_object* v_c_6702_){
_start:
{
lean_object* v_res_6703_; 
v_res_6703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented_spec__1(v_upperBound_6694_, v___x_6695_, v_sep_6696_, v_groups_6697_, v_inst_6698_, v_R_6699_, v_a_6700_, v_b_6701_, v_c_6702_);
lean_dec_ref(v_b_6701_);
lean_dec_ref(v_sep_6696_);
lean_dec(v___x_6695_);
lean_dec(v_upperBound_6694_);
return v_res_6703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0(lean_object* v_sep_6704_, size_t v_sz_6705_, size_t v_i_6706_, lean_object* v_bs_6707_){
_start:
{
uint8_t v___x_6708_; 
v___x_6708_ = lean_usize_dec_lt(v_i_6706_, v_sz_6705_);
if (v___x_6708_ == 0)
{
lean_dec_ref(v_sep_6704_);
return v_bs_6707_;
}
else
{
lean_object* v_v_6709_; lean_object* v___x_6710_; lean_object* v_bs_x27_6711_; lean_object* v___y_6713_; 
v_v_6709_ = lean_array_uget(v_bs_6707_, v_i_6706_);
v___x_6710_ = lean_unsigned_to_nat(0u);
v_bs_x27_6711_ = lean_array_uset(v_bs_6707_, v_i_6706_, v___x_6710_);
if (lean_obj_tag(v_v_6709_) == 0)
{
lean_object* v_g_6718_; uint8_t v___x_6719_; lean_object* v___x_6720_; 
v_g_6718_ = lean_ctor_get(v_v_6709_, 0);
lean_inc_ref(v_g_6718_);
lean_dec_ref_known(v_v_6709_, 1);
v___x_6719_ = 0;
lean_inc_ref(v_sep_6704_);
v___x_6720_ = l_Lean_Fmt_Layouts_sepLines(v_sep_6704_, v_g_6718_, v___x_6719_);
lean_dec_ref(v_g_6718_);
v___y_6713_ = v___x_6720_;
goto v___jp_6712_;
}
else
{
lean_object* v_t_6721_; 
v_t_6721_ = lean_ctor_get(v_v_6709_, 0);
lean_inc_ref(v_t_6721_);
lean_dec_ref_known(v_v_6709_, 1);
v___y_6713_ = v_t_6721_;
goto v___jp_6712_;
}
v___jp_6712_:
{
size_t v___x_6714_; size_t v___x_6715_; lean_object* v___x_6716_; 
v___x_6714_ = ((size_t)1ULL);
v___x_6715_ = lean_usize_add(v_i_6706_, v___x_6714_);
v___x_6716_ = lean_array_uset(v_bs_x27_6711_, v_i_6706_, v___y_6713_);
v_i_6706_ = v___x_6715_;
v_bs_6707_ = v___x_6716_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0___boxed(lean_object* v_sep_6722_, lean_object* v_sz_6723_, lean_object* v_i_6724_, lean_object* v_bs_6725_){
_start:
{
size_t v_sz_boxed_6726_; size_t v_i_boxed_6727_; lean_object* v_res_6728_; 
v_sz_boxed_6726_ = lean_unbox_usize(v_sz_6723_);
lean_dec(v_sz_6723_);
v_i_boxed_6727_ = lean_unbox_usize(v_i_6724_);
lean_dec(v_i_6724_);
v_res_6728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0(v_sep_6722_, v_sz_boxed_6726_, v_i_boxed_6727_, v_bs_6725_);
return v_res_6728_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSeq___redArg___closed__0(void){
_start:
{
uint8_t v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; 
v___x_6729_ = 1;
v___x_6730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0);
v___x_6731_ = lean_box(0);
v___x_6732_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_6732_, 0, v___x_6731_);
lean_ctor_set(v___x_6732_, 1, v___x_6730_);
lean_ctor_set_uint8(v___x_6732_, sizeof(void*)*2, v___x_6729_);
return v___x_6732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object* v_sep_6733_, lean_object* v_seq_6734_, lean_object* v_nestedKind_x3f_6735_, lean_object* v_a_6736_, lean_object* v_a_6737_){
_start:
{
lean_object* v_r_6739_; lean_object* v___y_6740_; lean_object* v___y_6744_; lean_object* v___y_6745_; 
if (lean_obj_tag(v_nestedKind_x3f_6735_) == 1)
{
lean_object* v_val_6778_; lean_object* v___x_6779_; lean_object* v_seqElems_6780_; uint8_t v___y_6782_; lean_object* v___x_6786_; lean_object* v___x_6787_; uint8_t v___x_6788_; 
v_val_6778_ = lean_ctor_get(v_nestedKind_x3f_6735_, 0);
v___x_6779_ = lean_box(0);
v_seqElems_6780_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_seq_6734_);
v___x_6786_ = lean_array_get_size(v_seqElems_6780_);
v___x_6787_ = lean_unsigned_to_nat(1u);
v___x_6788_ = lean_nat_dec_eq(v___x_6786_, v___x_6787_);
if (v___x_6788_ == 0)
{
v___y_6782_ = v___x_6788_;
goto v___jp_6781_;
}
else
{
lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; uint8_t v___x_6792_; 
v___x_6789_ = lean_unsigned_to_nat(0u);
v___x_6790_ = lean_array_get(v___x_6779_, v_seqElems_6780_, v___x_6789_);
v___x_6791_ = l_Lean_Syntax_getKind(v___x_6790_);
v___x_6792_ = lean_name_eq(v___x_6791_, v_val_6778_);
lean_dec(v___x_6791_);
v___y_6782_ = v___x_6792_;
goto v___jp_6781_;
}
v___jp_6781_:
{
if (v___y_6782_ == 0)
{
lean_dec_ref(v_seqElems_6780_);
v___y_6744_ = v_a_6736_;
v___y_6745_ = v_a_6737_;
goto v___jp_6743_;
}
else
{
lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; 
lean_dec_ref(v_sep_6733_);
v___x_6783_ = lean_unsigned_to_nat(0u);
v___x_6784_ = lean_array_get(v___x_6779_, v_seqElems_6780_, v___x_6783_);
lean_dec_ref(v_seqElems_6780_);
v___x_6785_ = l_Lean_Fmt_fmt(v___x_6784_, v_a_6736_, v_a_6737_);
return v___x_6785_;
}
}
}
else
{
v___y_6744_ = v_a_6736_;
v___y_6745_ = v_a_6737_;
goto v___jp_6743_;
}
v___jp_6738_:
{
lean_object* v___x_6741_; lean_object* v___x_6742_; 
v___x_6741_ = l_Lean_Fmt_TaggedDoc_withPosition(v_r_6739_);
v___x_6742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6742_, 0, v___x_6741_);
lean_ctor_set(v___x_6742_, 1, v___y_6740_);
return v___x_6742_;
}
v___jp_6743_:
{
lean_object* v___x_6746_; 
v___x_6746_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6733_, v_seq_6734_, v___y_6744_, v___y_6745_);
if (lean_obj_tag(v___x_6746_) == 0)
{
lean_object* v_a_6747_; lean_object* v_a_6748_; lean_object* v___x_6749_; size_t v_sz_6750_; size_t v___x_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; uint8_t v___x_6756_; 
v_a_6747_ = lean_ctor_get(v___x_6746_, 0);
lean_inc(v_a_6747_);
v_a_6748_ = lean_ctor_get(v___x_6746_, 1);
lean_inc(v_a_6748_);
lean_dec_ref_known(v___x_6746_, 2);
v___x_6749_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtSeq_applyPseudoDedented(v_sep_6733_, v_a_6747_);
v_sz_6750_ = lean_array_size(v___x_6749_);
v___x_6751_ = ((size_t)0ULL);
lean_inc_ref(v___x_6749_);
lean_inc_ref(v_sep_6733_);
v___x_6752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSeq_spec__0(v_sep_6733_, v_sz_6750_, v___x_6751_, v___x_6749_);
v___x_6753_ = l_Lean_Fmt_TaggedDoc_join(v___x_6752_);
v___x_6754_ = lean_array_get_size(v___x_6749_);
v___x_6755_ = lean_unsigned_to_nat(1u);
v___x_6756_ = lean_nat_dec_eq(v___x_6754_, v___x_6755_);
if (v___x_6756_ == 0)
{
lean_dec_ref(v___x_6749_);
lean_dec_ref(v_sep_6733_);
v_r_6739_ = v___x_6753_;
v___y_6740_ = v_a_6748_;
goto v___jp_6738_;
}
else
{
lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; 
v___x_6757_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6733_);
v___x_6758_ = lean_unsigned_to_nat(0u);
v___x_6759_ = lean_array_get(v___x_6757_, v___x_6749_, v___x_6758_);
lean_dec_ref(v___x_6749_);
lean_dec_ref(v___x_6757_);
if (lean_obj_tag(v___x_6759_) == 0)
{
lean_object* v_g_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; 
v_g_6760_ = lean_ctor_get(v___x_6759_, 0);
lean_inc_ref(v_g_6760_);
lean_dec_ref_known(v___x_6759_, 1);
v___x_6761_ = lean_obj_once(&l_Lean_Fmt_fmtSeq___redArg___closed__0, &l_Lean_Fmt_fmtSeq___redArg___closed__0_once, _init_l_Lean_Fmt_fmtSeq___redArg___closed__0);
v___x_6762_ = l_Lean_Fmt_Layouts_sepArray(v_sep_6733_, v_g_6760_, v___x_6761_);
lean_dec_ref(v_g_6760_);
v___x_6763_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_6762_);
v___x_6764_ = lean_unsigned_to_nat(2u);
v___x_6765_ = lean_mk_empty_array_with_capacity(v___x_6764_);
v___x_6766_ = lean_array_push(v___x_6765_, v___x_6763_);
v___x_6767_ = lean_array_push(v___x_6766_, v___x_6753_);
v___x_6768_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6767_);
v_r_6739_ = v___x_6768_;
v___y_6740_ = v_a_6748_;
goto v___jp_6738_;
}
else
{
lean_dec(v___x_6759_);
lean_dec_ref(v_sep_6733_);
v_r_6739_ = v___x_6753_;
v___y_6740_ = v_a_6748_;
goto v___jp_6738_;
}
}
}
else
{
lean_object* v_a_6769_; lean_object* v_a_6770_; lean_object* v___x_6772_; uint8_t v_isShared_6773_; uint8_t v_isSharedCheck_6777_; 
lean_dec_ref(v_sep_6733_);
v_a_6769_ = lean_ctor_get(v___x_6746_, 0);
v_a_6770_ = lean_ctor_get(v___x_6746_, 1);
v_isSharedCheck_6777_ = !lean_is_exclusive(v___x_6746_);
if (v_isSharedCheck_6777_ == 0)
{
v___x_6772_ = v___x_6746_;
v_isShared_6773_ = v_isSharedCheck_6777_;
goto v_resetjp_6771_;
}
else
{
lean_inc(v_a_6770_);
lean_inc(v_a_6769_);
lean_dec(v___x_6746_);
v___x_6772_ = lean_box(0);
v_isShared_6773_ = v_isSharedCheck_6777_;
goto v_resetjp_6771_;
}
v_resetjp_6771_:
{
lean_object* v___x_6775_; 
if (v_isShared_6773_ == 0)
{
v___x_6775_ = v___x_6772_;
goto v_reusejp_6774_;
}
else
{
lean_object* v_reuseFailAlloc_6776_; 
v_reuseFailAlloc_6776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6776_, 0, v_a_6769_);
lean_ctor_set(v_reuseFailAlloc_6776_, 1, v_a_6770_);
v___x_6775_ = v_reuseFailAlloc_6776_;
goto v_reusejp_6774_;
}
v_reusejp_6774_:
{
return v___x_6775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___redArg___boxed(lean_object* v_sep_6793_, lean_object* v_seq_6794_, lean_object* v_nestedKind_x3f_6795_, lean_object* v_a_6796_, lean_object* v_a_6797_){
_start:
{
lean_object* v_res_6798_; 
v_res_6798_ = l_Lean_Fmt_fmtSeq___redArg(v_sep_6793_, v_seq_6794_, v_nestedKind_x3f_6795_, v_a_6796_, v_a_6797_);
lean_dec_ref(v_a_6796_);
lean_dec(v_nestedKind_x3f_6795_);
lean_dec_ref(v_seq_6794_);
return v_res_6798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq(lean_object* v_ks_6799_, lean_object* v_sep_6800_, lean_object* v_seq_6801_, lean_object* v_nestedKind_x3f_6802_, lean_object* v_a_6803_, lean_object* v_a_6804_){
_start:
{
lean_object* v___x_6805_; 
v___x_6805_ = l_Lean_Fmt_fmtSeq___redArg(v_sep_6800_, v_seq_6801_, v_nestedKind_x3f_6802_, v_a_6803_, v_a_6804_);
return v___x_6805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeq___boxed(lean_object* v_ks_6806_, lean_object* v_sep_6807_, lean_object* v_seq_6808_, lean_object* v_nestedKind_x3f_6809_, lean_object* v_a_6810_, lean_object* v_a_6811_){
_start:
{
lean_object* v_res_6812_; 
v_res_6812_ = l_Lean_Fmt_fmtSeq(v_ks_6806_, v_sep_6807_, v_seq_6808_, v_nestedKind_x3f_6809_, v_a_6810_, v_a_6811_);
lean_dec_ref(v_a_6810_);
lean_dec(v_nestedKind_x3f_6809_);
lean_dec_ref(v_seq_6808_);
lean_dec(v_ks_6806_);
return v_res_6812_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_180207733____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

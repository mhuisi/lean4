// Lean compiler output
// Module: Lean.Linter.Fmt
// Imports: public import Lean.Linter.Util public import Lean.Elab.Command import Lean.Fmt.FmtM
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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object*);
lean_object* l_Lean_Fmt_fmt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FmtM_run___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fmt"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 8, 229, 42, 239, 166, 104, 120)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 124, 192, 112, 1, 27, 7, 59)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'missing formatter' linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 236, 195, 191, 86, 102, 217, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 199, 11, 55, 37, 150, 232, 166)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_fmt_missing;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ignorePrivate"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 8, 229, 42, 239, 166, 104, 120)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 124, 192, 112, 1, 27, 7, 59)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 138, 138, 89, 253, 59, 91, 6)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "make the 'missing formatter' linter ignore syntax with a private node kind, which is what `local syntax`, `local macro` and `local notation` produce"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 236, 195, 191, 86, 102, 217, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 199, 11, 55, 37, 150, 232, 166)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(18, 32, 83, 52, 79, 203, 129, 2)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_fmt_missing_ignorePrivate;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "no auto-formatter registered for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Auto-formatter "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " is incomplete.\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "The syntax at the location has the following form:\n\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "The auto-formatter failed, so this command was not checked for missing formatters:\n\n"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_fmtMissing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_fmtMissing___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_fmtMissing___closed__0 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__0_value;
static const lean_string_object l_Lean_Linter_fmtMissing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtMissing"};
static const lean_object* l_Lean_Linter_fmtMissing___closed__1 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__1_value;
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_fmtMissing___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 92, 3, 98, 243, 31, 56, 197)}};
static const lean_object* l_Lean_Linter_fmtMissing___closed__2 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value;
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__0_value),((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value)}};
static const lean_object* l_Lean_Linter_fmtMissing___closed__3 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_fmtMissing = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_));
v___x_83_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_));
v___x_85_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(lean_object* v_cmdStx_88_, lean_object* v_x_89_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
lean_object* v_stx_90_; 
v_stx_90_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_90_);
return v_stx_90_;
}
case 2:
{
lean_object* v_stx_91_; 
v_stx_91_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_91_);
return v_stx_91_;
}
case 3:
{
lean_object* v_stx_92_; 
v_stx_92_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_92_);
return v_stx_92_;
}
case 4:
{
lean_object* v_stx_93_; 
v_stx_93_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_93_);
return v_stx_93_;
}
case 5:
{
lean_object* v_stx_94_; 
v_stx_94_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_94_);
return v_stx_94_;
}
case 6:
{
lean_object* v_stx_95_; 
v_stx_95_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_stx_95_);
return v_stx_95_;
}
default: 
{
lean_inc(v_cmdStx_88_);
return v_cmdStx_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef___boxed(lean_object* v_cmdStx_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(v_cmdStx_96_, v_x_97_);
lean_dec_ref(v_x_97_);
lean_dec(v_cmdStx_96_);
return v_res_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(lean_object* v_opts_99_, lean_object* v_opt_100_){
_start:
{
lean_object* v_name_101_; lean_object* v_defValue_102_; lean_object* v_map_103_; lean_object* v___x_104_; 
v_name_101_ = lean_ctor_get(v_opt_100_, 0);
v_defValue_102_ = lean_ctor_get(v_opt_100_, 1);
v_map_103_ = lean_ctor_get(v_opts_99_, 0);
v___x_104_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_103_, v_name_101_);
if (lean_obj_tag(v___x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = lean_unbox(v_defValue_102_);
return v___x_105_;
}
else
{
lean_object* v_val_106_; 
v_val_106_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v___x_104_, 1);
if (lean_obj_tag(v_val_106_) == 1)
{
uint8_t v_v_107_; 
v_v_107_ = lean_ctor_get_uint8(v_val_106_, 0);
lean_dec_ref_known(v_val_106_, 0);
return v_v_107_;
}
else
{
uint8_t v___x_108_; 
lean_dec(v_val_106_);
v___x_108_ = lean_unbox(v_defValue_102_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0___boxed(lean_object* v_opts_109_, lean_object* v_opt_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_109_, v_opt_110_);
lean_dec_ref(v_opt_110_);
lean_dec_ref(v_opts_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(lean_object* v_opts_116_, lean_object* v_kind_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1));
v___x_119_ = lean_name_eq(v_kind_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Linter_linter_fmt_missing_ignorePrivate;
v___x_121_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_116_, v___x_120_);
if (v___x_121_ == 0)
{
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_isPrivateName(v_kind_117_);
return v___x_122_;
}
}
else
{
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___boxed(lean_object* v_opts_123_, lean_object* v_kind_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v_opts_123_, v_kind_124_);
lean_dec(v_kind_124_);
lean_dec_ref(v_opts_123_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0(lean_object* v_infoState_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_trees_131_; 
v___x_129_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_127_);
v___x_130_ = lean_task_get_own(v___x_129_);
v_trees_131_ = lean_ctor_get(v___x_130_, 2);
lean_inc_ref(v_trees_131_);
lean_dec(v___x_130_);
return v_trees_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(lean_object* v_range_135_, lean_object* v_as_136_, size_t v_sz_137_, size_t v_i_138_, lean_object* v_b_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = lean_usize_dec_lt(v_i_138_, v_sz_137_);
if (v___x_140_ == 0)
{
lean_dec_ref(v_range_135_);
lean_inc_ref(v_b_139_);
return v_b_139_;
}
else
{
lean_object* v___x_141_; lean_object* v_a_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v_a_142_ = lean_array_uget_borrowed(v_as_136_, v_i_138_);
lean_inc_ref(v_range_135_);
lean_inc(v_a_142_);
v___x_143_ = l_Lean_Fmt_findChoiceResolution_x3f(v_a_142_, v_range_135_);
if (lean_obj_tag(v___x_143_) == 1)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_range_135_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; 
lean_dec(v___x_143_);
v___x_146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_138_, v___x_147_);
v_i_138_ = v___x_148_;
v_b_139_ = v___x_146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___boxed(lean_object* v_range_150_, lean_object* v_as_151_, lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_b_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_150_, v_as_151_, v_sz_boxed_155_, v_i_boxed_156_, v_b_154_);
lean_dec_ref(v_b_154_);
lean_dec_ref(v_as_151_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object* v_range_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v_cs_160_; lean_object* v___x_161_; lean_object* v___x_162_; size_t v_sz_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v_fst_166_; 
v_cs_160_ = lean_ctor_get(v_x_159_, 0);
v___x_161_ = lean_box(0);
v___x_162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_163_ = lean_array_size(v_cs_160_);
v___x_164_ = ((size_t)0ULL);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_range_158_, v_cs_160_, v_sz_163_, v___x_164_, v___x_162_);
v_fst_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_fst_166_);
lean_dec_ref(v___x_165_);
if (lean_obj_tag(v_fst_166_) == 0)
{
return v___x_161_;
}
else
{
lean_object* v_val_167_; 
v_val_167_ = lean_ctor_get(v_fst_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v_fst_166_, 1);
return v_val_167_;
}
}
else
{
lean_object* v_vs_168_; lean_object* v___x_169_; lean_object* v___x_170_; size_t v_sz_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v_fst_174_; 
v_vs_168_ = lean_ctor_get(v_x_159_, 0);
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_171_ = lean_array_size(v_vs_168_);
v___x_172_ = ((size_t)0ULL);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_158_, v_vs_168_, v_sz_171_, v___x_172_, v___x_170_);
v_fst_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_fst_174_);
lean_dec_ref(v___x_173_);
if (lean_obj_tag(v_fst_174_) == 0)
{
return v___x_169_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v_fst_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v_fst_174_, 1);
return v_val_175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object* v_range_176_, lean_object* v_as_177_, size_t v_sz_178_, size_t v_i_179_, lean_object* v_b_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_181_ == 0)
{
lean_dec_ref(v_range_176_);
lean_inc_ref(v_b_180_);
return v_b_180_;
}
else
{
lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_184_; 
v___x_182_ = lean_box(0);
v_a_183_ = lean_array_uget_borrowed(v_as_177_, v_i_179_);
lean_inc_ref(v_range_176_);
v___x_184_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_176_, v_a_183_);
if (lean_obj_tag(v___x_184_) == 1)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec_ref(v_range_176_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_182_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; 
lean_dec(v___x_184_);
v___x_187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_179_, v___x_188_);
v_i_179_ = v___x_189_;
v_b_180_ = v___x_187_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object* v_range_191_, lean_object* v_as_192_, lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_b_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_range_191_, v_as_192_, v_sz_boxed_196_, v_i_boxed_197_, v_b_195_);
lean_dec_ref(v_b_195_);
lean_dec_ref(v_as_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object* v_range_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_199_, v_x_200_);
lean_dec_ref(v_x_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object* v_range_202_, lean_object* v_t_203_){
_start:
{
lean_object* v_root_204_; lean_object* v_tail_205_; lean_object* v___x_206_; 
v_root_204_ = lean_ctor_get(v_t_203_, 0);
v_tail_205_ = lean_ctor_get(v_t_203_, 1);
lean_inc_ref(v_range_202_);
v___x_206_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_202_, v_root_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_207_; size_t v_sz_208_; size_t v___x_209_; lean_object* v___x_210_; lean_object* v_fst_211_; 
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_208_ = lean_array_size(v_tail_205_);
v___x_209_ = ((size_t)0ULL);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_202_, v_tail_205_, v_sz_208_, v___x_209_, v___x_207_);
v_fst_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_fst_211_);
lean_dec_ref(v___x_210_);
if (lean_obj_tag(v_fst_211_) == 0)
{
return v___x_206_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v_fst_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v_fst_211_, 1);
return v_val_212_;
}
}
else
{
lean_dec_ref(v_range_202_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object* v_range_213_, lean_object* v_t_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v_range_213_, v_t_214_);
lean_dec_ref(v_t_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(lean_object* v___x_216_, lean_object* v_range_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_thunk_get_own(v___x_216_);
v___x_219_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v_range_217_, v___x_218_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed(lean_object* v___x_220_, lean_object* v_range_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(v___x_220_, v_range_221_);
lean_dec_ref(v___x_220_);
return v_res_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_224_, uint8_t v___y_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 1)
{
lean_object* v_pre_227_; 
v_pre_227_ = lean_ctor_get(v_x_226_, 0);
if (lean_obj_tag(v_pre_227_) == 0)
{
lean_object* v_str_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_str_228_ = lean_ctor_get(v_x_226_, 1);
v___x_229_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0));
v___x_230_ = lean_string_dec_eq(v_str_228_, v___x_229_);
if (v___x_230_ == 0)
{
return v___x_230_;
}
else
{
return v_suppressElabErrors_224_;
}
}
else
{
return v___y_225_;
}
}
else
{
return v___y_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_231_, lean_object* v___y_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_suppressElabErrors_boxed_234_; uint8_t v___y_8235__boxed_235_; uint8_t v_res_236_; lean_object* v_r_237_; 
v_suppressElabErrors_boxed_234_ = lean_unbox(v_suppressElabErrors_231_);
v___y_8235__boxed_235_ = lean_unbox(v___y_232_);
v_res_236_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_234_, v___y_8235__boxed_235_, v_x_233_);
lean_dec(v_x_233_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_238_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
lean_ctor_set(v___x_243_, 3, v___x_242_);
lean_ctor_set(v___x_243_, 4, v___x_241_);
lean_ctor_set(v___x_243_, 5, v___x_241_);
lean_ctor_set(v___x_243_, 6, v___x_241_);
lean_ctor_set(v___x_243_, 7, v___x_241_);
lean_ctor_set(v___x_243_, 8, v___x_241_);
lean_ctor_set(v___x_243_, 9, v___x_241_);
lean_ctor_set(v___x_243_, 10, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_unsigned_to_nat(32u);
v___x_245_ = lean_mk_empty_array_with_capacity(v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_247_ = ((size_t)5ULL);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_unsigned_to_nat(32u);
v___x_250_ = lean_mk_empty_array_with_capacity(v___x_249_);
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3);
v___x_252_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
lean_ctor_set(v___x_252_, 2, v___x_248_);
lean_ctor_set(v___x_252_, 3, v___x_248_);
lean_ctor_set_usize(v___x_252_, 4, v___x_247_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = lean_box(1);
v___x_254_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4);
v___x_255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_msgData_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_env_261_; lean_object* v___x_262_; lean_object* v_scopes_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_opts_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_260_ = lean_st_ref_get(v___y_258_);
v_env_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_env_261_);
lean_dec(v___x_260_);
v___x_262_ = lean_st_ref_get(v___y_258_);
v_scopes_263_ = lean_ctor_get(v___x_262_, 2);
lean_inc(v_scopes_263_);
lean_dec(v___x_262_);
v___x_264_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_265_ = l_List_head_x21___redArg(v___x_264_, v_scopes_263_);
lean_dec(v_scopes_263_);
v_opts_266_ = lean_ctor_get(v___x_265_, 1);
lean_inc_ref(v_opts_266_);
lean_dec(v___x_265_);
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2);
v___x_268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5);
v___x_269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_269_, 0, v_env_261_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
lean_ctor_set(v___x_269_, 3, v_opts_266_);
v___x_270_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_msgData_257_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_272_, v___y_273_);
lean_dec(v___y_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object* v_ref_277_, lean_object* v_msgData_278_, uint8_t v_severity_279_, uint8_t v_isSilent_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; uint8_t v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_350_; uint8_t v___y_351_; uint8_t v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; uint8_t v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; uint8_t v___y_386_; uint8_t v___y_387_; uint8_t v___y_388_; uint8_t v___x_403_; uint8_t v___y_405_; uint8_t v___y_406_; uint8_t v___y_407_; uint8_t v___y_409_; uint8_t v___x_421_; 
v___x_403_ = 2;
v___x_421_ = l_Lean_instBEqMessageSeverity_beq(v_severity_279_, v___x_403_);
if (v___x_421_ == 0)
{
v___y_409_ = v___x_421_;
goto v___jp_408_;
}
else
{
uint8_t v___x_422_; 
lean_inc_ref(v_msgData_278_);
v___x_422_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_278_);
v___y_409_ = v___x_422_;
goto v___jp_408_;
}
v___jp_284_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Elab_Command_getScope___redArg(v___y_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = l_Lean_Elab_Command_getScope___redArg(v___y_292_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_332_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_332_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_332_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_332_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v_currNamespace_301_; lean_object* v_openDecls_302_; lean_object* v_env_303_; lean_object* v_messages_304_; lean_object* v_scopes_305_; lean_object* v_usedQuotCtxts_306_; lean_object* v_nextMacroScope_307_; lean_object* v_maxRecDepth_308_; lean_object* v_ngen_309_; lean_object* v_auxDeclNGen_310_; lean_object* v_infoState_311_; lean_object* v_traceState_312_; lean_object* v_snapshotTasks_313_; lean_object* v_prevLinterStates_314_; lean_object* v_codeQualityEntryTasks_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_331_; 
v___x_300_ = lean_st_ref_take(v___y_292_);
v_currNamespace_301_ = lean_ctor_get(v_a_294_, 2);
lean_inc(v_currNamespace_301_);
lean_dec(v_a_294_);
v_openDecls_302_ = lean_ctor_get(v_a_296_, 3);
lean_inc(v_openDecls_302_);
lean_dec(v_a_296_);
v_env_303_ = lean_ctor_get(v___x_300_, 0);
v_messages_304_ = lean_ctor_get(v___x_300_, 1);
v_scopes_305_ = lean_ctor_get(v___x_300_, 2);
v_usedQuotCtxts_306_ = lean_ctor_get(v___x_300_, 3);
v_nextMacroScope_307_ = lean_ctor_get(v___x_300_, 4);
v_maxRecDepth_308_ = lean_ctor_get(v___x_300_, 5);
v_ngen_309_ = lean_ctor_get(v___x_300_, 6);
v_auxDeclNGen_310_ = lean_ctor_get(v___x_300_, 7);
v_infoState_311_ = lean_ctor_get(v___x_300_, 8);
v_traceState_312_ = lean_ctor_get(v___x_300_, 9);
v_snapshotTasks_313_ = lean_ctor_get(v___x_300_, 10);
v_prevLinterStates_314_ = lean_ctor_get(v___x_300_, 11);
v_codeQualityEntryTasks_315_ = lean_ctor_get(v___x_300_, 12);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_331_ == 0)
{
v___x_317_ = v___x_300_;
v_isShared_318_ = v_isSharedCheck_331_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_codeQualityEntryTasks_315_);
lean_inc(v_prevLinterStates_314_);
lean_inc(v_snapshotTasks_313_);
lean_inc(v_traceState_312_);
lean_inc(v_infoState_311_);
lean_inc(v_auxDeclNGen_310_);
lean_inc(v_ngen_309_);
lean_inc(v_maxRecDepth_308_);
lean_inc(v_nextMacroScope_307_);
lean_inc(v_usedQuotCtxts_306_);
lean_inc(v_scopes_305_);
lean_inc(v_messages_304_);
lean_inc(v_env_303_);
lean_dec(v___x_300_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_331_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_currNamespace_301_);
lean_ctor_set(v___x_319_, 1, v_openDecls_302_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___y_286_);
lean_inc_ref(v___y_288_);
lean_inc_ref(v___y_291_);
v___x_321_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_321_, 0, v___y_291_);
lean_ctor_set(v___x_321_, 1, v___y_285_);
lean_ctor_set(v___x_321_, 2, v___y_287_);
lean_ctor_set(v___x_321_, 3, v___y_288_);
lean_ctor_set(v___x_321_, 4, v___x_320_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5, v___y_289_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5 + 1, v___y_290_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5 + 2, v_isSilent_280_);
v___x_322_ = l_Lean_MessageLog_add(v___x_321_, v_messages_304_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_322_);
v___x_324_ = v___x_317_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_env_303_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_scopes_305_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_usedQuotCtxts_306_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_nextMacroScope_307_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v_maxRecDepth_308_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_ngen_309_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_auxDeclNGen_310_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_infoState_311_);
lean_ctor_set(v_reuseFailAlloc_330_, 9, v_traceState_312_);
lean_ctor_set(v_reuseFailAlloc_330_, 10, v_snapshotTasks_313_);
lean_ctor_set(v_reuseFailAlloc_330_, 11, v_prevLinterStates_314_);
lean_ctor_set(v_reuseFailAlloc_330_, 12, v_codeQualityEntryTasks_315_);
v___x_324_ = v_reuseFailAlloc_330_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_st_ref_put(v___y_292_, v___x_324_);
v___x_326_ = lean_box(0);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_326_);
v___x_328_ = v___x_298_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_a_294_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec_ref(v___y_285_);
v_a_333_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_295_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_295_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec_ref(v___y_285_);
v_a_341_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_293_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_293_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
v___jp_349_:
{
lean_object* v_fileName_355_; lean_object* v_fileMap_356_; uint8_t v_suppressElabErrors_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_376_; 
v_fileName_355_ = lean_ctor_get(v___y_281_, 0);
v_fileMap_356_ = lean_ctor_get(v___y_281_, 1);
v_suppressElabErrors_357_ = lean_ctor_get_uint8(v___y_281_, sizeof(void*)*10);
v___x_358_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_278_);
v___x_359_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v___x_358_, v___y_282_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc_ref_n(v_fileMap_356_, 2);
v___x_364_ = l_Lean_FileMap_toPosition(v_fileMap_356_, v___y_353_);
lean_dec(v___y_353_);
v___x_365_ = l_Lean_FileMap_toPosition(v_fileMap_356_, v___y_354_);
lean_dec(v___y_354_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___x_367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
if (v_suppressElabErrors_357_ == 0)
{
lean_del_object(v___x_362_);
v___y_285_ = v___x_364_;
v___y_286_ = v_a_360_;
v___y_287_ = v___x_366_;
v___y_288_ = v___x_367_;
v___y_289_ = v___y_351_;
v___y_290_ = v___y_352_;
v___y_291_ = v_fileName_355_;
v___y_292_ = v___y_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___f_370_; uint8_t v___x_371_; 
v___x_368_ = lean_box(v_suppressElabErrors_357_);
v___x_369_ = lean_box(v___y_350_);
v___f_370_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_370_, 0, v___x_368_);
lean_closure_set(v___f_370_, 1, v___x_369_);
lean_inc(v_a_360_);
v___x_371_ = l_Lean_MessageData_hasTag(v___f_370_, v_a_360_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec_ref_known(v___x_366_, 1);
lean_dec_ref(v___x_364_);
lean_dec(v_a_360_);
v___x_372_ = lean_box(0);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_372_);
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_del_object(v___x_362_);
v___y_285_ = v___x_364_;
v___y_286_ = v_a_360_;
v___y_287_ = v___x_366_;
v___y_288_ = v___x_367_;
v___y_289_ = v___y_351_;
v___y_290_ = v___y_352_;
v___y_291_ = v_fileName_355_;
v___y_292_ = v___y_282_;
goto v___jp_284_;
}
}
}
}
v___jp_377_:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Syntax_getTailPos_x3f(v___y_379_, v___y_380_);
lean_dec(v___y_379_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_inc(v___y_382_);
v___y_350_ = v___y_378_;
v___y_351_ = v___y_380_;
v___y_352_ = v___y_381_;
v___y_353_ = v___y_382_;
v___y_354_ = v___y_382_;
goto v___jp_349_;
}
else
{
lean_object* v_val_384_; 
v_val_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___x_383_, 1);
v___y_350_ = v___y_378_;
v___y_351_ = v___y_380_;
v___y_352_ = v___y_381_;
v___y_353_ = v___y_382_;
v___y_354_ = v_val_384_;
goto v___jp_349_;
}
}
v___jp_385_:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_Command_getRef___redArg(v___y_281_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_ref_391_; lean_object* v___x_392_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_ref_391_ = l_Lean_replaceRef(v_ref_277_, v_a_390_);
lean_dec(v_a_390_);
v___x_392_ = l_Lean_Syntax_getPos_x3f(v_ref_391_, v___y_387_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___y_378_ = v___y_386_;
v___y_379_ = v_ref_391_;
v___y_380_ = v___y_387_;
v___y_381_ = v___y_388_;
v___y_382_ = v___x_393_;
goto v___jp_377_;
}
else
{
lean_object* v_val_394_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_392_, 1);
v___y_378_ = v___y_386_;
v___y_379_ = v_ref_391_;
v___y_380_ = v___y_387_;
v___y_381_ = v___y_388_;
v___y_382_ = v_val_394_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_msgData_278_);
v_a_395_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
v___jp_404_:
{
if (v___y_407_ == 0)
{
v___y_386_ = v___y_405_;
v___y_387_ = v___y_406_;
v___y_388_ = v_severity_279_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___y_405_;
v___y_387_ = v___y_406_;
v___y_388_ = v___x_403_;
goto v___jp_385_;
}
}
v___jp_408_:
{
if (v___y_409_ == 0)
{
lean_object* v___x_410_; lean_object* v_scopes_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_opts_414_; uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_410_ = lean_st_ref_get(v___y_282_);
v_scopes_411_ = lean_ctor_get(v___x_410_, 2);
lean_inc(v_scopes_411_);
lean_dec(v___x_410_);
v___x_412_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_413_ = l_List_head_x21___redArg(v___x_412_, v_scopes_411_);
lean_dec(v_scopes_411_);
v_opts_414_ = lean_ctor_get(v___x_413_, 1);
lean_inc_ref(v_opts_414_);
lean_dec(v___x_413_);
v___x_415_ = 1;
v___x_416_ = l_Lean_instBEqMessageSeverity_beq(v_severity_279_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec_ref(v_opts_414_);
v___y_405_ = v___y_409_;
v___y_406_ = v___y_409_;
v___y_407_ = v___x_416_;
goto v___jp_404_;
}
else
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = l_Lean_warningAsError;
v___x_418_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_414_, v___x_417_);
lean_dec_ref(v_opts_414_);
v___y_405_ = v___y_409_;
v___y_406_ = v___y_409_;
v___y_407_ = v___x_418_;
goto v___jp_404_;
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v_msgData_278_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_423_, lean_object* v_msgData_424_, lean_object* v_severity_425_, lean_object* v_isSilent_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
uint8_t v_severity_boxed_430_; uint8_t v_isSilent_boxed_431_; lean_object* v_res_432_; 
v_severity_boxed_430_ = lean_unbox(v_severity_425_);
v_isSilent_boxed_431_ = lean_unbox(v_isSilent_426_);
v_res_432_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_423_, v_msgData_424_, v_severity_boxed_430_, v_isSilent_boxed_431_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_ref_423_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object* v_ref_433_, lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = 1;
v___x_439_ = 0;
v___x_440_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_433_, v_msgData_434_, v___x_438_, v___x_439_, v___y_435_, v___y_436_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object* v_ref_441_, lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_ref_441_, v_msgData_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v_ref_441_);
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object* v_linterOption_453_, lean_object* v_stx_454_, lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_name_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_477_; 
v_name_459_ = lean_ctor_get(v_linterOption_453_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_linterOption_453_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_linterOption_453_, 1);
lean_dec(v_unused_478_);
v___x_461_ = v_linterOption_453_;
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_name_459_);
lean_dec(v_linterOption_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1);
lean_inc(v_name_459_);
v___x_464_ = l_Lean_MessageData_ofName(v_name_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 7);
lean_ctor_set(v___x_461_, 1, v___x_464_);
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_476_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_disable_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_467_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v_disable_469_ = l_Lean_MessageData_note(v___x_468_);
v___x_470_ = l_Lean_Linter_linterMessageTag;
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v_msg_455_);
lean_ctor_set(v___x_471_, 1, v_disable_469_);
v___x_472_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_473_, 0, v_name_459_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_inc(v_stx_454_);
v___x_474_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_474_, 0, v_stx_454_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_stx_454_, v___x_474_, v___y_456_, v___y_457_);
lean_dec(v_stx_454_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object* v_linterOption_479_, lean_object* v_stx_480_, lean_object* v_msg_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_linterOption_479_, v_stx_480_, v_msg_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_485_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object* v___x_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
if (lean_obj_tag(v_a_490_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_a_491_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v_key_497_; lean_object* v_value_498_; lean_object* v_tail_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_key_497_ = lean_ctor_get(v_a_490_, 0);
lean_inc(v_key_497_);
v_value_498_ = lean_ctor_get(v_a_490_, 1);
lean_inc(v_value_498_);
v_tail_499_ = lean_ctor_get(v_a_490_, 2);
lean_inc(v_tail_499_);
lean_dec_ref_known(v_a_490_, 3);
v___x_500_ = lean_box(0);
v___x_501_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_489_, v_value_498_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_502_ = 1;
v___x_503_ = l_Lean_Linter_linter_fmt_missing;
v___x_504_ = l_Lean_Syntax_ofRange(v_key_497_, v___x_502_);
v___x_505_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1);
v___x_506_ = lean_box(0);
v___x_507_ = l_Lean_Expr_const___override(v_value_498_, v___x_506_);
v___x_508_ = l_Lean_MessageData_ofExpr(v___x_507_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_505_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_503_, v___x_504_, v___x_509_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec_ref_known(v___x_510_, 1);
v_a_490_ = v_tail_499_;
v_a_491_ = v___x_500_;
goto _start;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_tail_499_);
v_a_512_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_dec(v_value_498_);
lean_dec(v_key_497_);
v_a_490_ = v_tail_499_;
v_a_491_ = v___x_500_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object* v___x_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_521_, v_a_522_, v_a_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___x_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object* v___x_528_, lean_object* v_as_529_, size_t v_sz_530_, size_t v_i_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_lt(v_i_531_, v_sz_530_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_b_532_);
return v___x_537_;
}
else
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_array_uget_borrowed(v_as_529_, v_i_531_);
lean_inc(v_a_538_);
v___x_539_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_528_, v_a_538_, v_b_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_552_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
if (lean_obj_tag(v_a_540_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; 
v_a_544_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v_a_540_, 1);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_a_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_544_);
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
lean_object* v_a_548_; size_t v___x_549_; size_t v___x_550_; 
lean_del_object(v___x_542_);
v_a_548_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v_a_540_, 1);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_531_, v___x_549_);
v_i_531_ = v___x_550_;
v_b_532_ = v_a_548_;
goto _start;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_539_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_539_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object* v___x_561_, lean_object* v_as_562_, lean_object* v_sz_563_, lean_object* v_i_564_, lean_object* v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
size_t v_sz_boxed_569_; size_t v_i_boxed_570_; lean_object* v_res_571_; 
v_sz_boxed_569_ = lean_unbox_usize(v_sz_563_);
lean_dec(v_sz_563_);
v_i_boxed_570_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v___x_561_, v_as_562_, v_sz_boxed_569_, v_i_boxed_570_, v_b_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_as_562_);
lean_dec_ref(v___x_561_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
v___x_588_ = l_Lean_stringToMessageData(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object* v___x_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
if (lean_obj_tag(v_a_590_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_a_591_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_value_597_; lean_object* v_key_598_; lean_object* v_tail_599_; lean_object* v_stx_600_; lean_object* v_formatterName_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_654_; 
v_value_597_ = lean_ctor_get(v_a_590_, 1);
lean_inc(v_value_597_);
v_key_598_ = lean_ctor_get(v_a_590_, 0);
lean_inc(v_key_598_);
v_tail_599_ = lean_ctor_get(v_a_590_, 2);
lean_inc(v_tail_599_);
lean_dec_ref_known(v_a_590_, 3);
v_stx_600_ = lean_ctor_get(v_value_597_, 0);
v_formatterName_601_ = lean_ctor_get(v_value_597_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_value_597_);
if (v_isSharedCheck_654_ == 0)
{
v___x_603_ = v_value_597_;
v_isShared_604_ = v_isSharedCheck_654_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_formatterName_601_);
lean_inc(v_stx_600_);
lean_dec(v_value_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_654_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_box(0);
lean_inc(v_stx_600_);
v___x_606_ = l_Lean_Syntax_getKind(v_stx_600_);
v___x_607_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_589_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; lean_object* v___y_610_; uint8_t v___x_651_; 
v___x_608_ = 1;
v___x_651_ = l_Lean_Name_isAnonymous(v_formatterName_601_);
if (v___x_651_ == 0)
{
goto v___jp_645_;
}
else
{
if (v___x_607_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v_formatterName_601_);
v___x_652_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10);
v___y_610_ = v___x_652_;
goto v___jp_609_;
}
else
{
goto v___jp_645_;
}
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_611_ = l_Lean_Linter_linter_fmt_missing;
v___x_612_ = l_Lean_Syntax_ofRange(v_key_598_, v___x_608_);
v___x_613_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1);
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 7);
lean_ctor_set(v___x_603_, 1, v___y_610_);
lean_ctor_set(v___x_603_, 0, v___x_613_);
v___x_615_ = v___x_603_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___y_610_);
v___x_615_ = v_reuseFailAlloc_644_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_616_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_box(0);
v___x_619_ = l_Lean_Expr_const___override(v___x_606_, v___x_618_);
v___x_620_ = l_Lean_MessageData_ofExpr(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_617_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_box(0);
v___x_627_ = l_Lean_Syntax_formatStx(v_stx_600_, v___x_626_, v___x_607_);
v___x_628_ = l_Std_Format_defWidth;
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Std_Format_pretty(v___x_627_, v___x_628_, v___x_629_, v___x_629_);
v___x_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = l_Lean_MessageData_ofFormat(v___x_631_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_625_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_611_, v___x_612_, v___x_633_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref_known(v___x_634_, 1);
v_a_590_ = v_tail_599_;
v_a_591_ = v___x_605_;
goto _start;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_tail_599_);
v_a_636_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_Expr_const___override(v_formatterName_601_, v___x_646_);
v___x_648_ = l_Lean_MessageData_ofExpr(v___x_647_);
v___x_649_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___y_610_ = v___x_650_;
goto v___jp_609_;
}
}
else
{
lean_dec(v___x_606_);
lean_del_object(v___x_603_);
lean_dec(v_formatterName_601_);
lean_dec(v_stx_600_);
lean_dec(v_key_598_);
v_a_590_ = v_tail_599_;
v_a_591_ = v___x_605_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object* v___x_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_655_, v_a_656_, v_a_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___x_655_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object* v___x_662_, lean_object* v_as_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_lt(v_i_665_, v_sz_664_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_b_666_);
return v___x_671_;
}
else
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_array_uget_borrowed(v_as_663_, v_i_665_);
lean_inc(v_a_672_);
v___x_673_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_662_, v_a_672_, v_b_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_686_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_686_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_686_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_686_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; 
v_a_678_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v_a_674_, 1);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_a_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v_a_682_; size_t v___x_683_; size_t v___x_684_; 
lean_del_object(v___x_676_);
v_a_682_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_a_674_, 1);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_665_, v___x_683_);
v_i_665_ = v___x_684_;
v_b_666_ = v_a_682_;
goto _start;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_a_687_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_673_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_673_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object* v___x_695_, lean_object* v_as_696_, lean_object* v_sz_697_, lean_object* v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
size_t v_sz_boxed_703_; size_t v_i_boxed_704_; lean_object* v_res_705_; 
v_sz_boxed_703_ = lean_unbox_usize(v_sz_697_);
lean_dec(v_sz_697_);
v_i_boxed_704_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v___x_695_, v_as_696_, v_sz_boxed_703_, v_i_boxed_704_, v_b_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_as_696_);
lean_dec_ref(v___x_695_);
return v_res_705_;
}
}
static lean_object* _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object* v_stx_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_env_716_; lean_object* v_fileMap_717_; lean_object* v_scopes_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_opts_721_; lean_object* v_infoState_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_713_ = lean_st_ref_get(v_a_711_);
v___x_714_ = lean_st_ref_get(v_a_711_);
v___x_715_ = lean_st_ref_get(v_a_711_);
v_env_716_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_env_716_);
lean_dec(v___x_713_);
v_fileMap_717_ = lean_ctor_get(v_a_710_, 1);
v_scopes_718_ = lean_ctor_get(v___x_714_, 2);
lean_inc(v_scopes_718_);
lean_dec(v___x_714_);
v___x_719_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_720_ = l_List_head_x21___redArg(v___x_719_, v_scopes_718_);
lean_dec(v_scopes_718_);
v_opts_721_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref_n(v_opts_721_, 2);
lean_dec(v___x_720_);
v_infoState_722_ = lean_ctor_get(v___x_715_, 8);
lean_inc_ref(v_infoState_722_);
lean_dec(v___x_715_);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0), 2, 1);
lean_closure_set(v___f_723_, 0, v_infoState_722_);
v___x_724_ = lean_mk_thunk(v___f_723_);
v___f_725_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed), 2, 1);
lean_closure_set(v___f_725_, 0, v___x_724_);
lean_inc_n(v_stx_709_, 2);
v___x_726_ = l_Lean_Fmt_collectSyntaxLineInfos(v_stx_709_);
lean_inc_ref(v_fileMap_717_);
v___x_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_727_, 0, v_env_716_);
lean_ctor_set(v___x_727_, 1, v_fileMap_717_);
lean_ctor_set(v___x_727_, 2, v___f_725_);
lean_ctor_set(v___x_727_, 3, v_opts_721_);
lean_ctor_set(v___x_727_, 4, v___x_726_);
v___x_728_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 1);
lean_closure_set(v___x_728_, 0, v_stx_709_);
v___x_729_ = l_Lean_FmtM_run___redArg(v___x_727_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_opts_721_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_769_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_769_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_769_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_755_; 
v___x_734_ = l_Lean_Linter_linter_fmt_missing;
switch(lean_obj_tag(v_a_730_))
{
case 0:
{
lean_object* v_stx_763_; 
lean_dec(v_stx_709_);
v_stx_763_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_763_);
v___y_755_ = v_stx_763_;
goto v___jp_754_;
}
case 2:
{
lean_object* v_stx_764_; 
lean_dec(v_stx_709_);
v_stx_764_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_764_);
v___y_755_ = v_stx_764_;
goto v___jp_754_;
}
case 3:
{
lean_object* v_stx_765_; 
lean_dec(v_stx_709_);
v_stx_765_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_765_);
v___y_755_ = v_stx_765_;
goto v___jp_754_;
}
case 4:
{
lean_object* v_stx_766_; 
lean_dec(v_stx_709_);
v_stx_766_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_766_);
v___y_755_ = v_stx_766_;
goto v___jp_754_;
}
case 5:
{
lean_object* v_stx_767_; 
lean_dec(v_stx_709_);
v_stx_767_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_767_);
v___y_755_ = v_stx_767_;
goto v___jp_754_;
}
case 6:
{
lean_object* v_stx_768_; 
lean_dec(v_stx_709_);
v_stx_768_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_stx_768_);
v___y_755_ = v_stx_768_;
goto v___jp_754_;
}
default: 
{
v___y_755_ = v_stx_709_;
goto v___jp_754_;
}
}
v___jp_735_:
{
lean_object* v___x_740_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 3);
lean_ctor_set(v___x_732_, 0, v___y_738_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___y_738_);
v___x_740_ = v_reuseFailAlloc_753_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = l_Lean_MessageData_ofFormat(v___x_740_);
lean_inc_ref(v___y_736_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___y_736_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_734_, v___y_737_, v___x_742_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_752_);
v___x_745_ = v___x_743_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_box(0);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
return v___x_743_;
}
}
}
v___jp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1, &l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once, _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1);
switch(lean_obj_tag(v_a_730_))
{
case 1:
{
lean_object* v_msg_757_; 
v_msg_757_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_msg_757_);
lean_dec_ref_known(v_a_730_, 1);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_757_;
goto v___jp_735_;
}
case 4:
{
lean_object* v_msg_758_; 
v_msg_758_ = lean_ctor_get(v_a_730_, 3);
lean_inc_ref(v_msg_758_);
lean_dec_ref_known(v_a_730_, 4);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_758_;
goto v___jp_735_;
}
case 7:
{
lean_object* v_msg_759_; 
v_msg_759_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_msg_759_);
lean_dec_ref_known(v_a_730_, 1);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_759_;
goto v___jp_735_;
}
case 8:
{
lean_object* v_msg_760_; 
v_msg_760_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_msg_760_);
lean_dec_ref_known(v_a_730_, 1);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_760_;
goto v___jp_735_;
}
case 9:
{
lean_object* v_msg_761_; 
v_msg_761_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_msg_761_);
lean_dec_ref_known(v_a_730_, 1);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_761_;
goto v___jp_735_;
}
default: 
{
lean_object* v_msg_762_; 
v_msg_762_ = lean_ctor_get(v_a_730_, 1);
lean_inc_ref(v_msg_762_);
lean_dec(v_a_730_);
v___y_736_ = v___x_756_;
v___y_737_ = v___y_755_;
v___y_738_ = v_msg_762_;
goto v___jp_735_;
}
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v_toState_771_; lean_object* v_missingFormatters_772_; lean_object* v_partialFormatters_773_; lean_object* v_buckets_774_; lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_dec(v_stx_709_);
v_a_770_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_729_, 1);
v_toState_771_ = lean_ctor_get(v_a_770_, 0);
lean_inc_ref(v_toState_771_);
lean_dec(v_a_770_);
v_missingFormatters_772_ = lean_ctor_get(v_toState_771_, 3);
lean_inc_ref(v_missingFormatters_772_);
v_partialFormatters_773_ = lean_ctor_get(v_toState_771_, 4);
lean_inc_ref(v_partialFormatters_773_);
lean_dec_ref(v_toState_771_);
v_buckets_774_ = lean_ctor_get(v_missingFormatters_772_, 1);
lean_inc_ref(v_buckets_774_);
lean_dec_ref(v_missingFormatters_772_);
v___x_775_ = lean_box(0);
v_sz_776_ = lean_array_size(v_buckets_774_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_opts_721_, v_buckets_774_, v_sz_776_, v___x_777_, v___x_775_, v_a_710_, v_a_711_);
lean_dec_ref(v_buckets_774_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_buckets_779_; size_t v_sz_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_778_, 1);
v_buckets_779_ = lean_ctor_get(v_partialFormatters_773_, 1);
lean_inc_ref(v_buckets_779_);
lean_dec_ref(v_partialFormatters_773_);
v_sz_780_ = lean_array_size(v_buckets_779_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v_opts_721_, v_buckets_779_, v_sz_780_, v___x_777_, v___x_775_, v_a_710_, v_a_711_);
lean_dec_ref(v_buckets_779_);
lean_dec_ref(v_opts_721_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_781_, 0);
lean_dec(v_unused_789_);
v___x_783_ = v___x_781_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_dec(v___x_781_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_775_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_775_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
return v___x_781_;
}
}
else
{
lean_dec_ref(v_partialFormatters_773_);
lean_dec_ref(v_opts_721_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object* v_stx_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_stx_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object* v_msgData_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_795_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(v_msgData_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object* v_o_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v_env_809_; lean_object* v___x_810_; lean_object* v_toEnvExtension_811_; lean_object* v_asyncMode_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_merged_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v___x_808_ = lean_st_ref_get(v___y_806_);
v_env_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_env_809_);
lean_dec(v___x_808_);
v___x_810_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_811_ = lean_ctor_get(v___x_810_, 0);
v_asyncMode_812_ = lean_ctor_get(v_toEnvExtension_811_, 2);
v___x_813_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_814_ = lean_box(0);
v___x_815_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_813_, v___x_810_, v_env_809_, v_asyncMode_812_, v___x_814_);
v_merged_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_815_, 1);
lean_dec(v_unused_825_);
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_merged_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_merged_816_);
lean_ctor_set(v___x_818_, 0, v_o_805_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_o_805_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_merged_816_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object* v_o_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_826_, v___y_827_);
lean_dec(v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_scopes_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_opts_837_; lean_object* v___x_838_; 
v___x_833_ = lean_st_ref_get(v___y_831_);
v_scopes_834_ = lean_ctor_get(v___x_833_, 2);
lean_inc(v_scopes_834_);
lean_dec(v___x_833_);
v___x_835_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_836_ = l_List_head_x21___redArg(v___x_835_, v_scopes_834_);
lean_dec(v_scopes_834_);
v_opts_837_ = lean_ctor_get(v___x_836_, 1);
lean_inc_ref(v_opts_837_);
lean_dec(v___x_836_);
v___x_838_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_opts_837_, v___y_831_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object* v_cmdStx_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_865_; 
v___x_847_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_844_, v___y_845_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_865_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_865_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_865_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_toOptions_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_toOptions_852_ = lean_ctor_get(v_a_848_, 0);
lean_inc_ref(v_toOptions_852_);
lean_dec(v_a_848_);
v___x_853_ = l_Lean_Linter_linter_fmt_missing;
v___x_854_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_toOptions_852_, v___x_853_);
lean_dec_ref(v_toOptions_852_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_cmdStx_843_);
v___x_855_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_855_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
uint8_t v___x_859_; 
v___x_859_ = l_Lean_Syntax_hasMissing(v_cmdStx_843_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_del_object(v___x_850_);
v___x_860_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_cmdStx_843_, v___y_844_, v___y_845_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v_cmdStx_843_);
v___x_861_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_861_);
v___x_863_ = v___x_850_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object* v_cmdStx_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Linter_fmtMissing___lam__0(v_cmdStx_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object* v_o_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_881_, v___y_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object* v_o_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(v_o_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Linter_fmtMissing));
v___x_893_ = l_Lean_Elab_Command_addLinter(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
return v_res_895_;
}
}
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_fmt_missing = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_fmt_missing);
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_179712575____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_fmt_missing_ignorePrivate = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_fmt_missing_ignorePrivate);
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Fmt(builtin);
}
#ifdef __cplusplus
}
#endif

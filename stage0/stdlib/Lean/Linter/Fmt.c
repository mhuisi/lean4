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
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object*);
lean_object* l_Lean_Fmt_fmt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FmtM_run___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "missingFormatter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(31, 93, 27, 72, 141, 220, 114, 168)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'missing formatter' linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(220, 165, 152, 227, 176, 39, 169, 49)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_missingFormatter;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Auto-formatter "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__4 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__4_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " is incomplete.\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__6 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__6_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "The syntax at the location has the following form:\n\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__8 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__8_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__10 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__10_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "no auto-formatter registered for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "The auto-formatter failed, so this command was not checked for missing formatters:\n\n"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_missingFormatter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_missingFormatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_missingFormatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_missingFormatter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_missingFormatter___closed__0 = (const lean_object*)&l_Lean_Linter_missingFormatter___closed__0_value;
static const lean_ctor_object l_Lean_Linter_missingFormatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_missingFormatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_missingFormatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_missingFormatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_missingFormatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 161, 121, 130, 97, 25, 139, 248)}};
static const lean_object* l_Lean_Linter_missingFormatter___closed__1 = (const lean_object*)&l_Lean_Linter_missingFormatter___closed__1_value;
static const lean_ctor_object l_Lean_Linter_missingFormatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_missingFormatter___closed__0_value),((lean_object*)&l_Lean_Linter_missingFormatter___closed__1_value)}};
static const lean_object* l_Lean_Linter_missingFormatter___closed__2 = (const lean_object*)&l_Lean_Linter_missingFormatter___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_missingFormatter = (const lean_object*)&l_Lean_Linter_missingFormatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(lean_object* v_cmdStx_59_, lean_object* v_x_60_){
_start:
{
switch(lean_obj_tag(v_x_60_))
{
case 0:
{
lean_object* v_stx_61_; 
v_stx_61_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_61_);
return v_stx_61_;
}
case 2:
{
lean_object* v_stx_62_; 
v_stx_62_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_62_);
return v_stx_62_;
}
case 3:
{
lean_object* v_stx_63_; 
v_stx_63_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_63_);
return v_stx_63_;
}
case 4:
{
lean_object* v_stx_64_; 
v_stx_64_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_64_);
return v_stx_64_;
}
case 5:
{
lean_object* v_stx_65_; 
v_stx_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_65_);
return v_stx_65_;
}
case 6:
{
lean_object* v_stx_66_; 
v_stx_66_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_stx_66_);
return v_stx_66_;
}
default: 
{
lean_inc(v_cmdStx_59_);
return v_cmdStx_59_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef___boxed(lean_object* v_cmdStx_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_errorRef(v_cmdStx_67_, v_x_68_);
lean_dec_ref(v_x_68_);
lean_dec(v_cmdStx_67_);
return v_res_69_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_70_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
lean_ctor_set(v___x_75_, 3, v___x_74_);
lean_ctor_set(v___x_75_, 4, v___x_73_);
lean_ctor_set(v___x_75_, 5, v___x_73_);
lean_ctor_set(v___x_75_, 6, v___x_73_);
lean_ctor_set(v___x_75_, 7, v___x_73_);
lean_ctor_set(v___x_75_, 8, v___x_73_);
lean_ctor_set(v___x_75_, 9, v___x_73_);
lean_ctor_set(v___x_75_, 10, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(32u);
v___x_77_ = lean_mk_empty_array_with_capacity(v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_79_ = ((size_t)5ULL);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_unsigned_to_nat(32u);
v___x_82_ = lean_mk_empty_array_with_capacity(v___x_81_);
v___x_83_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__3);
v___x_84_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
lean_ctor_set(v___x_84_, 2, v___x_80_);
lean_ctor_set(v___x_84_, 3, v___x_80_);
lean_ctor_set_usize(v___x_84_, 4, v___x_79_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_box(1);
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_msgData_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_scopes_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_opts_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_90_);
v_scopes_95_ = lean_ctor_get(v___x_94_, 2);
lean_inc(v_scopes_95_);
lean_dec(v___x_94_);
v___x_96_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_97_ = l_List_head_x21___redArg(v___x_96_, v_scopes_95_);
lean_dec(v_scopes_95_);
v_opts_98_ = lean_ctor_get(v___x_97_, 1);
lean_inc_ref(v_opts_98_);
lean_dec(v___x_97_);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__2);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___closed__5);
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v_env_93_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v_opts_98_);
v___x_102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_msgData_89_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_104_, v___y_105_);
lean_dec(v___y_105_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7(lean_object* v_opts_108_, lean_object* v_opt_109_){
_start:
{
lean_object* v_name_110_; lean_object* v_defValue_111_; lean_object* v_map_112_; lean_object* v___x_113_; 
v_name_110_ = lean_ctor_get(v_opt_109_, 0);
v_defValue_111_ = lean_ctor_get(v_opt_109_, 1);
v_map_112_ = lean_ctor_get(v_opts_108_, 0);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_112_, v_name_110_);
if (lean_obj_tag(v___x_113_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = lean_unbox(v_defValue_111_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; 
v_val_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v___x_113_, 1);
if (lean_obj_tag(v_val_115_) == 1)
{
uint8_t v_v_116_; 
v_v_116_ = lean_ctor_get_uint8(v_val_115_, 0);
lean_dec_ref_known(v_val_115_, 0);
return v_v_116_;
}
else
{
uint8_t v___x_117_; 
lean_dec(v_val_115_);
v___x_117_ = lean_unbox(v_defValue_111_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7(v_opts_118_, v_opt_119_);
lean_dec_ref(v_opt_119_);
lean_dec_ref(v_opts_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_123_, uint8_t v_suppressElabErrors_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 1)
{
lean_object* v_pre_126_; 
v_pre_126_ = lean_ctor_get(v_x_125_, 0);
if (lean_obj_tag(v_pre_126_) == 0)
{
lean_object* v_str_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_str_127_ = lean_ctor_get(v_x_125_, 1);
v___x_128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_129_ = lean_string_dec_eq(v_str_127_, v___x_128_);
if (v___x_129_ == 0)
{
return v___y_123_;
}
else
{
return v_suppressElabErrors_124_;
}
}
else
{
return v___y_123_;
}
}
else
{
return v___y_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_130_, lean_object* v_suppressElabErrors_131_, lean_object* v_x_132_){
_start:
{
uint8_t v___y_6912__boxed_133_; uint8_t v_suppressElabErrors_boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v___y_6912__boxed_133_ = lean_unbox(v___y_130_);
v_suppressElabErrors_boxed_134_ = lean_unbox(v_suppressElabErrors_131_);
v_res_135_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0(v___y_6912__boxed_133_, v_suppressElabErrors_boxed_134_, v_x_132_);
lean_dec(v_x_132_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object* v_ref_138_, lean_object* v_msgData_139_, uint8_t v_severity_140_, uint8_t v_isSilent_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___y_146_; lean_object* v___y_147_; uint8_t v___y_148_; uint8_t v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; uint8_t v___y_210_; uint8_t v___y_211_; uint8_t v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; uint8_t v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; uint8_t v___y_241_; lean_object* v___y_242_; uint8_t v___y_246_; uint8_t v___y_247_; uint8_t v___y_248_; uint8_t v___x_263_; uint8_t v___y_265_; uint8_t v___y_266_; uint8_t v___y_267_; uint8_t v___y_269_; uint8_t v___x_281_; 
v___x_263_ = 2;
v___x_281_ = l_Lean_instBEqMessageSeverity_beq(v_severity_140_, v___x_263_);
if (v___x_281_ == 0)
{
v___y_269_ = v___x_281_;
goto v___jp_268_;
}
else
{
uint8_t v___x_282_; 
lean_inc_ref(v_msgData_139_);
v___x_282_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_139_);
v___y_269_ = v___x_282_;
goto v___jp_268_;
}
v___jp_145_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Elab_Command_getScope___redArg(v___y_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = l_Lean_Elab_Command_getScope___redArg(v___y_153_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_192_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_192_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_192_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_192_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v_env_164_; lean_object* v_messages_165_; lean_object* v_scopes_166_; lean_object* v_usedQuotCtxts_167_; lean_object* v_nextMacroScope_168_; lean_object* v_maxRecDepth_169_; lean_object* v_ngen_170_; lean_object* v_auxDeclNGen_171_; lean_object* v_infoState_172_; lean_object* v_traceState_173_; lean_object* v_snapshotTasks_174_; lean_object* v_prevLinterStates_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_191_; 
v___x_161_ = lean_st_ref_take(v___y_153_);
v_currNamespace_162_ = lean_ctor_get(v_a_155_, 2);
lean_inc(v_currNamespace_162_);
lean_dec(v_a_155_);
v_openDecls_163_ = lean_ctor_get(v_a_157_, 3);
lean_inc(v_openDecls_163_);
lean_dec(v_a_157_);
v_env_164_ = lean_ctor_get(v___x_161_, 0);
v_messages_165_ = lean_ctor_get(v___x_161_, 1);
v_scopes_166_ = lean_ctor_get(v___x_161_, 2);
v_usedQuotCtxts_167_ = lean_ctor_get(v___x_161_, 3);
v_nextMacroScope_168_ = lean_ctor_get(v___x_161_, 4);
v_maxRecDepth_169_ = lean_ctor_get(v___x_161_, 5);
v_ngen_170_ = lean_ctor_get(v___x_161_, 6);
v_auxDeclNGen_171_ = lean_ctor_get(v___x_161_, 7);
v_infoState_172_ = lean_ctor_get(v___x_161_, 8);
v_traceState_173_ = lean_ctor_get(v___x_161_, 9);
v_snapshotTasks_174_ = lean_ctor_get(v___x_161_, 10);
v_prevLinterStates_175_ = lean_ctor_get(v___x_161_, 11);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_191_ == 0)
{
v___x_177_ = v___x_161_;
v_isShared_178_ = v_isSharedCheck_191_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_prevLinterStates_175_);
lean_inc(v_snapshotTasks_174_);
lean_inc(v_traceState_173_);
lean_inc(v_infoState_172_);
lean_inc(v_auxDeclNGen_171_);
lean_inc(v_ngen_170_);
lean_inc(v_maxRecDepth_169_);
lean_inc(v_nextMacroScope_168_);
lean_inc(v_usedQuotCtxts_167_);
lean_inc(v_scopes_166_);
lean_inc(v_messages_165_);
lean_inc(v_env_164_);
lean_dec(v___x_161_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_191_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_currNamespace_162_);
lean_ctor_set(v___x_179_, 1, v_openDecls_163_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___y_151_);
lean_inc_ref(v___y_147_);
lean_inc_ref(v___y_152_);
v___x_181_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_181_, 0, v___y_152_);
lean_ctor_set(v___x_181_, 1, v___y_146_);
lean_ctor_set(v___x_181_, 2, v___y_150_);
lean_ctor_set(v___x_181_, 3, v___y_147_);
lean_ctor_set(v___x_181_, 4, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5, v___y_149_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5 + 1, v___y_148_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5 + 2, v_isSilent_141_);
v___x_182_ = l_Lean_MessageLog_add(v___x_181_, v_messages_165_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_182_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_env_164_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_scopes_166_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_usedQuotCtxts_167_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_nextMacroScope_168_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_maxRecDepth_169_);
lean_ctor_set(v_reuseFailAlloc_190_, 6, v_ngen_170_);
lean_ctor_set(v_reuseFailAlloc_190_, 7, v_auxDeclNGen_171_);
lean_ctor_set(v_reuseFailAlloc_190_, 8, v_infoState_172_);
lean_ctor_set(v_reuseFailAlloc_190_, 9, v_traceState_173_);
lean_ctor_set(v_reuseFailAlloc_190_, 10, v_snapshotTasks_174_);
lean_ctor_set(v_reuseFailAlloc_190_, 11, v_prevLinterStates_175_);
v___x_184_ = v_reuseFailAlloc_190_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_st_ref_put(v___y_153_, v___x_184_);
v___x_186_ = lean_box(0);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_186_);
v___x_188_ = v___x_159_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_a_155_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_146_);
v_a_193_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_156_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_156_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_146_);
v_a_201_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_154_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_154_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
v___jp_209_:
{
lean_object* v_fileName_215_; lean_object* v_fileMap_216_; uint8_t v_suppressElabErrors_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_236_; 
v_fileName_215_ = lean_ctor_get(v___y_142_, 0);
v_fileMap_216_ = lean_ctor_get(v___y_142_, 1);
v_suppressElabErrors_217_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*10);
v___x_218_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_139_);
v___x_219_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg(v___x_218_, v___y_143_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_236_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_236_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_236_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_inc_ref_n(v_fileMap_216_, 2);
v___x_224_ = l_Lean_FileMap_toPosition(v_fileMap_216_, v___y_213_);
lean_dec(v___y_213_);
v___x_225_ = l_Lean_FileMap_toPosition(v_fileMap_216_, v___y_214_);
lean_dec(v___y_214_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
v___x_227_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___closed__0));
if (v_suppressElabErrors_217_ == 0)
{
lean_del_object(v___x_222_);
v___y_146_ = v___x_224_;
v___y_147_ = v___x_227_;
v___y_148_ = v___y_212_;
v___y_149_ = v___y_211_;
v___y_150_ = v___x_226_;
v___y_151_ = v_a_220_;
v___y_152_ = v_fileName_215_;
v___y_153_ = v___y_143_;
goto v___jp_145_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___f_230_; uint8_t v___x_231_; 
v___x_228_ = lean_box(v___y_210_);
v___x_229_ = lean_box(v_suppressElabErrors_217_);
v___f_230_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_230_, 0, v___x_228_);
lean_closure_set(v___f_230_, 1, v___x_229_);
lean_inc(v_a_220_);
v___x_231_ = l_Lean_MessageData_hasTag(v___f_230_, v_a_220_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec_ref_known(v___x_226_, 1);
lean_dec_ref(v___x_224_);
lean_dec(v_a_220_);
v___x_232_ = lean_box(0);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_232_);
v___x_234_ = v___x_222_;
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
else
{
lean_del_object(v___x_222_);
v___y_146_ = v___x_224_;
v___y_147_ = v___x_227_;
v___y_148_ = v___y_212_;
v___y_149_ = v___y_211_;
v___y_150_ = v___x_226_;
v___y_151_ = v_a_220_;
v___y_152_ = v_fileName_215_;
v___y_153_ = v___y_143_;
goto v___jp_145_;
}
}
}
}
v___jp_237_:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Syntax_getTailPos_x3f(v___y_239_, v___y_241_);
lean_dec(v___y_239_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_inc(v___y_242_);
v___y_210_ = v___y_238_;
v___y_211_ = v___y_241_;
v___y_212_ = v___y_240_;
v___y_213_ = v___y_242_;
v___y_214_ = v___y_242_;
goto v___jp_209_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_243_, 1);
v___y_210_ = v___y_238_;
v___y_211_ = v___y_241_;
v___y_212_ = v___y_240_;
v___y_213_ = v___y_242_;
v___y_214_ = v_val_244_;
goto v___jp_209_;
}
}
v___jp_245_:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Elab_Command_getRef___redArg(v___y_142_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_ref_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v_ref_251_ = l_Lean_replaceRef(v_ref_138_, v_a_250_);
lean_dec(v_a_250_);
v___x_252_ = l_Lean_Syntax_getPos_x3f(v_ref_251_, v___y_247_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___y_238_ = v___y_246_;
v___y_239_ = v_ref_251_;
v___y_240_ = v___y_248_;
v___y_241_ = v___y_247_;
v___y_242_ = v___x_253_;
goto v___jp_237_;
}
else
{
lean_object* v_val_254_; 
v_val_254_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v___x_252_, 1);
v___y_238_ = v___y_246_;
v___y_239_ = v_ref_251_;
v___y_240_ = v___y_248_;
v___y_241_ = v___y_247_;
v___y_242_ = v_val_254_;
goto v___jp_237_;
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_msgData_139_);
v_a_255_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_249_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_249_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
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
v___jp_264_:
{
if (v___y_267_ == 0)
{
v___y_246_ = v___y_265_;
v___y_247_ = v___y_266_;
v___y_248_ = v_severity_140_;
goto v___jp_245_;
}
else
{
v___y_246_ = v___y_265_;
v___y_247_ = v___y_266_;
v___y_248_ = v___x_263_;
goto v___jp_245_;
}
}
v___jp_268_:
{
if (v___y_269_ == 0)
{
lean_object* v___x_270_; lean_object* v_scopes_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_opts_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_270_ = lean_st_ref_get(v___y_143_);
v_scopes_271_ = lean_ctor_get(v___x_270_, 2);
lean_inc(v_scopes_271_);
lean_dec(v___x_270_);
v___x_272_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_273_ = l_List_head_x21___redArg(v___x_272_, v_scopes_271_);
lean_dec(v_scopes_271_);
v_opts_274_ = lean_ctor_get(v___x_273_, 1);
lean_inc_ref(v_opts_274_);
lean_dec(v___x_273_);
v___x_275_ = 1;
v___x_276_ = l_Lean_instBEqMessageSeverity_beq(v_severity_140_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_opts_274_);
v___y_265_ = v___y_269_;
v___y_266_ = v___y_269_;
v___y_267_ = v___x_276_;
goto v___jp_264_;
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_warningAsError;
v___x_278_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7(v_opts_274_, v___x_277_);
lean_dec_ref(v_opts_274_);
v___y_265_ = v___y_269_;
v___y_266_ = v___y_269_;
v___y_267_ = v___x_278_;
goto v___jp_264_;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v_msgData_139_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_283_, lean_object* v_msgData_284_, lean_object* v_severity_285_, lean_object* v_isSilent_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
uint8_t v_severity_boxed_290_; uint8_t v_isSilent_boxed_291_; lean_object* v_res_292_; 
v_severity_boxed_290_ = lean_unbox(v_severity_285_);
v_isSilent_boxed_291_ = lean_unbox(v_isSilent_286_);
v_res_292_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_ref_283_, v_msgData_284_, v_severity_boxed_290_, v_isSilent_boxed_291_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v_ref_283_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object* v_ref_293_, lean_object* v_msgData_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; 
v___x_298_ = 1;
v___x_299_ = 0;
v___x_300_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_ref_293_, v_msgData_294_, v___x_298_, v___x_299_, v___y_295_, v___y_296_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object* v_ref_301_, lean_object* v_msgData_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_ref_301_, v_msgData_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v_ref_301_);
return v_res_306_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__0));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__2));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object* v_linterOption_313_, lean_object* v_stx_314_, lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_name_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_337_; 
v_name_319_ = lean_ctor_get(v_linterOption_313_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_linterOption_313_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_linterOption_313_, 1);
lean_dec(v_unused_338_);
v___x_321_ = v_linterOption_313_;
v_isShared_322_ = v_isSharedCheck_337_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_name_319_);
lean_dec(v_linterOption_313_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_337_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__1);
lean_inc(v_name_319_);
v___x_324_ = l_Lean_MessageData_ofName(v_name_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 7);
lean_ctor_set(v___x_321_, 1, v___x_324_);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_336_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_disable_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_327_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v_disable_329_ = l_Lean_MessageData_note(v___x_328_);
v___x_330_ = l_Lean_Linter_linterMessageTag;
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v_msg_315_);
lean_ctor_set(v___x_331_, 1, v_disable_329_);
v___x_332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_333_, 0, v_name_319_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_inc(v_stx_314_);
v___x_334_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_334_, 0, v_stx_314_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_stx_314_, v___x_334_, v___y_316_, v___y_317_);
lean_dec(v_stx_314_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object* v_linterOption_339_, lean_object* v_stx_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v_linterOption_339_, v_stx_340_, v_msg_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__4));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__6));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__8));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__10));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___closed__0));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
if (lean_obj_tag(v_a_366_) == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v_a_367_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v_value_373_; lean_object* v_key_374_; lean_object* v_tail_375_; lean_object* v_stx_376_; lean_object* v_formatterName_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_431_; 
v_value_373_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_value_373_);
v_key_374_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_key_374_);
v_tail_375_ = lean_ctor_get(v_a_366_, 2);
lean_inc(v_tail_375_);
lean_dec_ref_known(v_a_366_, 3);
v_stx_376_ = lean_ctor_get(v_value_373_, 0);
v_formatterName_377_ = lean_ctor_get(v_value_373_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_value_373_);
if (v_isSharedCheck_431_ == 0)
{
v___x_379_ = v_value_373_;
v_isShared_380_ = v_isSharedCheck_431_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_formatterName_377_);
lean_inc(v_stx_376_);
lean_dec(v_value_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_431_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_381_ = lean_box(0);
lean_inc(v_stx_376_);
v___x_382_ = l_Lean_Syntax_getKind(v_stx_376_);
v___x_383_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1));
v___x_384_ = lean_name_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; lean_object* v___y_387_; uint8_t v___x_428_; 
v___x_385_ = 1;
v___x_428_ = l_Lean_Name_isAnonymous(v_formatterName_377_);
if (v___x_428_ == 0)
{
goto v___jp_422_;
}
else
{
if (v___x_384_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v_formatterName_377_);
v___x_429_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__12);
v___y_387_ = v___x_429_;
goto v___jp_386_;
}
else
{
goto v___jp_422_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_388_ = l_Lean_Linter_linter_missingFormatter;
v___x_389_ = l_Lean_Syntax_ofRange(v_key_374_, v___x_385_);
v___x_390_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 7);
lean_ctor_set(v___x_379_, 1, v___y_387_);
lean_ctor_set(v___x_379_, 0, v___x_390_);
v___x_392_ = v___x_379_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___y_387_);
v___x_392_ = v_reuseFailAlloc_421_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_393_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__5);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_box(0);
v___x_396_ = l_Lean_Expr_const___override(v___x_382_, v___x_395_);
v___x_397_ = l_Lean_MessageData_ofExpr(v___x_396_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_394_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__7);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__9);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_box(0);
v___x_404_ = l_Lean_Syntax_formatStx(v_stx_376_, v___x_403_, v___x_384_);
v___x_405_ = l_Std_Format_defWidth;
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l_Std_Format_pretty(v___x_404_, v___x_405_, v___x_406_, v___x_406_);
v___x_408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = l_Lean_MessageData_ofFormat(v___x_408_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_402_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v___x_388_, v___x_389_, v___x_410_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref_known(v___x_411_, 1);
v_a_366_ = v_tail_375_;
v_a_367_ = v___x_381_;
goto _start;
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_tail_375_);
v_a_413_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_423_ = lean_box(0);
v___x_424_ = l_Lean_Expr_const___override(v_formatterName_377_, v___x_423_);
v___x_425_ = l_Lean_MessageData_ofExpr(v___x_424_);
v___x_426_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__11);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___y_387_ = v___x_427_;
goto v___jp_386_;
}
}
else
{
lean_dec(v___x_382_);
lean_del_object(v___x_379_);
lean_dec(v_formatterName_377_);
lean_dec(v_stx_376_);
lean_dec(v_key_374_);
v_a_366_ = v_tail_375_;
v_a_367_ = v___x_381_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_a_432_, v_a_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object* v_as_438_, size_t v_sz_439_, size_t v_i_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v_b_441_);
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; 
v_a_447_ = lean_array_uget_borrowed(v_as_438_, v_i_440_);
lean_inc(v_a_447_);
v___x_448_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_a_447_, v_b_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_461_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_461_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_461_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_461_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
if (lean_obj_tag(v_a_449_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; 
v_a_453_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v_a_449_, 1);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_a_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v_a_457_; size_t v___x_458_; size_t v___x_459_; 
lean_del_object(v___x_451_);
v_a_457_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v_a_449_, 1);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_440_, v___x_458_);
v_i_440_ = v___x_459_;
v_b_441_ = v_a_457_;
goto _start;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_448_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_448_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object* v_as_470_, lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
size_t v_sz_boxed_477_; size_t v_i_boxed_478_; lean_object* v_res_479_; 
v_sz_boxed_477_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_478_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_as_470_, v_sz_boxed_477_, v_i_boxed_478_, v_b_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec_ref(v_as_470_);
return v_res_479_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
if (lean_obj_tag(v_a_483_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v_a_484_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
else
{
lean_object* v_key_490_; lean_object* v_value_491_; lean_object* v_tail_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_key_490_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_key_490_);
v_value_491_ = lean_ctor_get(v_a_483_, 1);
lean_inc(v_value_491_);
v_tail_492_ = lean_ctor_get(v_a_483_, 2);
lean_inc(v_tail_492_);
lean_dec_ref_known(v_a_483_, 3);
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1));
v___x_495_ = lean_name_eq(v_value_491_, v___x_494_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_496_ = 1;
v___x_497_ = l_Lean_Linter_linter_missingFormatter;
v___x_498_ = l_Lean_Syntax_ofRange(v_key_490_, v___x_496_);
v___x_499_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1);
v___x_500_ = lean_box(0);
v___x_501_ = l_Lean_Expr_const___override(v_value_491_, v___x_500_);
v___x_502_ = l_Lean_MessageData_ofExpr(v___x_501_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_499_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v___x_497_, v___x_498_, v___x_503_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_dec_ref_known(v___x_504_, 1);
v_a_483_ = v_tail_492_;
v_a_484_ = v___x_493_;
goto _start;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_tail_492_);
v_a_506_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_dec(v_value_491_);
lean_dec(v_key_490_);
v_a_483_ = v_tail_492_;
v_a_484_ = v___x_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v_a_515_, v_a_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object* v_as_521_, size_t v_sz_522_, size_t v_i_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_523_, v_sz_522_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_b_524_);
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_array_uget_borrowed(v_as_521_, v_i_523_);
lean_inc(v_a_530_);
v___x_531_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v_a_530_, v_b_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_544_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_544_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
if (lean_obj_tag(v_a_532_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v_a_532_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v_a_532_, 1);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_a_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
lean_object* v_a_540_; size_t v___x_541_; size_t v___x_542_; 
lean_del_object(v___x_534_);
v_a_540_ = lean_ctor_get(v_a_532_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v_a_532_, 1);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_523_, v___x_541_);
v_i_523_ = v___x_542_;
v_b_524_ = v_a_540_;
goto _start;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_531_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_531_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object* v_as_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_561_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v_as_553_, v_sz_boxed_560_, v_i_boxed_561_, v_b_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v_as_553_);
return v_res_562_;
}
}
static lean_object* _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object* v_stx_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v_fileMap_573_; lean_object* v_scopes_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_opts_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_570_ = lean_st_ref_get(v_a_568_);
v___x_571_ = lean_st_ref_get(v_a_568_);
v_env_572_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_570_);
v_fileMap_573_ = lean_ctor_get(v_a_567_, 1);
v_scopes_574_ = lean_ctor_get(v___x_571_, 2);
lean_inc(v_scopes_574_);
lean_dec(v___x_571_);
v___x_575_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_576_ = l_List_head_x21___redArg(v___x_575_, v_scopes_574_);
lean_dec(v_scopes_574_);
v_opts_577_ = lean_ctor_get(v___x_576_, 1);
lean_inc_ref(v_opts_577_);
lean_dec(v___x_576_);
lean_inc_n(v_stx_566_, 2);
v___x_578_ = l_Lean_Fmt_collectSyntaxLineInfos(v_stx_566_);
v___x_579_ = lean_box(0);
lean_inc_ref(v_fileMap_573_);
v___x_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_580_, 0, v_env_572_);
lean_ctor_set(v___x_580_, 1, v_fileMap_573_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v_opts_577_);
lean_ctor_set(v___x_580_, 4, v___x_578_);
v___x_581_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 1);
lean_closure_set(v___x_581_, 0, v_stx_566_);
v___x_582_ = l_Lean_FmtM_run___redArg(v___x_580_, v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_622_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_622_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_622_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_622_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_608_; 
v___x_587_ = l_Lean_Linter_linter_missingFormatter;
switch(lean_obj_tag(v_a_583_))
{
case 0:
{
lean_object* v_stx_616_; 
lean_dec(v_stx_566_);
v_stx_616_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_616_);
v___y_608_ = v_stx_616_;
goto v___jp_607_;
}
case 2:
{
lean_object* v_stx_617_; 
lean_dec(v_stx_566_);
v_stx_617_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_617_);
v___y_608_ = v_stx_617_;
goto v___jp_607_;
}
case 3:
{
lean_object* v_stx_618_; 
lean_dec(v_stx_566_);
v_stx_618_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_618_);
v___y_608_ = v_stx_618_;
goto v___jp_607_;
}
case 4:
{
lean_object* v_stx_619_; 
lean_dec(v_stx_566_);
v_stx_619_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_619_);
v___y_608_ = v_stx_619_;
goto v___jp_607_;
}
case 5:
{
lean_object* v_stx_620_; 
lean_dec(v_stx_566_);
v_stx_620_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_620_);
v___y_608_ = v_stx_620_;
goto v___jp_607_;
}
case 6:
{
lean_object* v_stx_621_; 
lean_dec(v_stx_566_);
v_stx_621_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_stx_621_);
v___y_608_ = v_stx_621_;
goto v___jp_607_;
}
default: 
{
v___y_608_ = v_stx_566_;
goto v___jp_607_;
}
}
v___jp_588_:
{
lean_object* v___x_593_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 3);
lean_ctor_set(v___x_585_, 0, v___y_591_);
v___x_593_ = v___x_585_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___y_591_);
v___x_593_ = v_reuseFailAlloc_606_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_MessageData_ofFormat(v___x_593_);
lean_inc_ref(v___y_590_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___y_590_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v___x_587_, v___y_589_, v___x_595_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_596_, 0);
lean_dec(v_unused_605_);
v___x_598_ = v___x_596_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_dec(v___x_596_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
return v___x_596_;
}
}
}
v___jp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1, &l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once, _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1);
switch(lean_obj_tag(v_a_583_))
{
case 1:
{
lean_object* v_msg_610_; 
v_msg_610_ = lean_ctor_get(v_a_583_, 0);
lean_inc_ref(v_msg_610_);
lean_dec_ref_known(v_a_583_, 1);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_610_;
goto v___jp_588_;
}
case 4:
{
lean_object* v_msg_611_; 
v_msg_611_ = lean_ctor_get(v_a_583_, 3);
lean_inc_ref(v_msg_611_);
lean_dec_ref_known(v_a_583_, 4);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_611_;
goto v___jp_588_;
}
case 7:
{
lean_object* v_msg_612_; 
v_msg_612_ = lean_ctor_get(v_a_583_, 0);
lean_inc_ref(v_msg_612_);
lean_dec_ref_known(v_a_583_, 1);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_612_;
goto v___jp_588_;
}
case 8:
{
lean_object* v_msg_613_; 
v_msg_613_ = lean_ctor_get(v_a_583_, 0);
lean_inc_ref(v_msg_613_);
lean_dec_ref_known(v_a_583_, 1);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_613_;
goto v___jp_588_;
}
case 9:
{
lean_object* v_msg_614_; 
v_msg_614_ = lean_ctor_get(v_a_583_, 0);
lean_inc_ref(v_msg_614_);
lean_dec_ref_known(v_a_583_, 1);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_614_;
goto v___jp_588_;
}
default: 
{
lean_object* v_msg_615_; 
v_msg_615_ = lean_ctor_get(v_a_583_, 1);
lean_inc_ref(v_msg_615_);
lean_dec(v_a_583_);
v___y_589_ = v___y_608_;
v___y_590_ = v___x_609_;
v___y_591_ = v_msg_615_;
goto v___jp_588_;
}
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v_toState_624_; lean_object* v_missingFormatters_625_; lean_object* v_partialFormatters_626_; lean_object* v_buckets_627_; lean_object* v___x_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v___x_631_; 
lean_dec(v_stx_566_);
v_a_623_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_582_, 1);
v_toState_624_ = lean_ctor_get(v_a_623_, 0);
lean_inc_ref(v_toState_624_);
lean_dec(v_a_623_);
v_missingFormatters_625_ = lean_ctor_get(v_toState_624_, 3);
lean_inc_ref(v_missingFormatters_625_);
v_partialFormatters_626_ = lean_ctor_get(v_toState_624_, 4);
lean_inc_ref(v_partialFormatters_626_);
lean_dec_ref(v_toState_624_);
v_buckets_627_ = lean_ctor_get(v_missingFormatters_625_, 1);
lean_inc_ref(v_buckets_627_);
lean_dec_ref(v_missingFormatters_625_);
v___x_628_ = lean_box(0);
v_sz_629_ = lean_array_size(v_buckets_627_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v_buckets_627_, v_sz_629_, v___x_630_, v___x_628_, v_a_567_, v_a_568_);
lean_dec_ref(v_buckets_627_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_buckets_632_; size_t v_sz_633_; lean_object* v___x_634_; 
lean_dec_ref_known(v___x_631_, 1);
v_buckets_632_ = lean_ctor_get(v_partialFormatters_626_, 1);
lean_inc_ref(v_buckets_632_);
lean_dec_ref(v_partialFormatters_626_);
v_sz_633_ = lean_array_size(v_buckets_632_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_buckets_632_, v_sz_633_, v___x_630_, v___x_628_, v_a_567_, v_a_568_);
lean_dec_ref(v_buckets_632_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_642_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_628_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_628_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
return v___x_634_;
}
}
else
{
lean_dec_ref(v_partialFormatters_626_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object* v_stx_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_stx_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6(lean_object* v_msgData_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_648_, v___y_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__6(v_msgData_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg(lean_object* v_o_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v___x_663_; lean_object* v_toEnvExtension_664_; lean_object* v_asyncMode_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_merged_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v___x_661_ = lean_st_ref_get(v___y_659_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_ref(v_env_662_);
lean_dec(v___x_661_);
v___x_663_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_664_ = lean_ctor_get(v___x_663_, 0);
v_asyncMode_665_ = lean_ctor_get(v_toEnvExtension_664_, 2);
v___x_666_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_667_ = lean_box(0);
v___x_668_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_666_, v___x_663_, v_env_662_, v_asyncMode_665_, v___x_667_);
v_merged_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_668_, 1);
lean_dec(v_unused_678_);
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_merged_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v_merged_669_);
lean_ctor_set(v___x_671_, 0, v_o_658_);
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_o_658_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_merged_669_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg___boxed(lean_object* v_o_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg(v_o_679_, v___y_680_);
lean_dec(v___y_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0(lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; lean_object* v_scopes_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_opts_690_; lean_object* v___x_691_; 
v___x_686_ = lean_st_ref_get(v___y_684_);
v_scopes_687_ = lean_ctor_get(v___x_686_, 2);
lean_inc(v_scopes_687_);
lean_dec(v___x_686_);
v___x_688_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_689_ = l_List_head_x21___redArg(v___x_688_, v_scopes_687_);
lean_dec(v_scopes_687_);
v_opts_690_ = lean_ctor_get(v___x_689_, 1);
lean_inc_ref(v_opts_690_);
lean_dec(v___x_689_);
v___x_691_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg(v_opts_690_, v___y_684_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0___boxed(lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0(v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_missingFormatter___lam__0(lean_object* v_cmdStx_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_713_; 
v___x_700_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0(v___y_697_, v___y_698_);
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_713_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_toOptions_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_toOptions_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_toOptions_705_);
lean_dec(v_a_701_);
v___x_706_ = l_Lean_Linter_linter_missingFormatter;
v___x_707_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1_spec__7(v_toOptions_705_, v___x_706_);
lean_dec_ref(v_toOptions_705_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_cmdStx_696_);
v___x_708_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_708_);
v___x_710_ = v___x_703_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v___x_712_; 
lean_del_object(v___x_703_);
v___x_712_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_cmdStx_696_, v___y_697_, v___y_698_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_missingFormatter___lam__0___boxed(lean_object* v_cmdStx_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Linter_missingFormatter___lam__0(v_cmdStx_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0(lean_object* v_o_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___redArg(v_o_728_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0___boxed(lean_object* v_o_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_missingFormatter_spec__0_spec__0(v_o_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_Linter_missingFormatter));
v___x_740_ = l_Lean_Elab_Command_addLinter(v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2____boxed(lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2_();
return v_res_742_;
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
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_647331892____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_missingFormatter = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_missingFormatter);
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_548683249____hygCtx___hyg_2_();
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

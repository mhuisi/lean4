// Lean compiler output
// Module: Lean.Language.Lean.Util
// Imports: public import Lean.Language.Lean.Types import Lean.Server.InfoUtils
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
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object*);
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Language.Lean.Util"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Language.Lean.findCmdDataAtPos"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: s.infoTree\?.isSome\n        "};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object*);
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object*);
static const lean_closure_object l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_findInfoTreeAtPos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_Lean_moduleData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_Lean_moduleData___closed__0 = (const lean_object*)&l_Lean_Language_Lean_moduleData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData(lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object* v_text_1_, lean_object* v_r_2_, lean_object* v_hoverPos_3_, uint8_t v_includeStop_4_){
_start:
{
if (v_includeStop_4_ == 0)
{
lean_object* v_stop_5_; lean_object* v_source_6_; lean_object* v___x_7_; uint8_t v_isRangeAtEOF_8_; uint8_t v___x_9_; 
v_stop_5_ = lean_ctor_get(v_r_2_, 1);
v_source_6_ = lean_ctor_get(v_text_1_, 0);
v___x_7_ = lean_string_utf8_byte_size(v_source_6_);
v_isRangeAtEOF_8_ = lean_nat_dec_eq(v_stop_5_, v___x_7_);
v___x_9_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_isRangeAtEOF_8_);
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_includeStop_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object* v_text_11_, lean_object* v_r_12_, lean_object* v_hoverPos_13_, lean_object* v_includeStop_14_){
_start:
{
uint8_t v_includeStop_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_includeStop_boxed_15_ = lean_unbox(v_includeStop_14_);
v_res_16_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_11_, v_r_12_, v_hoverPos_13_, v_includeStop_boxed_15_);
lean_dec(v_hoverPos_13_);
lean_dec_ref(v_r_12_);
lean_dec_ref(v_text_11_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object* v_text_18_, lean_object* v_documentRange_19_, lean_object* v_requestedRange_20_, uint8_t v_includeDocumentRangeStop_21_, uint8_t v_includeRequestedRangeStop_22_){
_start:
{
if (v_includeDocumentRangeStop_21_ == 0)
{
lean_object* v_stop_23_; lean_object* v_source_24_; lean_object* v___x_25_; uint8_t v_isDocumentRangeAtEOF_26_; uint8_t v___x_27_; 
v_stop_23_ = lean_ctor_get(v_documentRange_19_, 1);
v_source_24_ = lean_ctor_get(v_text_18_, 0);
v___x_25_ = lean_string_utf8_byte_size(v_source_24_);
v_isDocumentRangeAtEOF_26_ = lean_nat_dec_eq(v_stop_23_, v___x_25_);
v___x_27_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_isDocumentRangeAtEOF_26_, v_includeRequestedRangeStop_22_);
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_includeDocumentRangeStop_21_, v_includeRequestedRangeStop_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object* v_text_29_, lean_object* v_documentRange_30_, lean_object* v_requestedRange_31_, lean_object* v_includeDocumentRangeStop_32_, lean_object* v_includeRequestedRangeStop_33_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_34_; uint8_t v_includeRequestedRangeStop_boxed_35_; uint8_t v_res_36_; lean_object* v_r_37_; 
v_includeDocumentRangeStop_boxed_34_ = lean_unbox(v_includeDocumentRangeStop_32_);
v_includeRequestedRangeStop_boxed_35_ = lean_unbox(v_includeRequestedRangeStop_33_);
v_res_36_ = l_Lean_FileMap_rangeOverlapsRequestedRange(v_text_29_, v_documentRange_30_, v_requestedRange_31_, v_includeDocumentRangeStop_boxed_34_, v_includeRequestedRangeStop_boxed_35_);
lean_dec_ref(v_requestedRange_31_);
lean_dec_ref(v_documentRange_30_);
lean_dec_ref(v_text_29_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object* v_text_38_, lean_object* v_documentRange_39_, lean_object* v_requestedRange_40_, uint8_t v_includeDocumentRangeStop_41_, uint8_t v_includeRequestedRangeStop_42_){
_start:
{
if (v_includeDocumentRangeStop_41_ == 0)
{
lean_object* v_stop_43_; lean_object* v_source_44_; lean_object* v___x_45_; uint8_t v_isDocumentRangeAtEOF_46_; uint8_t v___x_47_; 
v_stop_43_ = lean_ctor_get(v_documentRange_39_, 1);
v_source_44_ = lean_ctor_get(v_text_38_, 0);
v___x_45_ = lean_string_utf8_byte_size(v_source_44_);
v_isDocumentRangeAtEOF_46_ = lean_nat_dec_eq(v_stop_43_, v___x_45_);
v___x_47_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_isDocumentRangeAtEOF_46_, v_includeRequestedRangeStop_42_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_includeDocumentRangeStop_41_, v_includeRequestedRangeStop_42_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object* v_text_49_, lean_object* v_documentRange_50_, lean_object* v_requestedRange_51_, lean_object* v_includeDocumentRangeStop_52_, lean_object* v_includeRequestedRangeStop_53_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_54_; uint8_t v_includeRequestedRangeStop_boxed_55_; uint8_t v_res_56_; lean_object* v_r_57_; 
v_includeDocumentRangeStop_boxed_54_ = lean_unbox(v_includeDocumentRangeStop_52_);
v_includeRequestedRangeStop_boxed_55_ = lean_unbox(v_includeRequestedRangeStop_53_);
v_res_56_ = l_Lean_FileMap_rangeIncludesRequestedRange(v_text_49_, v_documentRange_50_, v_requestedRange_51_, v_includeDocumentRangeStop_boxed_54_, v_includeRequestedRangeStop_boxed_55_);
lean_dec_ref(v_requestedRange_51_);
lean_dec_ref(v_documentRange_50_);
lean_dec_ref(v_text_49_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(0u);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
v___x_60_ = lean_unsigned_to_nat(1u);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(v_x_61_);
lean_dec(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object* v_t_63_, lean_object* v_k_64_){
_start:
{
if (lean_obj_tag(v_t_63_) == 0)
{
return v_k_64_;
}
else
{
uint8_t v_foldChildren_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_foldChildren_65_ = lean_ctor_get_uint8(v_t_63_, 0);
v___x_66_ = lean_box(v_foldChildren_65_);
v___x_67_ = lean_apply_1(v_k_64_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object* v_t_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_68_, v_k_69_);
lean_dec(v_t_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_t_79_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object* v_t_83_, lean_object* v_done_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_83_, v_done_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object* v_t_86_, lean_object* v_done_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(v_t_86_, v_done_87_);
lean_dec(v_t_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_done_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_90_, v_done_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_done_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(v_motive_94_, v_t_95_, v_h_96_, v_done_97_);
lean_dec(v_t_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object* v_t_99_, lean_object* v_proceed_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_99_, v_proceed_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object* v_t_102_, lean_object* v_proceed_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(v_t_102_, v_proceed_103_);
lean_dec(v_t_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_proceed_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_106_, v_proceed_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_proceed_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(v_motive_110_, v_t_111_, v_h_112_, v_proceed_113_);
lean_dec(v_t_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object* v_f_115_, lean_object* v_tail_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_snd_118_; uint8_t v___x_119_; 
v_snd_118_ = lean_ctor_get(v_x_117_, 1);
v___x_119_ = lean_unbox(v_snd_118_);
if (v___x_119_ == 0)
{
lean_object* v_fst_120_; lean_object* v___x_121_; 
v_fst_120_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_fst_120_);
lean_dec_ref(v_x_117_);
v___x_121_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_115_, v_fst_120_, v_tail_116_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_tail_116_);
lean_dec_ref(v_f_115_);
v___x_122_ = lean_task_pure(v_x_117_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object* v_f_123_, lean_object* v_tail_124_, lean_object* v_head_125_, lean_object* v___f_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_snd_128_; 
v_snd_128_ = lean_ctor_get(v_x_127_, 1);
if (lean_obj_tag(v_snd_128_) == 1)
{
uint8_t v_foldChildren_129_; 
v_foldChildren_129_ = lean_ctor_get_uint8(v_snd_128_, 0);
if (v_foldChildren_129_ == 0)
{
lean_object* v_fst_130_; lean_object* v___x_131_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
v_fst_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_130_);
lean_dec_ref(v_x_127_);
v___x_131_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_123_, v_fst_130_, v_tail_124_);
return v___x_131_;
}
else
{
lean_object* v_fst_132_; lean_object* v_task_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v_subtreeTask_136_; lean_object* v___x_137_; 
lean_dec(v_tail_124_);
v_fst_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v_x_127_);
v_task_133_ = lean_ctor_get(v_head_125_, 3);
lean_inc_ref(v_task_133_);
lean_dec_ref(v_head_125_);
v___f_134_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_134_, 0, v_f_123_);
lean_closure_set(v___f_134_, 1, v_fst_132_);
v___x_135_ = lean_unsigned_to_nat(0u);
v_subtreeTask_136_ = lean_task_bind(v_task_133_, v___f_134_, v___x_135_, v_foldChildren_129_);
v___x_137_ = lean_task_bind(v_subtreeTask_136_, v___f_126_, v___x_135_, v_foldChildren_129_);
return v___x_137_;
}
}
else
{
lean_object* v_fst_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
lean_dec(v_tail_124_);
lean_dec_ref(v_f_123_);
v_fst_138_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v_x_127_, 1);
lean_dec(v_unused_149_);
v___x_140_ = v_x_127_;
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_fst_138_);
lean_dec(v_x_127_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = 1;
v___x_143_ = lean_box(v___x_142_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_147_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_task_pure(v___x_145_);
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object* v_f_150_, lean_object* v_acc_151_, lean_object* v_a_152_){
_start:
{
if (lean_obj_tag(v_a_152_) == 0)
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref(v_f_150_);
v___x_153_ = 0;
v___x_154_ = lean_box(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_acc_151_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_task_pure(v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v_head_157_ = lean_ctor_get(v_a_152_, 0);
lean_inc_n(v_head_157_, 2);
v_tail_158_ = lean_ctor_get(v_a_152_, 1);
lean_inc_n(v_tail_158_, 2);
lean_dec_ref_known(v_a_152_, 2);
lean_inc_ref_n(v_f_150_, 2);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_159_, 0, v_f_150_);
lean_closure_set(v___f_159_, 1, v_tail_158_);
v___f_160_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2), 5, 4);
lean_closure_set(v___f_160_, 0, v_f_150_);
lean_closure_set(v___f_160_, 1, v_tail_158_);
lean_closure_set(v___f_160_, 2, v_head_157_);
lean_closure_set(v___f_160_, 3, v___f_159_);
v___x_161_ = lean_apply_2(v_f_150_, v_head_157_, v_acc_151_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = 1;
v___x_164_ = lean_task_bind(v___x_161_, v___f_160_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object* v_f_165_, lean_object* v_acc_166_, lean_object* v_tree_167_){
_start:
{
lean_object* v_children_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_children_168_ = lean_ctor_get(v_tree_167_, 1);
lean_inc_ref(v_children_168_);
lean_dec_ref(v_tree_167_);
v___x_169_ = lean_array_to_list(v_children_168_);
v___x_170_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_165_, v_acc_166_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object* v_f_171_, lean_object* v_fst_172_, lean_object* v_tree_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_171_, v_fst_172_, v_tree_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object* v_00_u03b1_175_, lean_object* v_f_176_, lean_object* v_acc_177_, lean_object* v_tree_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_176_, v_acc_177_, v_tree_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object* v_00_u03b1_180_, lean_object* v_f_181_, lean_object* v_acc_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_181_, v_acc_182_, v_a_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object* v_x_185_){
_start:
{
lean_object* v_fst_186_; 
v_fst_186_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_fst_186_);
return v_fst_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(v_x_187_);
lean_dec_ref(v_x_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object* v_tree_190_, lean_object* v_init_191_, lean_object* v_f_192_){
_start:
{
lean_object* v___f_193_; lean_object* v_t_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___f_193_ = ((lean_object*)(l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0));
v_t_194_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_192_, v_init_191_, v_tree_190_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = 1;
v___x_197_ = lean_task_map(v___f_193_, v_t_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object* v_00_u03b1_198_, lean_object* v_tree_199_, lean_object* v_init_200_, lean_object* v_f_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_199_, v_init_200_, v_f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t v___x_203_, lean_object* v___x_204_, lean_object* v_tree_205_){
_start:
{
lean_object* v_element_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_219_; 
v_element_206_ = lean_ctor_get(v_tree_205_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_tree_205_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_tree_205_, 1);
lean_dec(v_unused_220_);
v___x_208_ = v_tree_205_;
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_element_206_);
lean_dec(v_tree_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_infoTree_x3f_210_; 
v_infoTree_x3f_210_ = lean_ctor_get(v_element_206_, 2);
lean_inc(v_infoTree_x3f_210_);
lean_dec_ref(v_element_206_);
if (lean_obj_tag(v_infoTree_x3f_210_) == 1)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec(v___x_204_);
v___x_211_ = lean_box(0);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_211_);
lean_ctor_set(v___x_208_, 0, v_infoTree_x3f_210_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_infoTree_x3f_210_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_dec(v_infoTree_x3f_210_);
v___x_215_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_215_, 0, v___x_203_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_215_);
lean_ctor_set(v___x_208_, 0, v___x_204_);
v___x_217_ = v___x_208_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_tree_223_){
_start:
{
uint8_t v___x_468__boxed_224_; lean_object* v_res_225_; 
v___x_468__boxed_224_ = lean_unbox(v___x_221_);
v_res_225_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_468__boxed_224_, v___x_222_, v_tree_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object* v_text_230_, lean_object* v_hoverPos_231_, uint8_t v_includeStop_232_, lean_object* v___x_233_, lean_object* v_snap_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_stx_x3f_236_; 
v_stx_x3f_236_ = lean_ctor_get(v_snap_234_, 0);
lean_inc(v_stx_x3f_236_);
if (lean_obj_tag(v_stx_x3f_236_) == 1)
{
lean_object* v_task_237_; lean_object* v_val_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v_task_237_ = lean_ctor_get(v_snap_234_, 3);
lean_inc_ref(v_task_237_);
lean_dec_ref(v_snap_234_);
v_val_238_ = lean_ctor_get(v_stx_x3f_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_stx_x3f_236_, 1);
v___x_239_ = 1;
v___x_240_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_238_, v___x_239_);
lean_dec(v_val_238_);
if (lean_obj_tag(v___x_240_) == 1)
{
lean_object* v_val_241_; uint8_t v___x_242_; 
v_val_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_230_, v_val_241_, v_hoverPos_231_, v_includeStop_232_);
lean_dec(v_val_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_task_237_);
v___x_243_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_233_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_task_pure(v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_box(v___x_242_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v___x_246_);
lean_closure_set(v___f_247_, 1, v___x_233_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_task_map(v___f_247_, v_task_237_, v___x_248_, v___x_242_);
return v___x_249_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___x_240_);
lean_dec_ref(v_task_237_);
v___x_250_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_233_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_task_pure(v___x_251_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_stx_x3f_236_);
lean_dec_ref(v_snap_234_);
v___x_253_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_233_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_task_pure(v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object* v_text_256_, lean_object* v_hoverPos_257_, lean_object* v_includeStop_258_, lean_object* v___x_259_, lean_object* v_snap_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_includeStop_boxed_262_; lean_object* v_res_263_; 
v_includeStop_boxed_262_ = lean_unbox(v_includeStop_258_);
v_res_263_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_256_, v_hoverPos_257_, v_includeStop_boxed_262_, v___x_259_, v_snap_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_hoverPos_257_);
lean_dec_ref(v_text_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* v_text_264_, lean_object* v_tree_265_, lean_object* v_hoverPos_266_, uint8_t v_includeStop_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_box(v_includeStop_267_);
v___f_270_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed), 6, 4);
lean_closure_set(v___f_270_, 0, v_text_264_);
lean_closure_set(v___f_270_, 1, v_hoverPos_266_);
lean_closure_set(v___f_270_, 2, v___x_269_);
lean_closure_set(v___f_270_, 3, v___x_268_);
v___x_271_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_265_, v___x_268_, v___f_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* v_text_272_, lean_object* v_tree_273_, lean_object* v_hoverPos_274_, lean_object* v_includeStop_275_){
_start:
{
uint8_t v_includeStop_boxed_276_; lean_object* v_res_277_; 
v_includeStop_boxed_276_ = lean_unbox(v_includeStop_275_);
v_res_277_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_272_, v_tree_273_, v_hoverPos_274_, v_includeStop_boxed_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object* v_requestedRange_278_, uint8_t v___x_279_, lean_object* v_f_280_, lean_object* v_ctx_281_, lean_object* v_i_282_, lean_object* v_acc_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Elab_Info_range_x3f(v_i_282_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; uint8_t v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = l_Lean_Syntax_Range_overlaps(v_val_285_, v_requestedRange_278_, v___x_279_, v___x_279_);
lean_dec(v_val_285_);
if (v___x_286_ == 0)
{
lean_dec_ref(v_i_282_);
lean_dec_ref(v_ctx_281_);
lean_dec(v_f_280_);
return v_acc_283_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_3(v_f_280_, v_ctx_281_, v_i_282_, v_acc_283_);
return v___x_287_;
}
}
else
{
lean_dec(v___x_284_);
lean_dec_ref(v_i_282_);
lean_dec_ref(v_ctx_281_);
lean_dec(v_f_280_);
return v_acc_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object* v_requestedRange_288_, lean_object* v___x_289_, lean_object* v_f_290_, lean_object* v_ctx_291_, lean_object* v_i_292_, lean_object* v_acc_293_){
_start:
{
uint8_t v___x_630__boxed_294_; lean_object* v_res_295_; 
v___x_630__boxed_294_ = lean_unbox(v___x_289_);
v_res_295_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_288_, v___x_630__boxed_294_, v_f_290_, v_ctx_291_, v_i_292_, v_acc_293_);
lean_dec_ref(v_requestedRange_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object* v___f_296_, lean_object* v_acc_297_, uint8_t v___x_298_, lean_object* v_tree_299_){
_start:
{
lean_object* v_element_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_315_; 
v_element_300_ = lean_ctor_get(v_tree_299_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_tree_299_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v_tree_299_, 1);
lean_dec(v_unused_316_);
v___x_302_ = v_tree_299_;
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_element_300_);
lean_dec(v_tree_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_infoTree_x3f_304_; 
v_infoTree_x3f_304_ = lean_ctor_get(v_element_300_, 2);
lean_inc(v_infoTree_x3f_304_);
lean_dec_ref(v_element_300_);
if (lean_obj_tag(v_infoTree_x3f_304_) == 1)
{
lean_object* v_val_305_; lean_object* v_acc_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v_val_305_ = lean_ctor_get(v_infoTree_x3f_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_infoTree_x3f_304_, 1);
v_acc_306_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_296_, v_acc_297_, v_val_305_);
v___x_307_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_307_, 0, v___x_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_307_);
lean_ctor_set(v___x_302_, 0, v_acc_306_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_acc_306_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_infoTree_x3f_304_);
lean_dec(v___f_296_);
v___x_311_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_311_, 0, v___x_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_311_);
lean_ctor_set(v___x_302_, 0, v_acc_297_);
v___x_313_ = v___x_302_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_acc_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object* v___f_317_, lean_object* v_acc_318_, lean_object* v___x_319_, lean_object* v_tree_320_){
_start:
{
uint8_t v___x_642__boxed_321_; lean_object* v_res_322_; 
v___x_642__boxed_321_ = lean_unbox(v___x_319_);
v_res_322_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_317_, v_acc_318_, v___x_642__boxed_321_, v_tree_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object* v_requestedRange_323_, lean_object* v_f_324_, lean_object* v_snap_325_, lean_object* v_acc_326_){
_start:
{
lean_object* v_stx_x3f_327_; 
v_stx_x3f_327_ = lean_ctor_get(v_snap_325_, 0);
lean_inc(v_stx_x3f_327_);
if (lean_obj_tag(v_stx_x3f_327_) == 1)
{
lean_object* v_task_328_; lean_object* v_val_329_; uint8_t v___x_330_; lean_object* v___x_331_; 
v_task_328_ = lean_ctor_get(v_snap_325_, 3);
lean_inc_ref(v_task_328_);
lean_dec_ref(v_snap_325_);
v_val_329_ = lean_ctor_get(v_stx_x3f_327_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v_stx_x3f_327_, 1);
v___x_330_ = 1;
v___x_331_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_329_, v___x_330_);
lean_dec(v_val_329_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; uint8_t v___x_333_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = l_Lean_Syntax_Range_overlaps(v_val_332_, v_requestedRange_323_, v___x_330_, v___x_330_);
lean_dec(v_val_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_task_328_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_334_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_acc_326_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_task_pure(v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_box(v___x_330_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_338_, 0, v_requestedRange_323_);
lean_closure_set(v___f_338_, 1, v___x_337_);
lean_closure_set(v___f_338_, 2, v_f_324_);
v___x_339_ = lean_box(v___x_330_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_340_, 0, v___f_338_);
lean_closure_set(v___f_340_, 1, v_acc_326_);
lean_closure_set(v___f_340_, 2, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_task_map(v___f_340_, v_task_328_, v___x_341_, v___x_330_);
return v___x_342_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_331_);
lean_dec_ref(v_task_328_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_343_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_acc_326_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_task_pure(v___x_344_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_stx_x3f_327_);
lean_dec_ref(v_snap_325_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_346_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_acc_326_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_task_pure(v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object* v_tree_349_, lean_object* v_requestedRange_350_, lean_object* v_init_351_, lean_object* v_f_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2), 4, 2);
lean_closure_set(v___f_353_, 0, v_requestedRange_350_);
lean_closure_set(v___f_353_, 1, v_f_352_);
v___x_354_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_349_, v_init_351_, v___f_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object* v_00_u03b1_355_, lean_object* v_tree_356_, lean_object* v_requestedRange_357_, lean_object* v_init_358_, lean_object* v_f_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_356_, v_requestedRange_357_, v_init_358_, v_f_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object* v_log_361_, uint8_t v___x_362_, lean_object* v_tree_363_){
_start:
{
lean_object* v_element_364_; lean_object* v_diagnostics_365_; lean_object* v_msgLog_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_element_364_ = lean_ctor_get(v_tree_363_, 0);
lean_inc_ref(v_element_364_);
lean_dec_ref(v_tree_363_);
v_diagnostics_365_ = lean_ctor_get(v_element_364_, 1);
lean_inc_ref(v_diagnostics_365_);
lean_dec_ref(v_element_364_);
v_msgLog_366_ = lean_ctor_get(v_diagnostics_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_diagnostics_365_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_diagnostics_365_, 1);
lean_dec(v_unused_376_);
v___x_368_ = v_diagnostics_365_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_msgLog_366_);
lean_dec(v_diagnostics_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = l_Lean_MessageLog_append(v_log_361_, v_msgLog_366_);
v___x_371_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_371_, 0, v___x_362_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_371_);
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object* v_log_377_, lean_object* v___x_378_, lean_object* v_tree_379_){
_start:
{
uint8_t v___x_421__boxed_380_; lean_object* v_res_381_; 
v___x_421__boxed_380_ = lean_unbox(v___x_378_);
v_res_381_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_377_, v___x_421__boxed_380_, v_tree_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object* v_requestedRange_382_, lean_object* v_snap_383_, lean_object* v_log_384_){
_start:
{
lean_object* v_stx_x3f_385_; 
v_stx_x3f_385_ = lean_ctor_get(v_snap_383_, 0);
lean_inc(v_stx_x3f_385_);
if (lean_obj_tag(v_stx_x3f_385_) == 1)
{
lean_object* v_task_386_; lean_object* v_val_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v_task_386_ = lean_ctor_get(v_snap_383_, 3);
lean_inc_ref(v_task_386_);
lean_dec_ref(v_snap_383_);
v_val_387_ = lean_ctor_get(v_stx_x3f_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_stx_x3f_385_, 1);
v___x_388_ = 1;
v___x_389_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_387_, v___x_388_);
lean_dec(v_val_387_);
if (lean_obj_tag(v___x_389_) == 1)
{
lean_object* v_val_390_; uint8_t v___x_391_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = l_Lean_Syntax_Range_overlaps(v_val_390_, v_requestedRange_382_, v___x_388_, v___x_388_);
lean_dec(v_val_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_task_386_);
v___x_392_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_392_, 0, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_log_384_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_task_pure(v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(v___x_388_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed), 3, 2);
lean_closure_set(v___f_396_, 0, v_log_384_);
lean_closure_set(v___f_396_, 1, v___x_395_);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_task_map(v___f_396_, v_task_386_, v___x_397_, v___x_388_);
return v___x_398_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v___x_389_);
lean_dec_ref(v_task_386_);
v___x_399_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_log_384_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_task_pure(v___x_400_);
return v___x_401_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_stx_x3f_385_);
lean_dec_ref(v_snap_383_);
v___x_402_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_log_384_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_task_pure(v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object* v_requestedRange_405_, lean_object* v_snap_406_, lean_object* v_log_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(v_requestedRange_405_, v_snap_406_, v_log_407_);
lean_dec_ref(v_requestedRange_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object* v_tree_409_, lean_object* v_requestedRange_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed), 3, 1);
lean_closure_set(v___f_411_, 0, v_requestedRange_410_);
v___x_412_ = l_Lean_MessageLog_empty;
v___x_413_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_409_, v___x_412_, v___f_411_);
return v___x_413_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object* v_hoverPos_414_, lean_object* v_cmdParsed_415_){
_start:
{
lean_object* v_stx_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v_stx_416_ = lean_ctor_get(v_cmdParsed_415_, 1);
v___x_417_ = 1;
v___x_418_ = l_Lean_Syntax_getPos_x3f(v_stx_416_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 1)
{
lean_object* v_val_419_; uint8_t v___x_420_; 
v_val_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = lean_nat_dec_lt(v_hoverPos_414_, v_val_419_);
lean_dec(v_val_419_);
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
lean_dec(v___x_418_);
v___x_421_ = 0;
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* v_hoverPos_422_, lean_object* v_cmdParsed_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_422_, v_cmdParsed_423_);
lean_dec_ref(v_cmdParsed_423_);
lean_dec(v_hoverPos_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object* v_text_426_, lean_object* v_hoverPos_427_, lean_object* v_cmdParsed_428_){
_start:
{
lean_object* v_stx_429_; uint8_t v___x_430_; lean_object* v___x_431_; 
v_stx_429_ = lean_ctor_get(v_cmdParsed_428_, 1);
v___x_430_ = 1;
v___x_431_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_429_, v___x_430_);
if (lean_obj_tag(v___x_431_) == 1)
{
lean_object* v_val_432_; uint8_t v___x_433_; uint8_t v___x_434_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = 0;
v___x_434_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_426_, v_val_432_, v_hoverPos_427_, v___x_433_);
lean_dec(v_val_432_);
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
lean_dec(v___x_431_);
v___x_435_ = 0;
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object* v_text_436_, lean_object* v_hoverPos_437_, lean_object* v_cmdParsed_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_436_, v_hoverPos_437_, v_cmdParsed_438_);
lean_dec_ref(v_cmdParsed_438_);
lean_dec(v_hoverPos_437_);
lean_dec_ref(v_text_436_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_task_pure(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object* v_text_443_, lean_object* v_hoverPos_444_, lean_object* v_cmdParsed_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_443_, v_hoverPos_444_, v_cmdParsed_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
v___x_447_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_444_, v_cmdParsed_445_);
if (v___x_447_ == 0)
{
lean_object* v_nextCmdSnap_x3f_448_; 
v_nextCmdSnap_x3f_448_ = lean_ctor_get(v_cmdParsed_445_, 4);
lean_inc(v_nextCmdSnap_x3f_448_);
lean_dec_ref(v_cmdParsed_445_);
if (lean_obj_tag(v_nextCmdSnap_x3f_448_) == 0)
{
lean_object* v___x_449_; 
lean_dec(v_hoverPos_444_);
lean_dec_ref(v_text_443_);
v___x_449_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v_task_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_val_450_ = lean_ctor_get(v_nextCmdSnap_x3f_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_nextCmdSnap_x3f_448_, 1);
v_task_451_ = lean_ctor_get(v_val_450_, 3);
lean_inc_ref(v_task_451_);
lean_dec(v_val_450_);
v___x_452_ = 1;
v___x_453_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_453_, 0, v_text_443_);
lean_closure_set(v___x_453_, 1, v_hoverPos_444_);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_task_bind(v_task_451_, v___x_453_, v___x_454_, v___x_452_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v_cmdParsed_445_);
lean_dec(v_hoverPos_444_);
lean_dec_ref(v_text_443_);
v___x_456_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_456_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_hoverPos_444_);
lean_dec_ref(v_text_443_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v_cmdParsed_445_);
v___x_458_ = lean_task_pure(v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object* v_text_459_, lean_object* v_hoverPos_460_, lean_object* v_headerProcessed_461_){
_start:
{
lean_object* v_result_x3f_462_; 
v_result_x3f_462_ = lean_ctor_get(v_headerProcessed_461_, 2);
lean_inc(v_result_x3f_462_);
lean_dec_ref(v_headerProcessed_461_);
if (lean_obj_tag(v_result_x3f_462_) == 1)
{
lean_object* v_val_463_; lean_object* v_firstCmdSnap_464_; lean_object* v_task_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; 
v_val_463_ = lean_ctor_get(v_result_x3f_462_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v_result_x3f_462_, 1);
v_firstCmdSnap_464_ = lean_ctor_get(v_val_463_, 1);
lean_inc_ref(v_firstCmdSnap_464_);
lean_dec(v_val_463_);
v_task_465_ = lean_ctor_get(v_firstCmdSnap_464_, 3);
lean_inc_ref(v_task_465_);
lean_dec_ref(v_firstCmdSnap_464_);
v___x_466_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_466_, 0, v_text_459_);
lean_closure_set(v___x_466_, 1, v_hoverPos_460_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = 1;
v___x_469_ = lean_task_bind(v_task_465_, v___x_466_, v___x_467_, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_result_x3f_462_);
lean_dec(v_hoverPos_460_);
lean_dec_ref(v_text_459_);
v___x_470_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object* v_initSnap_471_, lean_object* v_text_472_, lean_object* v_hoverPos_473_){
_start:
{
lean_object* v_result_x3f_474_; 
v_result_x3f_474_ = lean_ctor_get(v_initSnap_471_, 4);
lean_inc(v_result_x3f_474_);
lean_dec_ref(v_initSnap_471_);
if (lean_obj_tag(v_result_x3f_474_) == 1)
{
lean_object* v_val_475_; lean_object* v_processedSnap_476_; lean_object* v_task_477_; lean_object* v___f_478_; lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; 
v_val_475_ = lean_ctor_get(v_result_x3f_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v_result_x3f_474_, 1);
v_processedSnap_476_ = lean_ctor_get(v_val_475_, 1);
lean_inc_ref(v_processedSnap_476_);
lean_dec(v_val_475_);
v_task_477_ = lean_ctor_get(v_processedSnap_476_, 3);
lean_inc_ref(v_task_477_);
lean_dec_ref(v_processedSnap_476_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdParsedSnap___lam__0), 3, 2);
lean_closure_set(v___f_478_, 0, v_text_472_);
lean_closure_set(v___f_478_, 1, v_hoverPos_473_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = 1;
v___x_481_ = lean_task_bind(v_task_477_, v___f_478_, v___x_479_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; 
lean_dec(v_result_x3f_474_);
lean_dec(v_hoverPos_473_);
lean_dec_ref(v_text_472_);
v___x_482_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object* v_msg_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_panic_fn_borrowed(v___x_484_, v_msg_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_489_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2));
v___x_490_ = lean_unsigned_to_nat(8u);
v___x_491_ = lean_unsigned_to_nat(199u);
v___x_492_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1));
v___x_493_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0));
v___x_494_ = l_mkPanicMessageWithDecl(v___x_493_, v___x_492_, v___x_491_, v___x_490_, v___x_489_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object* v_stx_495_, lean_object* v_s_496_){
_start:
{
lean_object* v_infoTree_x3f_497_; 
v_infoTree_x3f_497_ = lean_ctor_get(v_s_496_, 2);
lean_inc(v_infoTree_x3f_497_);
lean_dec_ref(v_s_496_);
if (lean_obj_tag(v_infoTree_x3f_497_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_stx_495_);
v___x_498_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3, &l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3);
v___x_499_ = l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_val_500_ = lean_ctor_get(v_infoTree_x3f_497_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_infoTree_x3f_497_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v_infoTree_x3f_497_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v_infoTree_x3f_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_stx_495_);
lean_ctor_set(v___x_504_, 1, v_val_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object* v_elabSnap_509_, lean_object* v___f_510_, lean_object* v_stx_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_infoTreeSnap_513_; lean_object* v_task_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
lean_dec(v_stx_511_);
v_infoTreeSnap_513_ = lean_ctor_get(v_elabSnap_509_, 3);
lean_inc_ref(v_infoTreeSnap_513_);
lean_dec_ref(v_elabSnap_509_);
v_task_514_ = lean_ctor_get(v_infoTreeSnap_513_, 3);
lean_inc_ref(v_task_514_);
lean_dec_ref(v_infoTreeSnap_513_);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = 1;
v___x_517_ = lean_task_map(v___f_510_, v_task_514_, v___x_515_, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v_val_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v___f_510_);
lean_dec_ref(v_elabSnap_509_);
v_val_518_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_527_ == 0)
{
v___x_520_ = v_x_512_;
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_val_518_);
lean_dec(v_x_512_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_stx_511_);
lean_ctor_set(v___x_522_, 1, v_val_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_task_pure(v___x_524_);
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object* v_s_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_toSnapshot_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v_toSnapshot_532_ = lean_ctor_get(v_s_530_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_s_530_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v_s_530_, 1);
lean_dec(v_unused_542_);
v___x_534_ = v_s_530_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_toSnapshot_532_);
lean_dec(v_s_530_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_532_, v___y_531_);
v___x_537_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_537_);
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object* v_s_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(v_s_543_, v___y_544_);
lean_dec_ref(v___y_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object* v_t_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___f_549_; lean_object* v___x_550_; 
v___f_549_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0));
v___x_550_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_547_, v___f_549_, v_a_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object* v_t_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_t_551_, v_a_552_);
lean_dec_ref(v_a_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object* v_t_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; 
v___f_557_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0));
v___x_558_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_555_, v___f_557_, v_a_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object* v_t_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_t_559_, v_a_560_);
lean_dec_ref(v_a_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object* v_s_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Language_Snapshot_transform(v_s_562_, v___y_563_);
v___x_565_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object* v_s_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(v_s_567_, v___y_568_);
lean_dec_ref(v___y_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object* v_t_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___f_573_; lean_object* v___x_574_; 
v___f_573_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0));
v___x_574_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_571_, v___f_573_, v_a_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object* v_t_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_t_575_, v_a_576_);
lean_dec_ref(v_a_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object* v_s_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_toSnapshotTreeM_580_; lean_object* v___x_581_; 
v_toSnapshotTreeM_580_ = lean_ctor_get(v_s_578_, 1);
lean_inc_ref(v_toSnapshotTreeM_580_);
lean_dec_ref(v_s_578_);
lean_inc_ref(v___y_579_);
v___x_581_ = lean_apply_1(v_toSnapshotTreeM_580_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object* v_s_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(v_s_582_, v___y_583_);
lean_dec_ref(v___y_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object* v_t_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
v___f_588_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0));
v___x_589_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_586_, v___f_588_, v_a_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object* v_t_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_t_590_, v_a_591_);
lean_dec_ref(v_a_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object* v_a_593_){
_start:
{
lean_object* v_toSnapshot_594_; lean_object* v_elabSnap_595_; lean_object* v_resultSnap_596_; lean_object* v_infoTreeSnap_597_; lean_object* v_reportSnap_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_toSnapshot_594_ = lean_ctor_get(v_a_593_, 0);
lean_inc_ref(v_toSnapshot_594_);
v_elabSnap_595_ = lean_ctor_get(v_a_593_, 1);
lean_inc_ref(v_elabSnap_595_);
v_resultSnap_596_ = lean_ctor_get(v_a_593_, 2);
lean_inc_ref(v_resultSnap_596_);
v_infoTreeSnap_597_ = lean_ctor_get(v_a_593_, 3);
lean_inc_ref(v_infoTreeSnap_597_);
v_reportSnap_598_ = lean_ctor_get(v_a_593_, 4);
lean_inc_ref(v_reportSnap_598_);
lean_dec_ref(v_a_593_);
v___x_599_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_600_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_594_, v___x_599_);
v___x_601_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_elabSnap_595_, v___x_599_);
v___x_602_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_resultSnap_596_, v___x_599_);
v___x_603_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_infoTreeSnap_597_, v___x_599_);
v___x_604_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_reportSnap_598_, v___x_599_);
v___x_605_ = lean_unsigned_to_nat(4u);
v___x_606_ = lean_mk_empty_array_with_capacity(v___x_605_);
v___x_607_ = lean_array_push(v___x_606_, v___x_601_);
v___x_608_ = lean_array_push(v___x_607_, v___x_602_);
v___x_609_ = lean_array_push(v___x_608_, v___x_603_);
v___x_610_ = lean_array_push(v___x_609_, v___x_604_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_600_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = lean_task_pure(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object* v_text_614_, lean_object* v_hoverPos_615_, uint8_t v_includeStop_616_, lean_object* v_x_617_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v___x_618_; 
lean_dec(v_hoverPos_615_);
lean_dec_ref(v_text_614_);
v___x_618_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0);
return v___x_618_;
}
else
{
lean_object* v_val_619_; lean_object* v_stx_620_; lean_object* v_elabSnap_621_; lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; 
v_val_619_ = lean_ctor_get(v_x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v_x_617_, 1);
v_stx_620_ = lean_ctor_get(v_val_619_, 1);
lean_inc_n(v_stx_620_, 2);
v_elabSnap_621_ = lean_ctor_get(v_val_619_, 3);
lean_inc_ref_n(v_elabSnap_621_, 2);
lean_dec(v_val_619_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_622_, 0, v_stx_620_);
v___f_623_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_623_, 0, v_elabSnap_621_);
lean_closure_set(v___f_623_, 1, v___f_622_);
lean_closure_set(v___f_623_, 2, v_stx_620_);
v___x_624_ = l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(v_elabSnap_621_);
v___x_625_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_614_, v___x_624_, v_hoverPos_615_, v_includeStop_616_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = 1;
v___x_628_ = lean_task_bind(v___x_625_, v___f_623_, v___x_626_, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object* v_text_629_, lean_object* v_hoverPos_630_, lean_object* v_includeStop_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_includeStop_boxed_633_; lean_object* v_res_634_; 
v_includeStop_boxed_633_ = lean_unbox(v_includeStop_631_);
v_res_634_ = l_Lean_Language_Lean_findCmdDataAtPos___lam__2(v_text_629_, v_hoverPos_630_, v_includeStop_boxed_633_, v_x_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object* v_initSnap_635_, lean_object* v_text_636_, lean_object* v_hoverPos_637_, uint8_t v_includeStop_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_639_ = lean_box(v_includeStop_638_);
lean_inc(v_hoverPos_637_);
lean_inc_ref(v_text_636_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_640_, 0, v_text_636_);
lean_closure_set(v___f_640_, 1, v_hoverPos_637_);
lean_closure_set(v___f_640_, 2, v___x_639_);
v___x_641_ = l_Lean_Language_Lean_findCmdParsedSnap(v_initSnap_635_, v_text_636_, v_hoverPos_637_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = 1;
v___x_644_ = lean_task_bind(v___x_641_, v___f_640_, v___x_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object* v_initSnap_645_, lean_object* v_text_646_, lean_object* v_hoverPos_647_, lean_object* v_includeStop_648_){
_start:
{
uint8_t v_includeStop_boxed_649_; lean_object* v_res_650_; 
v_includeStop_boxed_649_ = lean_unbox(v_includeStop_648_);
v_res_650_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_645_, v_text_646_, v_hoverPos_647_, v_includeStop_boxed_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(0);
return v___x_652_;
}
else
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_val_653_ = lean_ctor_get(v_x_651_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v_x_651_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v_x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_snd_657_; lean_object* v___x_659_; 
v_snd_657_ = lean_ctor_get(v_val_653_, 1);
lean_inc(v_snd_657_);
lean_dec(v_val_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_snd_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_snd_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object* v_initSnap_663_, lean_object* v_text_664_, lean_object* v_hoverPos_665_, uint8_t v_includeStop_666_){
_start:
{
lean_object* v___f_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; 
v___f_667_ = ((lean_object*)(l_Lean_Language_Lean_findInfoTreeAtPos___closed__0));
v___x_668_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_663_, v_text_664_, v_hoverPos_665_, v_includeStop_666_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = 1;
v___x_671_ = lean_task_map(v___f_667_, v___x_668_, v___x_669_, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object* v_initSnap_672_, lean_object* v_text_673_, lean_object* v_hoverPos_674_, lean_object* v_includeStop_675_){
_start:
{
uint8_t v_includeStop_boxed_676_; lean_object* v_res_677_; 
v_includeStop_boxed_676_ = lean_unbox(v_includeStop_675_);
v_res_677_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_672_, v_text_673_, v_hoverPos_674_, v_includeStop_boxed_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0(lean_object* v_acc_678_, lean_object* v_stx_679_, lean_object* v_parserState_680_, lean_object* v_nextCmdSnap_x3f_681_, lean_object* v_toSnapshot_682_, lean_object* v_cmdResultSnap_683_){
_start:
{
lean_object* v_headerData_684_; lean_object* v_cmdData_685_; uint8_t v_hasParseErrors_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_704_; 
v_headerData_684_ = lean_ctor_get(v_acc_678_, 0);
v_cmdData_685_ = lean_ctor_get(v_acc_678_, 1);
v_hasParseErrors_686_ = lean_ctor_get_uint8(v_acc_678_, sizeof(void*)*2);
v_isSharedCheck_704_ = !lean_is_exclusive(v_acc_678_);
if (v_isSharedCheck_704_ == 0)
{
v___x_688_ = v_acc_678_;
v_isShared_689_ = v_isSharedCheck_704_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_cmdData_685_);
lean_inc(v_headerData_684_);
lean_dec(v_acc_678_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_704_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_cmdState_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___y_694_; 
v_cmdState_690_ = lean_ctor_get(v_cmdResultSnap_683_, 1);
lean_inc_ref(v_cmdState_690_);
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v_stx_679_);
lean_ctor_set(v___x_691_, 1, v_parserState_680_);
lean_ctor_set(v___x_691_, 2, v_cmdState_690_);
v___x_692_ = lean_array_push(v_cmdData_685_, v___x_691_);
if (v_hasParseErrors_686_ == 0)
{
lean_object* v_diagnostics_701_; lean_object* v_msgLog_702_; uint8_t v___x_703_; 
v_diagnostics_701_ = lean_ctor_get(v_toSnapshot_682_, 1);
v_msgLog_702_ = lean_ctor_get(v_diagnostics_701_, 0);
v___x_703_ = l_Lean_MessageLog_hasErrors(v_msgLog_702_);
v___y_694_ = v___x_703_;
goto v___jp_693_;
}
else
{
v___y_694_ = v_hasParseErrors_686_;
goto v___jp_693_;
}
v___jp_693_:
{
lean_object* v_acc_696_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_692_);
v_acc_696_ = v___x_688_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_headerData_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_692_);
v_acc_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_ctor_set_uint8(v_acc_696_, sizeof(void*)*2, v___y_694_);
if (lean_obj_tag(v_nextCmdSnap_x3f_681_) == 1)
{
lean_object* v_val_697_; lean_object* v___x_698_; 
v_val_697_ = lean_ctor_get(v_nextCmdSnap_x3f_681_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v_nextCmdSnap_x3f_681_, 1);
v___x_698_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go(v_val_697_, v_acc_696_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; 
lean_dec(v_nextCmdSnap_x3f_681_);
v___x_699_ = lean_task_pure(v_acc_696_);
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0___boxed(lean_object* v_acc_705_, lean_object* v_stx_706_, lean_object* v_parserState_707_, lean_object* v_nextCmdSnap_x3f_708_, lean_object* v_toSnapshot_709_, lean_object* v_cmdResultSnap_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0(v_acc_705_, v_stx_706_, v_parserState_707_, v_nextCmdSnap_x3f_708_, v_toSnapshot_709_, v_cmdResultSnap_710_);
lean_dec_ref(v_cmdResultSnap_710_);
lean_dec_ref(v_toSnapshot_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__1(lean_object* v_acc_712_, lean_object* v_cmdParsedSnap_713_){
_start:
{
lean_object* v_elabSnap_714_; lean_object* v_resultSnap_715_; lean_object* v_toSnapshot_716_; lean_object* v_stx_717_; lean_object* v_parserState_718_; lean_object* v_nextCmdSnap_x3f_719_; lean_object* v_task_720_; lean_object* v___f_721_; lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v_elabSnap_714_ = lean_ctor_get(v_cmdParsedSnap_713_, 3);
v_resultSnap_715_ = lean_ctor_get(v_elabSnap_714_, 2);
lean_inc_ref(v_resultSnap_715_);
v_toSnapshot_716_ = lean_ctor_get(v_cmdParsedSnap_713_, 0);
lean_inc_ref(v_toSnapshot_716_);
v_stx_717_ = lean_ctor_get(v_cmdParsedSnap_713_, 1);
lean_inc(v_stx_717_);
v_parserState_718_ = lean_ctor_get(v_cmdParsedSnap_713_, 2);
lean_inc_ref(v_parserState_718_);
v_nextCmdSnap_x3f_719_ = lean_ctor_get(v_cmdParsedSnap_713_, 4);
lean_inc(v_nextCmdSnap_x3f_719_);
lean_dec_ref(v_cmdParsedSnap_713_);
v_task_720_ = lean_ctor_get(v_resultSnap_715_, 3);
lean_inc_ref(v_task_720_);
lean_dec_ref(v_resultSnap_715_);
v___f_721_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__0___boxed), 6, 5);
lean_closure_set(v___f_721_, 0, v_acc_712_);
lean_closure_set(v___f_721_, 1, v_stx_717_);
lean_closure_set(v___f_721_, 2, v_parserState_718_);
lean_closure_set(v___f_721_, 3, v_nextCmdSnap_x3f_719_);
lean_closure_set(v___f_721_, 4, v_toSnapshot_716_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = 1;
v___x_724_ = lean_task_bind(v_task_720_, v___f_721_, v___x_722_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go(lean_object* v_cmdParsedSnapTask_725_, lean_object* v_acc_726_){
_start:
{
lean_object* v_task_727_; lean_object* v___f_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v_task_727_ = lean_ctor_get(v_cmdParsedSnapTask_725_, 3);
lean_inc_ref(v_task_727_);
lean_dec_ref(v_cmdParsedSnapTask_725_);
v___f_728_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go___lam__1), 2, 1);
lean_closure_set(v___f_728_, 0, v_acc_726_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = 1;
v___x_731_ = lean_task_bind(v_task_727_, v___f_728_, v___x_729_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData___lam__0(lean_object* v_stx_732_, lean_object* v___x_733_, lean_object* v___x_734_, uint8_t v___x_735_, lean_object* v_acc_736_, lean_object* v_headerProcessedSnap_737_){
_start:
{
lean_object* v_result_x3f_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_758_; 
v_result_x3f_738_ = lean_ctor_get(v_headerProcessedSnap_737_, 2);
v_isSharedCheck_758_ = !lean_is_exclusive(v_headerProcessedSnap_737_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_759_ = lean_ctor_get(v_headerProcessedSnap_737_, 1);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_headerProcessedSnap_737_, 0);
lean_dec(v_unused_760_);
v___x_740_ = v_headerProcessedSnap_737_;
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_result_x3f_738_);
lean_dec(v_headerProcessedSnap_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_758_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_result_x3f_738_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_acc_736_);
v_val_742_ = lean_ctor_get(v_result_x3f_738_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_result_x3f_738_);
if (v_isSharedCheck_756_ == 0)
{
v___x_744_ = v_result_x3f_738_;
v_isShared_745_ = v_isSharedCheck_756_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_result_x3f_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_756_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_cmdState_746_; lean_object* v_firstCmdSnap_747_; lean_object* v___x_749_; 
v_cmdState_746_ = lean_ctor_get(v_val_742_, 0);
lean_inc_ref(v_cmdState_746_);
v_firstCmdSnap_747_ = lean_ctor_get(v_val_742_, 1);
lean_inc_ref(v_firstCmdSnap_747_);
lean_dec(v_val_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v_cmdState_746_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_cmdState_746_);
v___x_749_ = v_reuseFailAlloc_755_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 2, v___x_749_);
lean_ctor_set(v___x_740_, 1, v___x_733_);
lean_ctor_set(v___x_740_, 0, v_stx_732_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_stx_732_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v___x_749_);
v___x_751_ = v_reuseFailAlloc_754_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v_acc_752_; lean_object* v___x_753_; 
v_acc_752_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_acc_752_, 0, v___x_751_);
lean_ctor_set(v_acc_752_, 1, v___x_734_);
lean_ctor_set_uint8(v_acc_752_, sizeof(void*)*2, v___x_735_);
v___x_753_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_moduleData_go(v_firstCmdSnap_747_, v_acc_752_);
return v___x_753_;
}
}
}
}
else
{
lean_object* v___x_757_; 
lean_del_object(v___x_740_);
lean_dec(v_result_x3f_738_);
lean_dec_ref(v___x_734_);
lean_dec(v___x_733_);
lean_dec(v_stx_732_);
v___x_757_ = lean_task_pure(v_acc_736_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData___lam__0___boxed(lean_object* v_stx_761_, lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_acc_765_, lean_object* v_headerProcessedSnap_766_){
_start:
{
uint8_t v___x_209__boxed_767_; lean_object* v_res_768_; 
v___x_209__boxed_767_ = lean_unbox(v___x_764_);
v_res_768_ = l_Lean_Language_Lean_moduleData___lam__0(v_stx_761_, v___x_762_, v___x_763_, v___x_209__boxed_767_, v_acc_765_, v_headerProcessedSnap_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_moduleData(lean_object* v_initSnap_771_){
_start:
{
lean_object* v_stx_772_; lean_object* v_result_x3f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_stx_772_ = lean_ctor_get(v_initSnap_771_, 3);
lean_inc(v_stx_772_);
v_result_x3f_773_ = lean_ctor_get(v_initSnap_771_, 4);
lean_inc(v_result_x3f_773_);
lean_dec_ref(v_initSnap_771_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = ((lean_object*)(l_Lean_Language_Lean_moduleData___closed__0));
if (lean_obj_tag(v_result_x3f_773_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_794_; 
v_val_777_ = lean_ctor_get(v_result_x3f_773_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_result_x3f_773_);
if (v_isSharedCheck_794_ == 0)
{
v___x_779_ = v_result_x3f_773_;
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v_result_x3f_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_processedSnap_781_; lean_object* v_parserState_782_; lean_object* v_task_783_; uint8_t v___x_784_; lean_object* v___x_786_; 
v_processedSnap_781_ = lean_ctor_get(v_val_777_, 1);
lean_inc_ref(v_processedSnap_781_);
v_parserState_782_ = lean_ctor_get(v_val_777_, 0);
lean_inc_ref(v_parserState_782_);
lean_dec(v_val_777_);
v_task_783_ = lean_ctor_get(v_processedSnap_781_, 3);
lean_inc_ref(v_task_783_);
lean_dec_ref(v_processedSnap_781_);
v___x_784_ = 0;
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_parserState_782_);
v___x_786_ = v___x_779_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_parserState_782_);
v___x_786_ = v_reuseFailAlloc_793_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v_acc_788_; lean_object* v___x_789_; lean_object* v___f_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
lean_inc_ref(v___x_786_);
lean_inc(v_stx_772_);
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v_stx_772_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
lean_ctor_set(v___x_787_, 2, v___x_774_);
v_acc_788_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_acc_788_, 0, v___x_787_);
lean_ctor_set(v_acc_788_, 1, v___x_776_);
lean_ctor_set_uint8(v_acc_788_, sizeof(void*)*2, v___x_784_);
v___x_789_ = lean_box(v___x_784_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_moduleData___lam__0___boxed), 6, 5);
lean_closure_set(v___f_790_, 0, v_stx_772_);
lean_closure_set(v___f_790_, 1, v___x_786_);
lean_closure_set(v___f_790_, 2, v___x_776_);
lean_closure_set(v___f_790_, 3, v___x_789_);
lean_closure_set(v___f_790_, 4, v_acc_788_);
v___x_791_ = 1;
v___x_792_ = lean_task_bind(v_task_783_, v___f_790_, v___x_775_, v___x_791_);
return v___x_792_;
}
}
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_result_x3f_773_);
v___x_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_795_, 0, v_stx_772_);
lean_ctor_set(v___x_795_, 1, v___x_774_);
lean_ctor_set(v___x_795_, 2, v___x_774_);
v___x_796_ = 1;
v___x_797_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_776_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*2, v___x_796_);
v___x_798_ = lean_task_pure(v___x_797_);
return v___x_798_;
}
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Lean_Util(builtin);
}
#ifdef __cplusplus
}
#endif

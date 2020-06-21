// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Lean.Util.FindMVar Lean.Meta.Message Lean.Meta.ExprDefEq Lean.Meta.SynthInstance Lean.Meta.Tactic.Util
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1;
lean_object* l_Lean_Meta_renameMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_array_get_size(x_1);
x_6 = l_Lean_Expr_getAppFn___main(x_2);
x_7 = l_Lean_Expr_isMVar(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 2;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_7);
x_8 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_9 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_10);
lean_dec(x_5);
x_17 = 2;
x_18 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 3, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 4, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 6, x_17);
lean_ctor_set(x_2, 0, x_18);
x_19 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_20 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_19, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 2);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 3);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 4);
x_32 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = 2;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 7);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 4, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 5, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 6, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
x_37 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_38 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_37, x_36, x_3);
return x_38;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unify");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lean_indentExpr(x_6);
x_8 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_16, x_4, x_5);
return x_18;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign synthesized instance");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_6, x_11);
lean_dec(x_6);
x_13 = lean_nat_sub(x_5, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_BinderInfo_inhabited;
x_16 = lean_box(x_15);
x_17 = lean_array_get(x_16, x_4, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_Lean_BinderInfo_isInstImplicit(x_18);
if (x_19 == 0)
{
lean_dec(x_14);
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Expr_Inhabited;
x_22 = lean_array_get(x_21, x_3, x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_22);
x_23 = l_Lean_Meta_inferType(x_22, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
x_26 = l_Lean_Meta_synthInstance(x_24, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
x_29 = l_Lean_Meta_isExprDefEq(x_22, x_27, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_12);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_33, x_7, x_32);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_6 = x_12;
x_8 = x_39;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
return x_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
}
}
lean_object* l_Lean_Meta_synthAppInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_get_size(x_3);
lean_inc(x_7);
x_8 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_7, x_7, x_5, x_6);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = l_Lean_Expr_mvarId_x21(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
x_18 = lean_metavar_ctx_is_expr_assigned(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = l_Lean_BinderInfo_inhabited;
x_20 = lean_box(x_19);
x_21 = lean_array_get(x_20, x_2, x_13);
lean_dec(x_13);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_16);
x_24 = l_Lean_Meta_getMVarTag(x_16, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Name_eraseMacroScopes(x_25);
lean_dec(x_25);
x_28 = l_Lean_Name_append___main(x_3, x_27);
x_29 = l_Lean_Meta_renameMVar(x_16, x_28, x_6, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_5 = x_11;
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_dec(x_16);
x_5 = x_11;
goto _start;
}
}
else
{
lean_dec(x_16);
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
}
}
lean_object* l_Lean_Meta_appendParentTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getMVarTag(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Name_isAnonymous(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_array_get_size(x_2);
lean_inc(x_11);
x_12 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_8, x_11, x_11, x_4, x_9);
lean_dec(x_11);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = l_Lean_Name_isAnonymous(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_get_size(x_2);
lean_inc(x_17);
x_18 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_14, x_17, x_17, x_4, x_15);
lean_dec(x_17);
lean_dec(x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_appendParentTag(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_2);
x_7 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_appendParentTag(x_2, x_3, x_4, x_5, x_8);
lean_dec(x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_postprocessAppMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Expr_mvarId_x21(x_1);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_expr_eqv(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_6);
x_14 = l_Lean_Meta_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(0);
x_19 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_5 = x_21;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_25, x_27);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
x_7 = x_26;
goto _start;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_5);
x_17 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_10, x_1, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_push(x_14, x_16);
lean_ctor_set(x_4, 0, x_21);
x_3 = x_12;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_array_push(x_15, x_16);
lean_ctor_set(x_4, 1, x_24);
x_3 = x_12;
x_6 = x_23;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_5);
x_33 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_10, x_1, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_array_push(x_30, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_3 = x_12;
x_4 = x_38;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_array_push(x_31, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_3 = x_12;
x_4 = x_42;
x_6 = x_40;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_5);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1;
x_6 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(x_1, x_1, x_4, x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_toList___rarg(x_9);
lean_dec(x_9);
x_12 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_13 = l_List_append___rarg(x_11, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_19 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_20 = l_List_append___rarg(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_metavar_ctx_is_expr_assigned(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_apply___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lean_Meta_getMVarType(x_1, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_inferType(x_3, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_12, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = 0;
lean_inc(x_4);
x_22 = l_Lean_Meta_forallMetaTelescopeReducing(x_12, x_20, x_21, x_4, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_26, x_26, x_29, x_3);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_28);
x_31 = l_Lean_Meta_isExprDefEq(x_28, x_9, x_4, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_28, x_9, x_4, x_34);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_9);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_4);
lean_inc(x_1);
x_41 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_26, x_27, x_4, x_40);
lean_dec(x_27);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Meta_assignExprMVar(x_1, x_30, x_4, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_26, x_29, x_29, x_4, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_46, x_4, x_47);
lean_dec(x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_31);
if (x_57 == 0)
{
return x_31;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_31, 0);
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_31);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_22);
if (x_61 == 0)
{
return x_22;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_22, 0);
x_63 = lean_ctor_get(x_22, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_22);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_dec(x_14);
x_66 = lean_ctor_get(x_15, 0);
lean_inc(x_66);
lean_dec(x_15);
lean_inc(x_4);
lean_inc(x_9);
x_67 = l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_9, x_4, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_nat_sub(x_66, x_68);
lean_dec(x_68);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = 0;
lean_inc(x_4);
x_73 = l_Lean_Meta_forallMetaTelescopeReducing(x_12, x_71, x_72, x_4, x_69);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_77, x_77, x_80, x_3);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_79);
x_82 = l_Lean_Meta_isExprDefEq(x_79, x_9, x_4, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_2);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_79, x_9, x_4, x_85);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_9);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
lean_inc(x_4);
lean_inc(x_1);
x_92 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_77, x_78, x_4, x_91);
lean_dec(x_78);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Meta_assignExprMVar(x_1, x_81, x_4, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_77, x_80, x_80, x_4, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_97, x_4, x_98);
lean_dec(x_97);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_77);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_94);
if (x_100 == 0)
{
return x_94;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_94, 0);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_94);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_4);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_92);
if (x_104 == 0)
{
return x_92;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_92, 0);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_92);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_82);
if (x_108 == 0)
{
return x_82;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_82, 0);
x_110 = lean_ctor_get(x_82, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_82);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_73);
if (x_112 == 0)
{
return x_73;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_73, 0);
x_114 = lean_ctor_get(x_73, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_73);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_67);
if (x_116 == 0)
{
return x_67;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_67, 0);
x_118 = lean_ctor_get(x_67, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_67);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_14);
if (x_120 == 0)
{
return x_14;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_14, 0);
x_122 = lean_ctor_get(x_14, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_14);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_11);
if (x_124 == 0)
{
return x_11;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_11, 0);
x_126 = lean_ctor_get(x_11, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_11);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_8);
if (x_128 == 0)
{
return x_8;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_6);
if (x_132 == 0)
{
return x_6;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_6, 0);
x_134 = lean_ctor_get(x_6, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_6);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* l_Lean_Meta_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_apply___lambda__1), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 4);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_withLocalContext___rarg(x_10, x_11, x_6, x_3, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_apply___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_apply(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3);
l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Hygiene
// Imports: Init.Control Init.LeanInit Lean.Syntax
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
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__3;
lean_object* l_Lean_Unhygienic_run(lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__6;
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__4;
lean_object* l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Unhygienic_MonadQuotation;
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__1;
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__2;
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2(lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("UnhygienicMain");
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Unhygienic_MonadQuotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_2 = l_Lean_Unhygienic_MonadQuotation___closed__3;
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__6;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_pure___at_Lean_Unhygienic_MonadQuotation___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Unhygienic_MonadQuotation___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Unhygienic_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Unhygienic_run___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = l_Lean_Unhygienic_run___rarg___closed__1;
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Unhygienic_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Unhygienic_run___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Control(lean_object*);
lean_object* initialize_Init_LeanInit(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Hygiene(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LeanInit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Unhygienic_MonadQuotation___closed__1 = _init_l_Lean_Unhygienic_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__1);
l_Lean_Unhygienic_MonadQuotation___closed__2 = _init_l_Lean_Unhygienic_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__2);
l_Lean_Unhygienic_MonadQuotation___closed__3 = _init_l_Lean_Unhygienic_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__3);
l_Lean_Unhygienic_MonadQuotation___closed__4 = _init_l_Lean_Unhygienic_MonadQuotation___closed__4();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__4);
l_Lean_Unhygienic_MonadQuotation___closed__5 = _init_l_Lean_Unhygienic_MonadQuotation___closed__5();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__5);
l_Lean_Unhygienic_MonadQuotation___closed__6 = _init_l_Lean_Unhygienic_MonadQuotation___closed__6();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__6);
l_Lean_Unhygienic_MonadQuotation = _init_l_Lean_Unhygienic_MonadQuotation();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation);
l_Lean_Unhygienic_run___rarg___closed__1 = _init_l_Lean_Unhygienic_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_run___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

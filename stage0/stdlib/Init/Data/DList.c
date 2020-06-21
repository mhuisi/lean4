// Lean compiler output
// Module: Init.Data.DList
// Imports: Init.Data.List.Basic
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
lean_object* l_DList_HasAppend(lean_object*);
lean_object* l_DList_push___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_DList_append___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_DList_toList___rarg(lean_object*);
lean_object* l_DList_cons(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_DList_empty(lean_object*);
lean_object* l_DList_ofList___elambda__1(lean_object*);
lean_object* l_DList_cons___elambda__1(lean_object*);
lean_object* l_DList_push(lean_object*);
lean_object* l_DList_empty___elambda__1___rarg___boxed(lean_object*);
lean_object* l_DList_empty___elambda__1(lean_object*);
lean_object* l_DList_singleton___elambda__1(lean_object*);
lean_object* l_DList_HasEmptyc(lean_object*);
lean_object* l_DList_cons___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_DList_singleton(lean_object*);
lean_object* l_DList_ofList___rarg(lean_object*);
lean_object* l_DList_singleton___rarg(lean_object*);
lean_object* l_DList_singleton___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_DList_cons___rarg(lean_object*, lean_object*);
lean_object* l_DList_append___rarg(lean_object*, lean_object*);
lean_object* l_DList_empty___closed__1;
lean_object* l_DList_empty___elambda__1___rarg(lean_object*);
lean_object* l_DList_ofList(lean_object*);
lean_object* l_DList_push___rarg(lean_object*, lean_object*);
lean_object* l_DList_HasAppend___closed__1;
lean_object* l_DList_push___elambda__1(lean_object*);
lean_object* l_DList_HasEmptyc___closed__1;
lean_object* l_DList_toList(lean_object*);
lean_object* l_DList_append___elambda__1(lean_object*);
lean_object* l_DList_append(lean_object*);
lean_object* l_DList_ofList___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_DList_ofList___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_DList_ofList___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_ofList___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_DList_ofList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_ofList___elambda__1___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_DList_ofList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_ofList___rarg), 1, 0);
return x_2;
}
}
lean_object* l_DList_empty___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_DList_empty___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_empty___elambda__1___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* _init_l_DList_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_DList_empty___elambda__1___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_DList_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DList_empty___closed__1;
return x_2;
}
}
lean_object* l_DList_empty___elambda__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DList_empty___elambda__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_DList_HasEmptyc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_DList_empty___elambda__1___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_DList_HasEmptyc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DList_HasEmptyc___closed__1;
return x_2;
}
}
lean_object* l_DList_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_DList_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_toList___rarg), 1, 0);
return x_2;
}
}
lean_object* l_DList_singleton___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_DList_singleton___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_singleton___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_DList_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_singleton___elambda__1___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_DList_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_singleton___rarg), 1, 0);
return x_2;
}
}
lean_object* l_DList_cons___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_DList_cons___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_cons___elambda__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_DList_cons___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DList_cons___elambda__1___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_DList_cons(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_cons___rarg), 2, 0);
return x_2;
}
}
lean_object* l_DList_append___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_DList_append___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_append___elambda__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_DList_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DList_append___elambda__1___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_DList_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_append___rarg), 2, 0);
return x_2;
}
}
lean_object* l_DList_push___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_DList_push___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_push___elambda__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_DList_push___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DList_push___elambda__1___rarg), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_DList_push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DList_push___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_DList_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_DList_append___rarg), 2, 0);
return x_1;
}
}
lean_object* l_DList_HasAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DList_HasAppend___closed__1;
return x_2;
}
}
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_DList(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_DList_empty___closed__1 = _init_l_DList_empty___closed__1();
lean_mark_persistent(l_DList_empty___closed__1);
l_DList_HasEmptyc___closed__1 = _init_l_DList_HasEmptyc___closed__1();
lean_mark_persistent(l_DList_HasEmptyc___closed__1);
l_DList_HasAppend___closed__1 = _init_l_DList_HasAppend___closed__1();
lean_mark_persistent(l_DList_HasAppend___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

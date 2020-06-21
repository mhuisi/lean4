// Lean compiler output
// Module: Init.Control.Functor
// Imports: Init.Core
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
lean_object* l_Functor_discard(lean_object*, lean_object*);
lean_object* l_Functor_mapRev(lean_object*);
lean_object* l_Functor_discard___rarg(lean_object*, lean_object*);
lean_object* l_Functor_mapRev___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Functor_mapRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_4);
return x_7;
}
}
lean_object* l_Functor_mapRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Functor_mapRev___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Functor_discard___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
lean_object* l_Functor_discard(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_discard___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Functor(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

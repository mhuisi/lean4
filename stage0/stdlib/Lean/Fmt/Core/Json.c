// Lean compiler output
// Module: Lean.Fmt.Core.Json
// Imports: public import Lean.Fmt.Core.Formatter public import Lean.Data.Json
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Json_isPrimitive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_isPrimitive___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__1;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__3;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__5;
static const lean_string_object l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__6;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__10;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__12;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__7 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__8;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__15;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__16;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__17;
static const lean_string_object l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\": "};
static const lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4;
static const lean_string_object l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\":"};
static const lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg(size_t, size_t, lean_object*);
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__20 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__21;
static const lean_string_object l_Lean_Fmt_Json_format___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Fmt_Json_format___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_Json_format___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__19;
static lean_once_cell_t l_Lean_Fmt_Json_format___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Json_format___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_format___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Json_isPrimitive(lean_object* v_j_1_){
_start:
{
switch(lean_obj_tag(v_j_1_))
{
case 4:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
case 5:
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
default: 
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_isPrimitive___boxed(lean_object* v_j_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_Fmt_Json_isPrimitive(v_j_5_);
lean_dec(v_j_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2(lean_object* v_as_8_, size_t v_i_9_, size_t v_stop_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_usize_dec_eq(v_i_9_, v_stop_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_12_ = 1;
v___x_13_ = lean_array_uget_borrowed(v_as_8_, v_i_9_);
v___x_14_ = l_Lean_Fmt_Json_isPrimitive(v___x_13_);
if (v___x_14_ == 0)
{
return v___x_12_;
}
else
{
if (v___x_11_ == 0)
{
size_t v___x_15_; size_t v___x_16_; 
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_9_, v___x_15_);
v_i_9_ = v___x_16_;
goto _start;
}
else
{
return v___x_12_;
}
}
}
else
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2___boxed(lean_object* v_as_19_, lean_object* v_i_20_, lean_object* v_stop_21_){
_start:
{
size_t v_i_boxed_22_; size_t v_stop_boxed_23_; uint8_t v_res_24_; lean_object* v_r_25_; 
v_i_boxed_22_ = lean_unbox_usize(v_i_20_);
lean_dec(v_i_20_);
v_stop_boxed_23_ = lean_unbox_usize(v_stop_21_);
lean_dec(v_stop_21_);
v_res_24_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2(v_as_19_, v_i_boxed_22_, v_stop_boxed_23_);
lean_dec_ref(v_as_19_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(lean_object* v_init_26_, lean_object* v_x_27_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v_k_28_; lean_object* v_v_29_; lean_object* v_l_30_; lean_object* v_r_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_k_28_ = lean_ctor_get(v_x_27_, 1);
v_v_29_ = lean_ctor_get(v_x_27_, 2);
v_l_30_ = lean_ctor_get(v_x_27_, 3);
v_r_31_ = lean_ctor_get(v_x_27_, 4);
v___x_32_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(v_init_26_, v_l_30_);
lean_inc(v_v_29_);
lean_inc(v_k_28_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v_k_28_);
lean_ctor_set(v___x_33_, 1, v_v_29_);
v___x_34_ = lean_array_push(v___x_32_, v___x_33_);
v_init_26_ = v___x_34_;
v_x_27_ = v_r_31_;
goto _start;
}
else
{
return v_init_26_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3___boxed(lean_object* v_init_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(v_init_36_, v_x_37_);
lean_dec(v_x_37_);
return v_res_38_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__1(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__0));
v___x_41_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__2));
v___x_44_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__5(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__4));
v___x_47_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__0));
v___x_50_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__6(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1);
v___x_52_ = lean_unsigned_to_nat(3u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = lean_array_push(v___x_53_, v___x_51_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__10(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__9));
v___x_57_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__12(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__11));
v___x_60_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__8(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__7));
v___x_63_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__13(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__8, &l_Lean_Fmt_Json_format___redArg___closed__8_once, _init_l_Lean_Fmt_Json_format___redArg___closed__8);
v___x_65_ = lean_unsigned_to_nat(3u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_array_push(v___x_66_, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Fmt_Doc_hardNl(lean_box(0));
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__15(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__14));
v___x_71_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__16(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7);
v___x_73_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__15, &l_Lean_Fmt_Json_format___redArg___closed__15_once, _init_l_Lean_Fmt_Json_format___redArg___closed__15);
v___x_74_ = l_Lean_Fmt_Doc_append___override___redArg(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__17(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__8, &l_Lean_Fmt_Json_format___redArg___closed__8_once, _init_l_Lean_Fmt_Json_format___redArg___closed__8);
v___x_76_ = lean_unsigned_to_nat(4u);
v___x_77_ = lean_mk_empty_array_with_capacity(v___x_76_);
v___x_78_ = lean_array_push(v___x_77_, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__2));
v___x_81_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1);
v___x_83_ = lean_unsigned_to_nat(4u);
v___x_84_ = lean_mk_empty_array_with_capacity(v___x_83_);
v___x_85_ = lean_array_push(v___x_84_, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__5));
v___x_88_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg(lean_object* v_k_89_, lean_object* v_v_90_){
_start:
{
lean_object* v_v_x27_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_f1_98_; uint8_t v___x_99_; 
lean_inc(v_v_90_);
v_v_x27_91_ = l_Lean_Fmt_Json_format___redArg(v_v_90_);
v___x_92_ = l_Lean_Fmt_Doc_text___override___redArg(v_k_89_);
v___x_93_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__3);
v___x_94_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__4);
v___x_95_ = lean_array_push(v___x_94_, v___x_92_);
lean_inc_ref(v___x_95_);
v___x_96_ = lean_array_push(v___x_95_, v___x_93_);
lean_inc(v_v_x27_91_);
v___x_97_ = lean_array_push(v___x_96_, v_v_x27_91_);
v_f1_98_ = l_Lean_Fmt_Doc_join___redArg(v___x_97_);
v___x_99_ = l_Lean_Fmt_Json_isPrimitive(v_v_90_);
lean_dec(v_v_90_);
if (v___x_99_ == 0)
{
lean_dec_ref(v___x_95_);
lean_dec(v_v_x27_91_);
return v_f1_98_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_f2_106_; lean_object* v___x_107_; 
v___x_100_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__6);
v___x_101_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7);
v___x_102_ = l_Lean_Fmt_Doc_append___override___redArg(v___x_101_, v_v_x27_91_);
v___x_103_ = l_Lean_Fmt_Doc_hardNested___redArg(v___x_102_);
v___x_104_ = lean_array_push(v___x_95_, v___x_100_);
v___x_105_ = lean_array_push(v___x_104_, v___x_103_);
v_f2_106_ = l_Lean_Fmt_Doc_join___redArg(v___x_105_);
v___x_107_ = l_Lean_Fmt_Doc_either___override___redArg(v_f1_98_, v_f2_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg(size_t v_sz_108_, size_t v_i_109_, lean_object* v_bs_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_usize_dec_lt(v_i_109_, v_sz_108_);
if (v___x_111_ == 0)
{
return v_bs_110_;
}
else
{
lean_object* v_v_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; lean_object* v_bs_x27_116_; lean_object* v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; 
v_v_112_ = lean_array_uget_borrowed(v_bs_110_, v_i_109_);
v_fst_113_ = lean_ctor_get(v_v_112_, 0);
lean_inc(v_fst_113_);
v_snd_114_ = lean_ctor_get(v_v_112_, 1);
lean_inc(v_snd_114_);
v___x_115_ = lean_unsigned_to_nat(0u);
v_bs_x27_116_ = lean_array_uset(v_bs_110_, v_i_109_, v___x_115_);
v___x_117_ = l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg(v_fst_113_, v_snd_114_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_109_, v___x_118_);
v___x_120_ = lean_array_uset(v_bs_x27_116_, v_i_109_, v___x_117_);
v_i_109_ = v___x_119_;
v_bs_110_ = v___x_120_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__21(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__20));
v___x_124_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__19(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Fmt_Json_format___redArg___closed__18));
v___x_127_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Fmt_Json_format___redArg___closed__22(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__19, &l_Lean_Fmt_Json_format___redArg___closed__19_once, _init_l_Lean_Fmt_Json_format___redArg___closed__19);
v___x_129_ = lean_unsigned_to_nat(4u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_array_push(v___x_130_, v___x_128_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_format___redArg(lean_object* v_j_132_){
_start:
{
switch(lean_obj_tag(v_j_132_))
{
case 0:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__1, &l_Lean_Fmt_Json_format___redArg___closed__1_once, _init_l_Lean_Fmt_Json_format___redArg___closed__1);
return v___x_133_;
}
case 1:
{
uint8_t v_b_134_; 
v_b_134_ = lean_ctor_get_uint8(v_j_132_, 0);
lean_dec_ref_known(v_j_132_, 0);
if (v_b_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__3, &l_Lean_Fmt_Json_format___redArg___closed__3_once, _init_l_Lean_Fmt_Json_format___redArg___closed__3);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__5, &l_Lean_Fmt_Json_format___redArg___closed__5_once, _init_l_Lean_Fmt_Json_format___redArg___closed__5);
return v___x_136_;
}
}
case 2:
{
lean_object* v_n_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_n_137_ = lean_ctor_get(v_j_132_, 0);
lean_inc_ref(v_n_137_);
lean_dec_ref_known(v_j_132_, 1);
v___x_138_ = l_Lean_JsonNumber_toString(v_n_137_);
v___x_139_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_138_);
return v___x_139_;
}
case 3:
{
lean_object* v_s_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_s_140_ = lean_ctor_get(v_j_132_, 0);
lean_inc_ref(v_s_140_);
lean_dec_ref_known(v_j_132_, 1);
v___x_141_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__1);
v___x_142_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_140_);
v___x_143_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__6, &l_Lean_Fmt_Json_format___redArg___closed__6_once, _init_l_Lean_Fmt_Json_format___redArg___closed__6);
v___x_144_ = lean_array_push(v___x_143_, v___x_142_);
v___x_145_ = lean_array_push(v___x_144_, v___x_141_);
v___x_146_ = l_Lean_Fmt_Doc_join___redArg(v___x_145_);
return v___x_146_;
}
case 4:
{
lean_object* v_elems_147_; size_t v_sz_148_; size_t v___x_149_; lean_object* v_elems_150_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_elems_147_ = lean_ctor_get(v_j_132_, 0);
lean_inc_ref_n(v_elems_147_, 2);
lean_dec_ref_known(v_j_132_, 1);
v_sz_148_ = lean_array_size(v_elems_147_);
v___x_149_ = ((size_t)0ULL);
v_elems_150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg(v_sz_148_, v___x_149_, v_elems_147_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_array_get_size(v_elems_147_);
v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_elems_147_);
goto v___jp_151_;
}
else
{
if (v___x_162_ == 0)
{
lean_dec_ref(v_elems_147_);
goto v___jp_151_;
}
else
{
size_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_usize_of_nat(v___x_161_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_Json_format_spec__2(v_elems_147_, v___x_149_, v___x_163_);
lean_dec_ref(v_elems_147_);
if (v___x_164_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_165_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7);
v___x_166_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__16, &l_Lean_Fmt_Json_format___redArg___closed__16_once, _init_l_Lean_Fmt_Json_format___redArg___closed__16);
v___x_167_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_166_, v_elems_150_);
v___x_168_ = l_Lean_Fmt_Doc_append___override___redArg(v___x_165_, v___x_167_);
v___x_169_ = l_Lean_Fmt_Doc_hardNested___redArg(v___x_168_);
v___x_170_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__12, &l_Lean_Fmt_Json_format___redArg___closed__12_once, _init_l_Lean_Fmt_Json_format___redArg___closed__12);
v___x_171_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__17, &l_Lean_Fmt_Json_format___redArg___closed__17_once, _init_l_Lean_Fmt_Json_format___redArg___closed__17);
v___x_172_ = lean_array_push(v___x_171_, v___x_169_);
v___x_173_ = lean_array_push(v___x_172_, v___x_165_);
v___x_174_ = lean_array_push(v___x_173_, v___x_170_);
v___x_175_ = l_Lean_Fmt_Doc_join___redArg(v___x_174_);
return v___x_175_;
}
}
}
v___jp_151_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_152_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__10, &l_Lean_Fmt_Json_format___redArg___closed__10_once, _init_l_Lean_Fmt_Json_format___redArg___closed__10);
v___x_153_ = l_Lean_Fmt_Doc_fillUsing___redArg(v___x_152_, v_elems_150_);
v___x_154_ = l_Lean_Fmt_Doc_aligned___override___redArg(v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__12, &l_Lean_Fmt_Json_format___redArg___closed__12_once, _init_l_Lean_Fmt_Json_format___redArg___closed__12);
v___x_156_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__13, &l_Lean_Fmt_Json_format___redArg___closed__13_once, _init_l_Lean_Fmt_Json_format___redArg___closed__13);
v___x_157_ = lean_array_push(v___x_156_, v___x_154_);
v___x_158_ = lean_array_push(v___x_157_, v___x_155_);
v___x_159_ = l_Lean_Fmt_Doc_join___redArg(v___x_158_);
return v___x_159_;
}
}
default: 
{
lean_object* v_kvPairs_176_; lean_object* v___y_178_; 
v_kvPairs_176_ = lean_ctor_get(v_j_132_, 0);
lean_inc(v_kvPairs_176_);
lean_dec_ref_known(v_j_132_, 1);
if (lean_obj_tag(v_kvPairs_176_) == 0)
{
lean_object* v_size_195_; 
v_size_195_ = lean_ctor_get(v_kvPairs_176_, 0);
lean_inc(v_size_195_);
v___y_178_ = v_size_195_;
goto v___jp_177_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___y_178_ = v___x_196_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; size_t v_sz_181_; size_t v___x_182_; lean_object* v_pairs_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_179_ = lean_mk_empty_array_with_capacity(v___y_178_);
lean_dec(v___y_178_);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(v___x_179_, v_kvPairs_176_);
lean_dec(v_kvPairs_176_);
v_sz_181_ = lean_array_size(v___x_180_);
v___x_182_ = ((size_t)0ULL);
v_pairs_183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg(v_sz_181_, v___x_182_, v___x_180_);
v___x_184_ = lean_obj_once(&l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7, &l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7_once, _init_l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg___closed__7);
v___x_185_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__16, &l_Lean_Fmt_Json_format___redArg___closed__16_once, _init_l_Lean_Fmt_Json_format___redArg___closed__16);
v___x_186_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_185_, v_pairs_183_);
v___x_187_ = l_Lean_Fmt_Doc_append___override___redArg(v___x_184_, v___x_186_);
v___x_188_ = l_Lean_Fmt_Doc_hardNested___redArg(v___x_187_);
v___x_189_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__21, &l_Lean_Fmt_Json_format___redArg___closed__21_once, _init_l_Lean_Fmt_Json_format___redArg___closed__21);
v___x_190_ = lean_obj_once(&l_Lean_Fmt_Json_format___redArg___closed__22, &l_Lean_Fmt_Json_format___redArg___closed__22_once, _init_l_Lean_Fmt_Json_format___redArg___closed__22);
v___x_191_ = lean_array_push(v___x_190_, v___x_188_);
v___x_192_ = lean_array_push(v___x_191_, v___x_184_);
v___x_193_ = lean_array_push(v___x_192_, v___x_189_);
v___x_194_ = l_Lean_Fmt_Doc_join___redArg(v___x_193_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg(size_t v_sz_197_, size_t v_i_198_, lean_object* v_bs_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_usize_dec_lt(v_i_198_, v_sz_197_);
if (v___x_200_ == 0)
{
return v_bs_199_;
}
else
{
lean_object* v_v_201_; lean_object* v___x_202_; lean_object* v_bs_x27_203_; lean_object* v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v_v_201_ = lean_array_uget(v_bs_199_, v_i_198_);
v___x_202_ = lean_unsigned_to_nat(0u);
v_bs_x27_203_ = lean_array_uset(v_bs_199_, v_i_198_, v___x_202_);
v___x_204_ = l_Lean_Fmt_Json_format___redArg(v_v_201_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_add(v_i_198_, v___x_205_);
v___x_207_ = lean_array_uset(v_bs_x27_203_, v_i_198_, v___x_204_);
v_i_198_ = v___x_206_;
v_bs_199_ = v___x_207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg___boxed(lean_object* v_sz_209_, lean_object* v_i_210_, lean_object* v_bs_211_){
_start:
{
size_t v_sz_boxed_212_; size_t v_i_boxed_213_; lean_object* v_res_214_; 
v_sz_boxed_212_ = lean_unbox_usize(v_sz_209_);
lean_dec(v_sz_209_);
v_i_boxed_213_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg(v_sz_boxed_212_, v_i_boxed_213_, v_bs_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg___boxed(lean_object* v_sz_215_, lean_object* v_i_216_, lean_object* v_bs_217_){
_start:
{
size_t v_sz_boxed_218_; size_t v_i_boxed_219_; lean_object* v_res_220_; 
v_sz_boxed_218_ = lean_unbox_usize(v_sz_215_);
lean_dec(v_sz_215_);
v_i_boxed_219_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg(v_sz_boxed_218_, v_i_boxed_219_, v_bs_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair(lean_object* v_00_u03c4_221_, lean_object* v_k_222_, lean_object* v_v_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Lean_Fmt_Core_Json_0__Lean_Fmt_Json_format_formatKvPair___redArg(v_k_222_, v_v_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Json_format(lean_object* v_00_u03c4_225_, lean_object* v_j_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Fmt_Json_format___redArg(v_j_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1(lean_object* v_00_u03c4_228_, size_t v_sz_229_, size_t v_i_230_, lean_object* v_bs_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___redArg(v_sz_229_, v_i_230_, v_bs_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1___boxed(lean_object* v_00_u03c4_233_, lean_object* v_sz_234_, lean_object* v_i_235_, lean_object* v_bs_236_){
_start:
{
size_t v_sz_boxed_237_; size_t v_i_boxed_238_; lean_object* v_res_239_; 
v_sz_boxed_237_ = lean_unbox_usize(v_sz_234_);
lean_dec(v_sz_234_);
v_i_boxed_238_ = lean_unbox_usize(v_i_235_);
lean_dec(v_i_235_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__1(v_00_u03c4_233_, v_sz_boxed_237_, v_i_boxed_238_, v_bs_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3(lean_object* v_init_240_, lean_object* v_t_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3_spec__3(v_init_240_, v_t_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3___boxed(lean_object* v_init_243_, lean_object* v_t_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Fmt_Json_format_spec__3(v_init_243_, v_t_244_);
lean_dec(v_t_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4(lean_object* v_00_u03c4_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_bs_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___redArg(v_sz_247_, v_i_248_, v_bs_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4___boxed(lean_object* v_00_u03c4_251_, lean_object* v_sz_252_, lean_object* v_i_253_, lean_object* v_bs_254_){
_start:
{
size_t v_sz_boxed_255_; size_t v_i_boxed_256_; lean_object* v_res_257_; 
v_sz_boxed_255_ = lean_unbox_usize(v_sz_252_);
lean_dec(v_sz_252_);
v_i_boxed_256_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Json_format_spec__4(v_00_u03c4_251_, v_sz_boxed_255_, v_i_boxed_256_, v_bs_254_);
return v_res_257_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Core_Json(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Core_Json(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Core_Json(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Core_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Core_Json(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Fmt.Util.Module
// Imports: public import Lean.Parser.Module.Syntax import Lean.Parser.Module
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static const lean_string_object l_Lean_Fmt_headerKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_headerKind___closed__0 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__0_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_headerKind___closed__1 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__1_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Fmt_headerKind___closed__2 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__2_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Fmt_headerKind___closed__3 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_headerKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Fmt_headerKind___closed__4 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_headerKind = (const lean_object*)&l_Lean_Fmt_headerKind___closed__4_value;
static const lean_string_object l_Lean_Fmt_moduleKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Fmt_moduleKind___closed__0 = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_moduleKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l_Lean_Fmt_moduleKind___closed__1 = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_moduleKind = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value;
static const lean_string_object l_Lean_Fmt_cmdsKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cmds"};
static const lean_object* l_Lean_Fmt_cmdsKind___closed__0 = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_cmdsKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 195, 254, 203, 161, 113, 38, 248)}};
static const lean_object* l_Lean_Fmt_cmdsKind___closed__1 = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_cmdsKind = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eoi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 206, 8, 118, 9, 188, 233, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_mkModuleSyntax_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0(lean_object* v_as_32_, size_t v_i_33_, size_t v_stop_34_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = lean_usize_dec_eq(v_i_33_, v_stop_34_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; uint8_t v___y_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_40_ = 1;
v___x_43_ = lean_array_uget_borrowed(v_as_32_, v_i_33_);
lean_inc(v___x_43_);
v___x_44_ = l_Lean_Parser_isTerminalCommand(v___x_43_);
if (v___x_44_ == 0)
{
v___y_42_ = v___x_44_;
goto v___jp_41_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___closed__2));
lean_inc(v___x_43_);
v___x_46_ = l_Lean_Syntax_isOfKind(v___x_43_, v___x_45_);
if (v___x_46_ == 0)
{
v___y_42_ = v___x_44_;
goto v___jp_41_;
}
else
{
goto v___jp_35_;
}
}
v___jp_41_:
{
if (v___y_42_ == 0)
{
goto v___jp_35_;
}
else
{
return v___x_40_;
}
}
}
else
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
v___jp_35_:
{
size_t v___x_36_; size_t v___x_37_; 
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_add(v_i_33_, v___x_36_);
v_i_33_ = v___x_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0___boxed(lean_object* v_as_48_, lean_object* v_i_49_, lean_object* v_stop_50_){
_start:
{
size_t v_i_boxed_51_; size_t v_stop_boxed_52_; uint8_t v_res_53_; lean_object* v_r_54_; 
v_i_boxed_51_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_stop_boxed_52_ = lean_unbox_usize(v_stop_50_);
lean_dec(v_stop_50_);
v_res_53_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0(v_as_48_, v_i_boxed_51_, v_stop_boxed_52_);
lean_dec_ref(v_as_48_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_mkModuleSyntax_x3f(lean_object* v_headerStx_55_, lean_object* v_cmdStxs_56_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_array_get_size(v_cmdStxs_56_);
v___x_70_ = lean_nat_dec_lt(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
goto v___jp_57_;
}
else
{
if (v___x_70_ == 0)
{
goto v___jp_57_;
}
else
{
size_t v___x_71_; size_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = ((size_t)0ULL);
v___x_72_ = lean_usize_of_nat(v___x_69_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_mkModuleSyntax_x3f_spec__0(v_cmdStxs_56_, v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
goto v___jp_57_;
}
else
{
lean_object* v___x_74_; 
lean_dec_ref(v_cmdStxs_56_);
lean_dec(v_headerStx_55_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
}
v___jp_57_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_58_ = ((lean_object*)(l_Lean_Fmt_moduleKind));
v___x_59_ = ((lean_object*)(l_Lean_Fmt_cmdsKind));
v___x_60_ = lean_box(2);
v___x_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
lean_ctor_set(v___x_61_, 2, v_cmdStxs_56_);
v___x_62_ = lean_unsigned_to_nat(2u);
v___x_63_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_64_ = lean_array_push(v___x_63_, v_headerStx_55_);
v___x_65_ = lean_array_push(v___x_64_, v___x_61_);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_60_);
lean_ctor_set(v___x_66_, 1, v___x_58_);
lean_ctor_set(v___x_66_, 2, v___x_65_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
}
lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_Module(builtin);
}
#ifdef __cplusplus
}
#endif

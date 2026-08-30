// Lean compiler output
// Module: Lean.Fmt.Util.Basic
// Imports: public import Init.Data.Ord.Basic public import Init.Data.String.Subslice import Init.Data.Hashable import Init.Data.ToString public import Lean.Syntax
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_instHashableRaw__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_instHashableRaw__lean_hash___boxed(lean_object*);
static const lean_closure_object l_instHashableRaw__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableRaw__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableRaw__lean___closed__0 = (const lean_object*)&l_instHashableRaw__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableRaw__lean = (const lean_object*)&l_instHashableRaw__lean___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdRaw__lean_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdRaw__lean_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdRaw__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdRaw__lean_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdRaw__lean___closed__0 = (const lean_object*)&l_instOrdRaw__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdRaw__lean = (const lean_object*)&l_instOrdRaw__lean___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean(lean_object*);
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean(lean_object*);
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean(lean_object*);
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean(lean_object*);
static const lean_string_object l_instToStringSubslice__lean___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " - "};
static const lean_object* l_instToStringSubslice__lean___lam__0___closed__0 = (const lean_object*)&l_instToStringSubslice__lean___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___lam__0(lean_object*);
static const lean_closure_object l_instToStringSubslice__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringSubslice__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringSubslice__lean___closed__0 = (const lean_object*)&l_instToStringSubslice__lean___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringSubslice__lean(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprSubslice__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprSubslice__lean___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprSubslice__lean___closed__0 = (const lean_object*)&l_instReprSubslice__lean___closed__0_value;
LEAN_EXPORT lean_object* l_instReprSubslice__lean(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_split___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_split(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableRaw__lean_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_instHashableRaw__lean_hash___boxed(lean_object* v_x_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_instHashableRaw__lean_hash(v_x_5_);
lean_dec(v_x_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_instOrdRaw__lean_ord(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_lt(v_x_10_, v_x_11_);
if (v___x_12_ == 0)
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_eq(v_x_10_, v_x_11_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = 2;
return v___x_14_;
}
else
{
uint8_t v___x_15_; 
v___x_15_ = 1;
return v___x_15_;
}
}
else
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdRaw__lean_ord___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_instOrdRaw__lean_ord(v_x_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec(v_x_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash___redArg(lean_object* v_x_23_){
_start:
{
uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; 
v___x_24_ = 0ULL;
v___x_25_ = l_instHashableRaw__lean_hash(v_x_23_);
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
v___x_27_ = lean_uint64_mix_hash(v___x_26_, v___x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___redArg___boxed(lean_object* v_x_28_){
_start:
{
uint64_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_instHashablePos__lean_hash___redArg(v_x_28_);
lean_dec(v_x_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash(lean_object* v_s_31_, lean_object* v_x_32_){
_start:
{
uint64_t v___x_33_; 
v___x_33_ = l_instHashablePos__lean_hash___redArg(v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___boxed(lean_object* v_s_34_, lean_object* v_x_35_){
_start:
{
uint64_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_instHashablePos__lean_hash(v_s_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec_ref(v_s_34_);
v_r_37_ = lean_box_uint64(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean(lean_object* v_s_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_closure((void*)(l_instHashablePos__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_39_, 0, v_s_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord___redArg(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_instOrdRaw__lean_ord(v_x_40_, v_x_41_);
if (v___x_42_ == 1)
{
return v___x_42_;
}
else
{
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___redArg___boxed(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_instOrdPos__lean_ord___redArg(v_x_43_, v_x_44_);
lean_dec(v_x_44_);
lean_dec(v_x_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord(lean_object* v_s_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = l_instOrdPos__lean_ord___redArg(v_x_48_, v_x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___boxed(lean_object* v_s_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_instOrdPos__lean_ord(v_s_51_, v_x_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_x_52_);
lean_dec_ref(v_s_51_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean(lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_closure((void*)(l_instOrdPos__lean_ord___boxed), 3, 1);
lean_closure_set(v___x_57_, 0, v_s_56_);
return v___x_57_;
}
}
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq___redArg(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_startInclusive_60_; lean_object* v_endExclusive_61_; lean_object* v_startInclusive_62_; lean_object* v_endExclusive_63_; uint8_t v___x_64_; 
v_startInclusive_60_ = lean_ctor_get(v_x_58_, 0);
v_endExclusive_61_ = lean_ctor_get(v_x_58_, 1);
v_startInclusive_62_ = lean_ctor_get(v_x_59_, 0);
v_endExclusive_63_ = lean_ctor_get(v_x_59_, 1);
v___x_64_ = lean_nat_dec_eq(v_startInclusive_60_, v_startInclusive_62_);
if (v___x_64_ == 0)
{
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_eq(v_endExclusive_61_, v_endExclusive_63_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___redArg___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_instBEqSubslice__lean_beq___redArg(v_x_66_, v_x_67_);
lean_dec_ref(v_x_67_);
lean_dec_ref(v_x_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq(lean_object* v_s_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_instBEqSubslice__lean_beq___redArg(v_x_71_, v_x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___boxed(lean_object* v_s_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_instBEqSubslice__lean_beq(v_s_74_, v_x_75_, v_x_76_);
lean_dec_ref(v_x_76_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_s_74_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean(lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_closure((void*)(l_instBEqSubslice__lean_beq___boxed), 3, 1);
lean_closure_set(v___x_80_, 0, v_s_79_);
return v___x_80_;
}
}
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash___redArg(lean_object* v_x_81_){
_start:
{
lean_object* v_startInclusive_82_; lean_object* v_endExclusive_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; 
v_startInclusive_82_ = lean_ctor_get(v_x_81_, 0);
v_endExclusive_83_ = lean_ctor_get(v_x_81_, 1);
v___x_84_ = 0ULL;
v___x_85_ = l_instHashablePos__lean_hash___redArg(v_startInclusive_82_);
v___x_86_ = lean_uint64_mix_hash(v___x_84_, v___x_85_);
v___x_87_ = l_instHashablePos__lean_hash___redArg(v_endExclusive_83_);
v___x_88_ = lean_uint64_mix_hash(v___x_86_, v___x_87_);
v___x_89_ = lean_uint64_mix_hash(v___x_88_, v___x_84_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___redArg___boxed(lean_object* v_x_90_){
_start:
{
uint64_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_instHashableSubslice__lean_hash___redArg(v_x_90_);
lean_dec_ref(v_x_90_);
v_r_92_ = lean_box_uint64(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash(lean_object* v_s_93_, lean_object* v_x_94_){
_start:
{
uint64_t v___x_95_; 
v___x_95_ = l_instHashableSubslice__lean_hash___redArg(v_x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___boxed(lean_object* v_s_96_, lean_object* v_x_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_instHashableSubslice__lean_hash(v_s_96_, v_x_97_);
lean_dec_ref(v_x_97_);
lean_dec_ref(v_s_96_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean(lean_object* v_s_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_closure((void*)(l_instHashableSubslice__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_101_, 0, v_s_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___lam__0(lean_object* v_s_103_){
_start:
{
lean_object* v_startInclusive_104_; lean_object* v_endExclusive_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_startInclusive_104_ = lean_ctor_get(v_s_103_, 0);
lean_inc(v_startInclusive_104_);
v_endExclusive_105_ = lean_ctor_get(v_s_103_, 1);
lean_inc(v_endExclusive_105_);
lean_dec_ref(v_s_103_);
v___x_106_ = l_Nat_reprFast(v_startInclusive_104_);
v___x_107_ = ((lean_object*)(l_instToStringSubslice__lean___lam__0___closed__0));
v___x_108_ = lean_string_append(v___x_106_, v___x_107_);
v___x_109_ = l_Nat_reprFast(v_endExclusive_105_);
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
lean_dec_ref(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean(lean_object* v_s_112_){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = ((lean_object*)(l_instToStringSubslice__lean___closed__0));
return v___f_113_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___boxed(lean_object* v_s_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_instToStringSubslice__lean(v_s_114_);
lean_dec_ref(v_s_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___lam__0(lean_object* v_s_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_startInclusive_118_; lean_object* v_endExclusive_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_startInclusive_118_ = lean_ctor_get(v_s_116_, 0);
lean_inc(v_startInclusive_118_);
v_endExclusive_119_ = lean_ctor_get(v_s_116_, 1);
lean_inc(v_endExclusive_119_);
lean_dec_ref(v_s_116_);
v___x_120_ = l_Nat_reprFast(v_startInclusive_118_);
v___x_121_ = ((lean_object*)(l_instToStringSubslice__lean___lam__0___closed__0));
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
v___x_123_ = l_Nat_reprFast(v_endExclusive_119_);
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
lean_dec_ref(v___x_123_);
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___lam__0___boxed(lean_object* v_s_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_instReprSubslice__lean___lam__0(v_s_126_, v_x_127_);
lean_dec(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean(lean_object* v_s_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = ((lean_object*)(l_instReprSubslice__lean___closed__0));
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___boxed(lean_object* v_s_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_instReprSubslice__lean(v_s_132_);
lean_dec_ref(v_s_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object* v_info_134_){
_start:
{
if (lean_obj_tag(v_info_134_) == 0)
{
lean_object* v_leading_135_; lean_object* v___x_136_; 
v_leading_135_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_leading_135_);
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_leading_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f___boxed(lean_object* v_info_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_SourceInfo_getLeading_x3f(v_info_138_);
lean_dec(v_info_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object* v_stx_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Lean_Syntax_getHeadInfo(v_stx_140_);
v___x_142_ = l_Lean_SourceInfo_getLeading_x3f(v___x_141_);
lean_dec(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object* v_stx_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Syntax_getLeading_x3f(v_stx_143_);
lean_dec(v_stx_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f(lean_object* v_stx_145_){
_start:
{
lean_object* v_info_146_; lean_object* v___x_147_; 
v_info_146_ = l_Lean_Syntax_getHeadInfo(v_stx_145_);
v___x_147_ = l_Lean_SourceInfo_getLeading_x3f(v_info_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
uint8_t v___x_148_; lean_object* v___x_149_; 
v___x_148_ = 0;
v___x_149_ = l_Lean_SourceInfo_getPos_x3f(v_info_146_, v___x_148_);
lean_dec(v_info_146_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_info_146_);
v_val_150_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v___x_147_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v___x_147_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_startPos_154_; lean_object* v___x_156_; 
v_startPos_154_ = lean_ctor_get(v_val_150_, 1);
lean_inc(v_startPos_154_);
lean_dec(v_val_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v_startPos_154_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_startPos_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f___boxed(lean_object* v_stx_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Syntax_getStartPos_x3f(v_stx_159_);
lean_dec(v_stx_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object* v_s_161_){
_start:
{
lean_object* v_startPos_162_; lean_object* v_stopPos_163_; lean_object* v___x_164_; 
v_startPos_162_ = lean_ctor_get(v_s_161_, 1);
v_stopPos_163_ = lean_ctor_get(v_s_161_, 2);
lean_inc(v_stopPos_163_);
lean_inc(v_startPos_162_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_startPos_162_);
lean_ctor_set(v___x_164_, 1, v_stopPos_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring___boxed(lean_object* v_s_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Syntax_Range_ofSubstring(v_s_165_);
lean_dec_ref(v_s_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0(lean_object* v_toPure_167_, lean_object* v_00_u03b1_168_, lean_object* v_o_x3f_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_2(v_toPure_167_, lean_box(0), v_o_x3f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg(lean_object* v_inst_171_){
_start:
{
lean_object* v_toApplicative_172_; lean_object* v_toPure_173_; lean_object* v___f_174_; 
v_toApplicative_172_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_172_);
lean_dec_ref(v_inst_171_);
v_toPure_173_ = lean_ctor_get(v_toApplicative_172_, 1);
lean_inc(v_toPure_173_);
lean_dec_ref(v_toApplicative_172_);
v___f_174_ = lean_alloc_closure((void*)(l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0), 3, 1);
lean_closure_set(v___f_174_, 0, v_toPure_173_);
return v___f_174_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean(lean_object* v_m_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_instMonadLiftOptionOptionTOfMonad__lean___redArg(v_inst_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Option_split___redArg(lean_object* v_o_178_){
_start:
{
lean_object* v___y_180_; 
if (lean_obj_tag(v_o_178_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
v___y_180_ = v___x_200_;
goto v___jp_179_;
}
else
{
lean_object* v_val_201_; lean_object* v_fst_202_; lean_object* v___x_203_; 
v_val_201_ = lean_ctor_get(v_o_178_, 0);
v_fst_202_ = lean_ctor_get(v_val_201_, 0);
lean_inc(v_fst_202_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_fst_202_);
v___y_180_ = v___x_203_;
goto v___jp_179_;
}
v___jp_179_:
{
if (lean_obj_tag(v_o_178_) == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___y_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_val_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_199_; 
v_val_183_ = lean_ctor_get(v_o_178_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_o_178_);
if (v_isSharedCheck_199_ == 0)
{
v___x_185_ = v_o_178_;
v_isShared_186_ = v_isSharedCheck_199_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_val_183_);
lean_dec(v_o_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_199_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_snd_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_snd_187_ = lean_ctor_get(v_val_183_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_val_183_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_val_183_, 0);
lean_dec(v_unused_198_);
v___x_189_ = v_val_183_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snd_187_);
lean_dec(v_val_183_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v_snd_187_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_snd_187_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_192_);
lean_ctor_set(v___x_189_, 0, v___y_180_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___y_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_split(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_o_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Option_split___redArg(v_o_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object* v_as_217_, size_t v_i_218_, size_t v_stop_219_, lean_object* v_b_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_eq(v_i_218_, v_stop_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___y_226_; 
v___x_222_ = lean_array_uget_borrowed(v_as_217_, v_i_218_);
v_fst_223_ = lean_ctor_get(v___x_222_, 0);
v_snd_224_ = lean_ctor_get(v___x_222_, 1);
if (lean_obj_tag(v_snd_224_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3));
v___y_226_ = v___x_235_;
goto v___jp_225_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v_snd_224_, 0);
lean_inc(v_val_236_);
v___y_226_ = v_val_236_;
goto v___jp_225_;
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; size_t v___x_232_; size_t v___x_233_; 
v___x_227_ = lean_unsigned_to_nat(2u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
lean_inc(v_fst_223_);
v___x_229_ = lean_array_push(v___x_228_, v_fst_223_);
v___x_230_ = lean_array_push(v___x_229_, v___y_226_);
v___x_231_ = l_Array_append___redArg(v_b_220_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_218_, v___x_232_);
v_i_218_ = v___x_233_;
v_b_220_ = v___x_231_;
goto _start;
}
}
else
{
return v_b_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_stop_239_, lean_object* v_b_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; lean_object* v_res_243_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_239_);
lean_dec(v_stop_239_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v_as_237_, v_i_boxed_241_, v_stop_boxed_242_, v_b_240_);
lean_dec_ref(v_as_237_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object* v_elems_244_, lean_object* v_seps_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_246_ = l_Array_zip___redArg(v_elems_244_, v_seps_245_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0));
v___x_249_ = lean_array_get_size(v___x_246_);
v___x_250_ = lean_nat_dec_lt(v___x_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_246_);
return v___x_248_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = lean_nat_dec_le(v___x_249_, v___x_249_);
if (v___x_251_ == 0)
{
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_246_);
return v___x_248_;
}
else
{
size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_252_ = ((size_t)0ULL);
v___x_253_ = lean_usize_of_nat(v___x_249_);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v___x_246_, v___x_252_, v___x_253_, v___x_248_);
lean_dec_ref(v___x_246_);
return v___x_254_;
}
}
else
{
size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_255_ = ((size_t)0ULL);
v___x_256_ = lean_usize_of_nat(v___x_249_);
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v___x_246_, v___x_255_, v___x_256_, v___x_248_);
lean_dec_ref(v___x_246_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object* v_elems_258_, lean_object* v_seps_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_258_, v_seps_259_);
lean_dec_ref(v_seps_259_);
lean_dec_ref(v_elems_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object* v_kinds_261_, lean_object* v_elems_262_, lean_object* v_seps_263_, lean_object* v_sep_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_262_, v_seps_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object* v_kinds_266_, lean_object* v_elems_267_, lean_object* v_seps_268_, lean_object* v_sep_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps(v_kinds_266_, v_elems_267_, v_seps_268_, v_sep_269_);
lean_dec_ref(v_sep_269_);
lean_dec_ref(v_seps_268_);
lean_dec_ref(v_elems_267_);
lean_dec(v_kinds_266_);
return v_res_270_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lean_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

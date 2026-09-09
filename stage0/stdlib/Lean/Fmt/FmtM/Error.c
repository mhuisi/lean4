// Lean compiler output
// Module: Lean.Fmt.FmtM.Error
// Imports: public import Init.Data.ToString public import Lean.Fmt.Core.Basic public import Init.Data.Format.Syntax public import Lean.Fmt.Core.Formatter
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_emptyInputSyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_emptyInputSyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_partialFormatter_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_partialFormatter_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_formattingFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_formattingFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_taintedFormatting_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_taintedFormatting_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_malformedInputSyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_malformedInputSyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ambiguousChoiceNode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ambiguousChoiceNode_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_headerError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_headerError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_parseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_parseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_earlyTerminationCommand_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_earlyTerminationCommand_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_raw_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_raw_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instInhabitedError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_instInhabitedError_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedError_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instInhabitedError_default___closed__1 = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedError_default = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedError = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringError___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringError = (const lean_object*)&l_Lean_Fmt_instToStringError___closed__0_value;
static const lean_string_object l_Lean_Fmt_Error_ofFormattingError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 527, .m_capacity = 527, .m_length = 526, .m_data = "Formatting of the document produced by the current set of `[fmt]` annotations contains a part that always exceeds the maximum column width within which the formatter attempts to find optimal configurations (200). This issue is commonly caused by syntax in the document that is not formatted (e.g. because there is no `[fmt]` attribute for it) and is also very long in the input document. To format the parts of the document that are formatteable, either break up the document that is not formatted or write a formatter for it."};
static const lean_object* l_Lean_Fmt_Error_ofFormattingError___closed__0 = (const lean_object*)&l_Lean_Fmt_Error_ofFormattingError___closed__0_value;
static const lean_string_object l_Lean_Fmt_Error_ofFormattingError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 193, .m_capacity = 193, .m_length = 192, .m_data = "Formatting of the document produced by the current set of `[fmt]` annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to flatten a document with hard newlines."};
static const lean_object* l_Lean_Fmt_Error_ofFormattingError___closed__1 = (const lean_object*)&l_Lean_Fmt_Error_ofFormattingError___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
default: 
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Fmt_Error_ctorIdx(v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
switch(lean_obj_tag(v_t_14_))
{
case 1:
{
lean_object* v_msg_16_; lean_object* v___x_17_; 
v_msg_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc_ref(v_msg_16_);
lean_dec_ref_known(v_t_14_, 1);
v___x_17_ = lean_apply_1(v_k_15_, v_msg_16_);
return v___x_17_;
}
case 4:
{
lean_object* v_stx_18_; lean_object* v_malformedPortion_x3f_19_; lean_object* v_reason_20_; lean_object* v_msg_21_; lean_object* v___x_22_; 
v_stx_18_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_stx_18_);
v_malformedPortion_x3f_19_ = lean_ctor_get(v_t_14_, 1);
lean_inc(v_malformedPortion_x3f_19_);
v_reason_20_ = lean_ctor_get(v_t_14_, 2);
lean_inc_ref(v_reason_20_);
v_msg_21_ = lean_ctor_get(v_t_14_, 3);
lean_inc_ref(v_msg_21_);
lean_dec_ref_known(v_t_14_, 4);
v___x_22_ = lean_apply_4(v_k_15_, v_stx_18_, v_malformedPortion_x3f_19_, v_reason_20_, v_msg_21_);
return v___x_22_;
}
case 7:
{
lean_object* v_msg_23_; lean_object* v___x_24_; 
v_msg_23_ = lean_ctor_get(v_t_14_, 0);
lean_inc_ref(v_msg_23_);
lean_dec_ref_known(v_t_14_, 1);
v___x_24_ = lean_apply_1(v_k_15_, v_msg_23_);
return v___x_24_;
}
case 8:
{
lean_object* v_msg_25_; lean_object* v___x_26_; 
v_msg_25_ = lean_ctor_get(v_t_14_, 0);
lean_inc_ref(v_msg_25_);
lean_dec_ref_known(v_t_14_, 1);
v___x_26_ = lean_apply_1(v_k_15_, v_msg_25_);
return v___x_26_;
}
case 9:
{
lean_object* v_msg_27_; lean_object* v___x_28_; 
v_msg_27_ = lean_ctor_get(v_t_14_, 0);
lean_inc_ref(v_msg_27_);
lean_dec_ref_known(v_t_14_, 1);
v___x_28_ = lean_apply_1(v_k_15_, v_msg_27_);
return v___x_28_;
}
default: 
{
lean_object* v_stx_29_; lean_object* v_msg_30_; lean_object* v___x_31_; 
v_stx_29_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_stx_29_);
v_msg_30_ = lean_ctor_get(v_t_14_, 1);
lean_inc_ref(v_msg_30_);
lean_dec_ref(v_t_14_);
v___x_31_ = lean_apply_2(v_k_15_, v_stx_29_, v_msg_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim(lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_34_, v_k_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___boxed(lean_object* v_motive_38_, lean_object* v_ctorIdx_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Fmt_Error_ctorElim(v_motive_38_, v_ctorIdx_39_, v_t_40_, v_h_41_, v_k_42_);
lean_dec(v_ctorIdx_39_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_emptyInputSyntax_elim___redArg(lean_object* v_t_44_, lean_object* v_emptyInputSyntax_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_44_, v_emptyInputSyntax_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_emptyInputSyntax_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_emptyInputSyntax_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_48_, v_emptyInputSyntax_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_partialFormatter_elim___redArg(lean_object* v_t_52_, lean_object* v_partialFormatter_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_52_, v_partialFormatter_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_partialFormatter_elim(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_partialFormatter_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_56_, v_partialFormatter_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_formattingFailure_elim___redArg(lean_object* v_t_60_, lean_object* v_formattingFailure_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_60_, v_formattingFailure_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_formattingFailure_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_formattingFailure_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_64_, v_formattingFailure_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_taintedFormatting_elim___redArg(lean_object* v_t_68_, lean_object* v_taintedFormatting_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_68_, v_taintedFormatting_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_taintedFormatting_elim(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_taintedFormatting_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_72_, v_taintedFormatting_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_malformedInputSyntax_elim___redArg(lean_object* v_t_76_, lean_object* v_malformedInputSyntax_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_76_, v_malformedInputSyntax_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_malformedInputSyntax_elim(lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_malformedInputSyntax_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_80_, v_malformedInputSyntax_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ambiguousChoiceNode_elim___redArg(lean_object* v_t_84_, lean_object* v_ambiguousChoiceNode_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_84_, v_ambiguousChoiceNode_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ambiguousChoiceNode_elim(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_ambiguousChoiceNode_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_88_, v_ambiguousChoiceNode_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_headerError_elim___redArg(lean_object* v_t_92_, lean_object* v_headerError_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_92_, v_headerError_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_headerError_elim(lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_headerError_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_96_, v_headerError_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_parseError_elim___redArg(lean_object* v_t_100_, lean_object* v_parseError_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_100_, v_parseError_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_parseError_elim(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_parseError_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_104_, v_parseError_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_earlyTerminationCommand_elim___redArg(lean_object* v_t_108_, lean_object* v_earlyTerminationCommand_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_108_, v_earlyTerminationCommand_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_earlyTerminationCommand_elim(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_earlyTerminationCommand_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_112_, v_earlyTerminationCommand_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_raw_elim___redArg(lean_object* v_t_116_, lean_object* v_raw_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_116_, v_raw_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_raw_elim(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_raw_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_120_, v_raw_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0(lean_object* v_x_130_){
_start:
{
switch(lean_obj_tag(v_x_130_))
{
case 1:
{
lean_object* v_msg_131_; 
v_msg_131_ = lean_ctor_get(v_x_130_, 0);
lean_inc_ref(v_msg_131_);
return v_msg_131_;
}
case 4:
{
lean_object* v_msg_132_; 
v_msg_132_ = lean_ctor_get(v_x_130_, 3);
lean_inc_ref(v_msg_132_);
return v_msg_132_;
}
case 7:
{
lean_object* v_msg_133_; 
v_msg_133_ = lean_ctor_get(v_x_130_, 0);
lean_inc_ref(v_msg_133_);
return v_msg_133_;
}
case 8:
{
lean_object* v_msg_134_; 
v_msg_134_ = lean_ctor_get(v_x_130_, 0);
lean_inc_ref(v_msg_134_);
return v_msg_134_;
}
case 9:
{
lean_object* v_msg_135_; 
v_msg_135_ = lean_ctor_get(v_x_130_, 0);
lean_inc_ref(v_msg_135_);
return v_msg_135_;
}
default: 
{
lean_object* v_msg_136_; 
v_msg_136_ = lean_ctor_get(v_x_130_, 1);
lean_inc_ref(v_msg_136_);
return v_msg_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Fmt_instToStringError___lam__0(v_x_137_);
lean_dec_ref(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError(lean_object* v_stx_143_, uint8_t v_x_144_){
_start:
{
if (v_x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__0));
v___x_146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_146_, 0, v_stx_143_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__1));
v___x_148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_148_, 0, v_stx_143_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError___boxed(lean_object* v_stx_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_x_26__boxed_151_; lean_object* v_res_152_; 
v_x_26__boxed_151_ = lean_unbox(v_x_150_);
v_res_152_ = l_Lean_Fmt_Error_ofFormattingError(v_stx_149_, v_x_26__boxed_151_);
return v_res_152_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Error(builtin);
}
#ifdef __cplusplus
}
#endif

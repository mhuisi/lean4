// Lean compiler output
// Module: Lake.CLI.Fmt
// Imports: import Lean.Fmt import Lean.Language.Lean import Lean.Elab.Import public import Init.System.IO public import Init.System.FilePath
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
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_inServer;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fileMain(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_collectParsedCmds_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_fmtFile_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_fmtFile_unsafe__1___boxed(lean_object*);
static const lean_array_object l_Lake_Fmt_fmtFile___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Fmt_fmtFile___lam__0___closed__0 = (const lean_object*)&l_Lake_Fmt_fmtFile___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Fmt_fmtFile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Fmt_fmtFile___closed__0;
static lean_once_cell_t l_Lake_Fmt_fmtFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Fmt_fmtFile___closed__1;
static const lean_string_object l_Lake_Fmt_fmtFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_Fmt_fmtFile___closed__2 = (const lean_object*)&l_Lake_Fmt_fmtFile___closed__2_value;
static const lean_string_object l_Lake_Fmt_fmtFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_Fmt_fmtFile___closed__3 = (const lean_object*)&l_Lake_Fmt_fmtFile___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_collectParsedCmds_x3f(lean_object* v_snap_1_, lean_object* v_cmds_2_){
_start:
{
lean_object* v_toSnapshot_3_; lean_object* v_diagnostics_4_; lean_object* v_stx_5_; lean_object* v_nextCmdSnap_x3f_6_; lean_object* v_msgLog_7_; uint8_t v___x_8_; 
v_toSnapshot_3_ = lean_ctor_get(v_snap_1_, 0);
v_diagnostics_4_ = lean_ctor_get(v_toSnapshot_3_, 1);
lean_inc_ref(v_diagnostics_4_);
v_stx_5_ = lean_ctor_get(v_snap_1_, 1);
lean_inc(v_stx_5_);
v_nextCmdSnap_x3f_6_ = lean_ctor_get(v_snap_1_, 4);
lean_inc(v_nextCmdSnap_x3f_6_);
lean_dec_ref(v_snap_1_);
v_msgLog_7_ = lean_ctor_get(v_diagnostics_4_, 0);
lean_inc_ref(v_msgLog_7_);
lean_dec_ref(v_diagnostics_4_);
v___x_8_ = l_Lean_MessageLog_hasErrors(v_msgLog_7_);
lean_dec_ref(v_msgLog_7_);
if (v___x_8_ == 0)
{
lean_object* v_cmds_9_; 
v_cmds_9_ = lean_array_push(v_cmds_2_, v_stx_5_);
if (lean_obj_tag(v_nextCmdSnap_x3f_6_) == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_10_, 0, v_cmds_9_);
return v___x_10_;
}
else
{
lean_object* v_val_11_; lean_object* v___x_12_; 
v_val_11_ = lean_ctor_get(v_nextCmdSnap_x3f_6_, 0);
lean_inc(v_val_11_);
lean_dec_ref_known(v_nextCmdSnap_x3f_6_, 1);
v___x_12_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_11_);
v_snap_1_ = v___x_12_;
v_cmds_2_ = v_cmds_9_;
goto _start;
}
}
else
{
lean_object* v___x_14_; 
lean_dec(v_nextCmdSnap_x3f_6_);
lean_dec(v_stx_5_);
lean_dec_ref(v_cmds_2_);
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_fmtFile_unsafe__1(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_enable_initializer_execution();
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Fmt_0__Lake_Fmt_fmtFile_unsafe__1___boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lake_CLI_Fmt_0__Lake_Fmt_fmtFile_unsafe__1();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___lam__0(uint8_t v___x_21_, lean_object* v___x_22_, lean_object* v_headerStx_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; uint32_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_Elab_HeaderSyntax_isModule(v_headerStx_23_);
v___x_29_ = l_Lean_Elab_HeaderSyntax_imports(v_headerStx_23_, v___x_21_);
v___x_30_ = 0;
v___x_31_ = lean_box(1);
v___x_32_ = ((lean_object*)(l_Lake_Fmt_fmtFile___lam__0___closed__0));
v___x_33_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_33_, 0, v___x_26_);
lean_ctor_set(v___x_33_, 1, v___x_27_);
lean_ctor_set(v___x_33_, 2, v___x_29_);
lean_ctor_set(v___x_33_, 3, v___x_22_);
lean_ctor_set(v___x_33_, 4, v___x_31_);
lean_ctor_set(v___x_33_, 5, v___x_32_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*6 + 4, v___x_28_);
lean_ctor_set_uint32(v___x_33_, sizeof(void*)*6, v___x_30_);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___lam__0___boxed(lean_object* v___x_36_, lean_object* v___x_37_, lean_object* v_headerStx_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
uint8_t v___x_887__boxed_41_; lean_object* v_res_42_; 
v___x_887__boxed_41_ = lean_unbox(v___x_36_);
v_res_42_ = l_Lake_Fmt_fmtFile___lam__0(v___x_887__boxed_41_, v___x_37_, v_headerStx_38_, v___y_39_);
lean_dec_ref(v___y_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2(lean_object* v_s_43_){
_start:
{
lean_object* v___x_45_; lean_object* v_putStr_46_; lean_object* v___x_47_; 
v___x_45_ = lean_get_stderr();
v_putStr_46_ = lean_ctor_get(v___x_45_, 4);
lean_inc_ref(v_putStr_46_);
lean_dec_ref(v___x_45_);
v___x_47_ = lean_apply_2(v_putStr_46_, v_s_43_, lean_box(0));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2___boxed(lean_object* v_s_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2(v_s_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1(lean_object* v_s_51_){
_start:
{
uint32_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = 10;
v___x_54_ = lean_string_push(v_s_51_, v___x_53_);
v___x_55_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1_spec__2(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1___boxed(lean_object* v_s_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1(v_s_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0(lean_object* v_o_62_, lean_object* v_k_63_, uint8_t v_v_64_){
_start:
{
lean_object* v_map_65_; uint8_t v_hasTrace_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_80_; 
v_map_65_ = lean_ctor_get(v_o_62_, 0);
v_hasTrace_66_ = lean_ctor_get_uint8(v_o_62_, sizeof(void*)*1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_o_62_);
if (v_isSharedCheck_80_ == 0)
{
v___x_68_ = v_o_62_;
v_isShared_69_ = v_isSharedCheck_80_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_map_65_);
lean_dec(v_o_62_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_80_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_70_, 0, v_v_64_);
lean_inc(v_k_63_);
v___x_71_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_63_, v___x_70_, v_map_65_);
if (v_hasTrace_66_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___closed__1));
v___x_73_ = l_Lean_Name_isPrefixOf(v___x_72_, v_k_63_);
lean_dec(v_k_63_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_71_);
v___x_75_ = v___x_68_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_71_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_73_);
return v___x_75_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v_k_63_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_71_);
v___x_78_ = v___x_68_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*1, v_hasTrace_66_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0___boxed(lean_object* v_o_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
uint8_t v_v_boxed_84_; lean_object* v_res_85_; 
v_v_boxed_84_ = lean_unbox(v_v_83_);
v_res_85_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0(v_o_81_, v_k_82_, v_v_boxed_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0(lean_object* v_opts_86_, lean_object* v_opt_87_, uint8_t v_val_88_){
_start:
{
lean_object* v_name_89_; lean_object* v___x_90_; 
v_name_89_ = lean_ctor_get(v_opt_87_, 0);
lean_inc(v_name_89_);
lean_dec_ref(v_opt_87_);
v___x_90_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0_spec__0(v_opts_86_, v_name_89_, v_val_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0___boxed(lean_object* v_opts_91_, lean_object* v_opt_92_, lean_object* v_val_93_){
_start:
{
uint8_t v_val_boxed_94_; lean_object* v_res_95_; 
v_val_boxed_94_ = lean_unbox(v_val_93_);
v_res_95_ = l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0(v_opts_91_, v_opt_92_, v_val_boxed_94_);
return v_res_95_;
}
}
static lean_object* _init_l_Lake_Fmt_fmtFile___closed__0(void){
_start:
{
uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = 1;
v___x_97_ = l_Lean_Elab_inServer;
v___x_98_ = l_Lean_Options_empty;
v___x_99_ = l_Lean_Option_set___at___00Lake_Fmt_fmtFile_spec__0(v___x_98_, v___x_97_, v___x_96_);
return v___x_99_;
}
}
static lean_object* _init_l_Lake_Fmt_fmtFile___closed__1(void){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___f_103_; 
v___x_100_ = lean_obj_once(&l_Lake_Fmt_fmtFile___closed__0, &l_Lake_Fmt_fmtFile___closed__0_once, _init_l_Lake_Fmt_fmtFile___closed__0);
v___x_101_ = 1;
v___x_102_ = lean_box(v___x_101_);
v___f_103_ = lean_alloc_closure((void*)(l_Lake_Fmt_fmtFile___lam__0___boxed), 5, 2);
lean_closure_set(v___f_103_, 0, v___x_102_);
lean_closure_set(v___f_103_, 1, v___x_100_);
return v___f_103_;
}
}
static lean_object* _init_l_Lake_Fmt_fmtFile___boxed__const__1(void){
_start:
{
uint32_t v___x_106_; lean_object* v___x_107_; 
v___x_106_ = 1;
v___x_107_ = lean_box_uint32(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lake_Fmt_fmtFile___boxed__const__2(void){
_start:
{
uint32_t v___x_108_; lean_object* v___x_109_; 
v___x_108_ = 0;
v___x_109_ = lean_box_uint32(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile(lean_object* v_file_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_IO_FS_readFile(v_file_110_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v___x_114_ = lean_enable_initializer_execution();
v___x_115_ = lean_string_utf8_byte_size(v_a_113_);
v___x_116_ = 1;
lean_inc_ref(v_file_110_);
v___x_117_ = l_Lean_Parser_mkInputContext___redArg(v_a_113_, v_file_110_, v___x_116_, v___x_115_);
v___f_118_ = lean_obj_once(&l_Lake_Fmt_fmtFile___closed__1, &l_Lake_Fmt_fmtFile___closed__1_once, _init_l_Lake_Fmt_fmtFile___closed__1);
v___x_119_ = lean_box(0);
v___x_120_ = l_Lean_Language_Lean_process(v___f_118_, v___x_119_, v___x_117_);
lean_dec_ref(v___x_117_);
v___x_121_ = l_Lean_Fmt_fileMain(v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___y_128_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_121_, 1);
v___x_123_ = ((lean_object*)(l_Lake_Fmt_fmtFile___closed__2));
v___x_124_ = lean_string_append(v___x_123_, v_file_110_);
lean_dec_ref(v_file_110_);
v___x_125_ = ((lean_object*)(l_Lake_Fmt_fmtFile___closed__3));
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
switch(lean_obj_tag(v_a_122_))
{
case 1:
{
lean_object* v_msg_148_; 
v_msg_148_ = lean_ctor_get(v_a_122_, 0);
lean_inc_ref(v_msg_148_);
lean_dec_ref_known(v_a_122_, 1);
v___y_128_ = v_msg_148_;
goto v___jp_127_;
}
case 4:
{
lean_object* v_msg_149_; 
v_msg_149_ = lean_ctor_get(v_a_122_, 3);
lean_inc_ref(v_msg_149_);
lean_dec_ref_known(v_a_122_, 4);
v___y_128_ = v_msg_149_;
goto v___jp_127_;
}
case 7:
{
lean_object* v_msg_150_; 
v_msg_150_ = lean_ctor_get(v_a_122_, 0);
lean_inc_ref(v_msg_150_);
lean_dec_ref_known(v_a_122_, 1);
v___y_128_ = v_msg_150_;
goto v___jp_127_;
}
case 8:
{
lean_object* v_msg_151_; 
v_msg_151_ = lean_ctor_get(v_a_122_, 0);
lean_inc_ref(v_msg_151_);
lean_dec_ref_known(v_a_122_, 1);
v___y_128_ = v_msg_151_;
goto v___jp_127_;
}
case 9:
{
lean_object* v_msg_152_; 
v_msg_152_ = lean_ctor_get(v_a_122_, 0);
lean_inc_ref(v_msg_152_);
lean_dec_ref_known(v_a_122_, 1);
v___y_128_ = v_msg_152_;
goto v___jp_127_;
}
default: 
{
lean_object* v_msg_153_; 
v_msg_153_ = lean_ctor_get(v_a_122_, 1);
lean_inc_ref(v_msg_153_);
lean_dec(v_a_122_);
v___y_128_ = v_msg_153_;
goto v___jp_127_;
}
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_string_append(v___x_126_, v___y_128_);
lean_dec_ref(v___y_128_);
v___x_130_ = l_IO_eprintln___at___00Lake_Fmt_fmtFile_spec__1(v___x_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_139_);
v___x_132_ = v___x_130_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_dec(v___x_130_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = l_Lake_Fmt_fmtFile___boxed__const__1;
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_130_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_130_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_121_, 1);
v___x_155_ = l_IO_FS_writeFile(v_file_110_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_file_110_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_163_; 
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v___x_155_, 0);
lean_dec(v_unused_164_);
v___x_157_ = v___x_155_;
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
else
{
lean_dec(v___x_155_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = l_Lake_Fmt_fmtFile___boxed__const__2;
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_159_);
v___x_161_ = v___x_157_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_155_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_155_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v_file_110_);
v_a_173_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_112_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_112_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Fmt_fmtFile___boxed(lean_object* v_file_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_Fmt_fmtFile(v_file_181_);
return v_res_183_;
}
}
lean_object* runtime_initialize_Lean_Fmt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Fmt_fmtFile___boxed__const__1 = _init_l_Lake_Fmt_fmtFile___boxed__const__1();
lean_mark_persistent(l_Lake_Fmt_fmtFile___boxed__const__1);
l_Lake_Fmt_fmtFile___boxed__const__2 = _init_l_Lake_Fmt_fmtFile___boxed__const__2();
lean_mark_persistent(l_Lake_Fmt_fmtFile___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Fmt(builtin);
}
#ifdef __cplusplus
}
#endif

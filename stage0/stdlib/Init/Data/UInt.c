// Lean compiler output
// Module: Init.Data.UInt
// Imports: Init.Data.Fin.Basic Init.System.Platform
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
lean_object* l_USize_HasSub;
lean_object* l_UInt64_HasSub;
size_t l_USize_add(size_t, size_t);
lean_object* l_UInt8_HasMod___closed__1;
uint8_t l_USize_hasDecidableLt(size_t, size_t);
lean_object* l_UInt16_modn___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_decLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_hasDecidableLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_modn___boxed(lean_object*, lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
size_t l_USize_div(size_t, size_t);
size_t l_UInt32_toUSize(uint32_t);
uint32_t l_UInt32_HasOne;
uint8_t l_UInt8_decEq(uint8_t, uint8_t);
uint32_t lean_uint32_modn(uint32_t, lean_object*);
lean_object* l_UInt64_decEq___boxed(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_UInt8_HasLessEq;
lean_object* l_UInt64_shiftRight___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_hasDecidableLe___boxed(lean_object*, lean_object*);
uint16_t l_UInt16_HasZero;
uint8_t l_UInt8_decLe(uint8_t, uint8_t);
lean_object* l_USize_toNat___boxed(lean_object*);
lean_object* l_UInt64_toUInt32___boxed(lean_object*);
uint64_t l_UInt64_add(uint64_t, uint64_t);
lean_object* l_USize_HasDiv___closed__1;
uint64_t l_Bool_toUInt64(uint8_t);
lean_object* l_USize_add___boxed(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
uint16_t l_UInt16_HasOne;
lean_object* l_UInt8_toNat___boxed(lean_object*);
uint8_t l_UInt8_lor(uint8_t, uint8_t);
lean_object* l_UInt16_ofNat___boxed(lean_object*);
lean_object* l_USize_hasDecidableLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_HasOfNat;
size_t l_USize_sub(size_t, size_t);
lean_object* l_UInt8_lor___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_decLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_DecidableEq___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_land(uint32_t, uint32_t);
lean_object* l_UInt16_HasSub___closed__1;
lean_object* l_UInt32_land___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toUSize___boxed(lean_object*);
uint32_t l_UInt32_shiftLeft(uint32_t, uint32_t);
size_t l_USize_Inhabited;
lean_object* l_UInt16_hasDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_land___boxed(lean_object*, lean_object*);
lean_object* l_USize_HasOfNat;
lean_object* l_UInt16_div___boxed(lean_object*, lean_object*);
lean_object* l_USize_decLt___boxed(lean_object*, lean_object*);
uint8_t l_UInt64_hasDecidableLt(uint64_t, uint64_t);
lean_object* l_UInt64_HasSub___closed__1;
uint16_t l_UInt16_land(uint16_t, uint16_t);
lean_object* l_UInt32_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_HasLess;
lean_object* l_USize_land___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_land___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_UInt8_HasDiv___closed__1;
lean_object* l_UInt64_HasOfNat___closed__1;
lean_object* l_UInt16_decLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_HasLessEq;
lean_object* l_USize_HasMod;
lean_object* l_UInt16_sub___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_uint64Sz___closed__1;
uint8_t l_UInt8_div(uint8_t, uint8_t);
uint64_t l_UInt64_HasOne;
lean_object* l_USize_HasAdd;
lean_object* l_USize_HasModN;
uint8_t l_UInt8_Inhabited;
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_UInt8_HasSub;
lean_object* l_UInt8_HasAdd;
lean_object* l_uint64Sz;
lean_object* l_UInt16_HasMod___closed__1;
lean_object* l_UInt32_HasMod;
uint32_t l_UInt32_shiftRight(uint32_t, uint32_t);
lean_object* l_UInt32_shiftRight___boxed(lean_object*, lean_object*);
uint8_t l_UInt8_decLt(uint8_t, uint8_t);
uint8_t l_UInt8_add(uint8_t, uint8_t);
uint16_t l_UInt16_add(uint16_t, uint16_t);
uint8_t l_UInt16_hasDecidableLt(uint16_t, uint16_t);
lean_object* l_USize_div___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasModN;
lean_object* l_USize_decEq___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_ofNat___boxed(lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
size_t l_UInt64_toUSize(uint64_t);
uint32_t l_UInt32_div(uint32_t, uint32_t);
lean_object* l_UInt32_ofNat_x27___boxed(lean_object*, lean_object*);
lean_object* l_USize_ofNat___boxed(lean_object*);
lean_object* l_UInt32_HasDiv___closed__1;
lean_object* l_USize_shiftRight___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_UInt64_modn___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_HasAdd;
uint16_t l_Nat_toUInt16(lean_object*);
lean_object* l_UInt64_sub___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_sub(uint32_t, uint32_t);
lean_object* l_UInt8_sub___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasAdd___closed__1;
uint8_t l_UInt8_hasDecidableLt(uint8_t, uint8_t);
uint8_t l_UInt8_DecidableEq(uint8_t, uint8_t);
lean_object* l_uint16Sz;
uint8_t l_UInt16_DecidableEq(uint16_t, uint16_t);
size_t l_USize_HasOne;
lean_object* l_UInt32_add___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_mod___boxed(lean_object*, lean_object*);
lean_object* l_USize_HasMod___closed__1;
lean_object* l_UInt64_HasLessEq;
uint32_t l_UInt64_toUInt32(uint64_t);
lean_object* l_UInt64_toUInt16___boxed(lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_UInt8_HasMod;
lean_object* l_USize_HasAdd___closed__1;
lean_object* l_UInt32_decLt___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_toNat___boxed(lean_object*);
uint8_t l_USize_DecidableEq(size_t, size_t);
lean_object* l_UInt8_add___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_HasOfNat___closed__1;
lean_object* l_UInt64_hasDecidableLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_HasMul___closed__1;
uint32_t l_Nat_toUInt32(lean_object*);
lean_object* l_UInt32_hasDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toUInt16___boxed(lean_object*);
uint64_t l_UInt64_Inhabited;
uint8_t l_UInt64_decLt(uint64_t, uint64_t);
uint8_t l_UInt32_DecidableEq(uint32_t, uint32_t);
lean_object* l_UInt64_HasOfNat;
uint64_t l_Nat_toUInt64(lean_object*);
lean_object* l_UInt64_mul___boxed(lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_UInt16_decLt___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_UInt32_HasLess;
size_t lean_usize_modn(size_t, lean_object*);
uint16_t l_UInt16_lor(uint16_t, uint16_t);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* l_UInt16_HasAdd___closed__1;
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_USize_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasDiv;
lean_object* l_USize_HasOfNat___closed__1;
lean_object* l_UInt64_HasDiv___closed__1;
size_t l_USize_mul(size_t, size_t);
uint64_t l_UInt64_land(uint64_t, uint64_t);
uint8_t l_UInt32_hasDecidableLe(uint32_t, uint32_t);
uint16_t l_UInt16_div(uint16_t, uint16_t);
uint8_t l_UInt8_land(uint8_t, uint8_t);
uint8_t l_UInt32_hasDecidableLt(uint32_t, uint32_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_UInt64_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_HasModN;
lean_object* l_UInt16_HasMul;
lean_object* l_UInt32_div___boxed(lean_object*, lean_object*);
lean_object* l_USize_hasDecidableLt___boxed(lean_object*, lean_object*);
uint64_t l_UInt64_mod(uint64_t, uint64_t);
lean_object* l_UInt16_add___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint64_t l_UInt64_mul(uint64_t, uint64_t);
lean_object* l_UInt32_HasMod___closed__1;
size_t l_USize_land(size_t, size_t);
lean_object* l_uint8Sz;
lean_object* l_UInt16_decEq___boxed(lean_object*, lean_object*);
lean_object* l_USize_mod___boxed(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
uint8_t l_UInt8_sub(uint8_t, uint8_t);
lean_object* l_UInt64_HasAdd___closed__1;
lean_object* l_Nat_toUInt64___boxed(lean_object*);
lean_object* l_UInt16_HasOfNat___closed__1;
lean_object* l_UInt32_DecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_USize_HasModN___closed__1;
lean_object* l_UInt32_HasSub___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_UInt16_HasOfNat;
lean_object* l_UInt16_HasAdd;
lean_object* l_USize_HasMul___closed__1;
uint16_t l_UInt16_Inhabited;
lean_object* l_USize_modn___boxed(lean_object*, lean_object*);
uint8_t l_UInt8_HasOne;
lean_object* l_USize_DecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_UInt64_toUInt8(uint64_t);
lean_object* l_UInt8_HasSub___closed__1;
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_UInt64_decLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_mod___boxed(lean_object*, lean_object*);
lean_object* l_usizeSz___closed__1;
uint64_t lean_uint64_modn(uint64_t, lean_object*);
uint8_t l_UInt64_DecidableEq(uint64_t, uint64_t);
lean_object* l_UInt16_HasModN;
uint32_t l_UInt32_Inhabited;
lean_object* l_UInt32_HasAdd;
lean_object* l_Bool_toUInt64___boxed(lean_object*);
uint32_t l_USize_toUInt32(size_t);
uint16_t l_UInt16_sub(uint16_t, uint16_t);
lean_object* l_UInt16_HasMod;
lean_object* l_UInt32_HasOfNat;
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
lean_object* l_UInt64_toNat___boxed(lean_object*);
lean_object* l_UInt16_toNat___boxed(lean_object*);
lean_object* l_USize_HasLessEq;
uint64_t l_UInt64_lor(uint64_t, uint64_t);
lean_object* l_UInt8_HasModN___closed__1;
lean_object* l_UInt16_hasDecidableLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasSub;
uint8_t l_UInt16_decLt(uint16_t, uint16_t);
lean_object* l_UInt32_ofNat___boxed(lean_object*);
lean_object* l_UInt64_HasLess;
lean_object* l_UInt64_HasMod___closed__1;
uint64_t l_UInt64_HasZero;
uint64_t l_UInt32_toUInt64(uint32_t);
lean_object* l_uint32Sz;
uint8_t lean_uint8_modn(uint8_t, lean_object*);
lean_object* l_UInt32_decEq___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_modn(uint16_t, lean_object*);
lean_object* l_UInt8_HasMul___closed__1;
lean_object* l_USize_decLe___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_sub___boxed(lean_object*, lean_object*);
uint8_t l_UInt8_mul(uint8_t, uint8_t);
lean_object* l_USize_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_decLt___boxed(lean_object*, lean_object*);
uint8_t l_UInt8_HasZero;
uint8_t l_Nat_toUInt8(lean_object*);
uint8_t l_UInt64_decLe(uint64_t, uint64_t);
lean_object* l_UInt32_HasLessEq;
uint32_t l_UInt32_mul(uint32_t, uint32_t);
size_t l_Nat_toUSize(lean_object*);
lean_object* l_UInt64_HasMul;
uint32_t l_UInt32_mod(uint32_t, uint32_t);
lean_object* l_UInt32_HasOfNat___closed__1;
lean_object* l_UInt64_toUSize___boxed(lean_object*);
lean_object* l_USize_HasSub___closed__1;
size_t l_USize_lor(size_t, size_t);
uint8_t l_USize_hasDecidableLe(size_t, size_t);
lean_object* l_UInt32_lor___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_div___boxed(lean_object*, lean_object*);
uint8_t l_UInt16_hasDecidableLe(uint16_t, uint16_t);
lean_object* l_UInt16_HasMul___closed__1;
lean_object* l_UInt16_HasDiv;
lean_object* l_Nat_toUInt32___boxed(lean_object*);
lean_object* l_UInt8_DecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_USize_HasDiv;
lean_object* l_UInt32_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_UInt16_mod___boxed(lean_object*, lean_object*);
size_t l_USize_HasZero;
lean_object* l_USize_toUInt32___boxed(lean_object*);
uint32_t l_UInt32_lor(uint32_t, uint32_t);
lean_object* l_UInt16_lor___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_modn___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_HasSub;
lean_object* l_USize_HasMul;
lean_object* l_UInt32_HasMul;
uint8_t l_UInt16_decEq(uint16_t, uint16_t);
lean_object* l_UInt8_decLt___boxed(lean_object*, lean_object*);
lean_object* l_USize_lor___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_HasMul___closed__1;
lean_object* l_UInt64_add___boxed(lean_object*, lean_object*);
lean_object* l_usizeSz;
lean_object* l_UInt64_lor___boxed(lean_object*, lean_object*);
uint16_t l_UInt16_mod(uint16_t, uint16_t);
uint16_t l_UInt16_mul(uint16_t, uint16_t);
lean_object* l_Nat_toUInt8___boxed(lean_object*);
uint16_t l_UInt64_toUInt16(uint64_t);
lean_object* l_UInt64_mod___boxed(lean_object*, lean_object*);
uint64_t l_UInt64_sub(uint64_t, uint64_t);
lean_object* l_UInt32_HasModN___closed__1;
lean_object* l_UInt32_toUSize___boxed(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint64_t l_UInt64_div(uint64_t, uint64_t);
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
lean_object* l_UInt64_HasModN;
uint8_t l_UInt8_mod(uint8_t, uint8_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_UInt64_HasModN___closed__1;
uint8_t l_UInt16_decLe(uint16_t, uint16_t);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_UInt16_HasModN___closed__1;
lean_object* l_UInt16_HasLess;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_UInt64_HasDiv;
uint8_t l_UInt64_hasDecidableLe(uint64_t, uint64_t);
lean_object* l_UInt8_HasMul;
lean_object* l_UInt64_hasDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_decEq___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_toUInt8___boxed(lean_object*);
lean_object* l_USize_HasLess;
lean_object* l_UInt8_HasDiv;
lean_object* l_USize_sub___boxed(lean_object*, lean_object*);
uint8_t l_UInt8_hasDecidableLe(uint8_t, uint8_t);
lean_object* l_UInt16_HasDiv___closed__1;
lean_object* l_UInt8_hasDecidableLt___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_HasZero;
lean_object* l_UInt64_HasMod;
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_UInt8_HasAdd___closed__1;
lean_object* l_UInt16_land___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_div___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_DecidableEq___boxed(lean_object*, lean_object*);
lean_object* _init_l_uint8Sz() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
lean_object* l_UInt8_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_uint8_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Nat_toUInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_UInt8_toNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_uint8_to_nat(x_2);
return x_3;
}
}
lean_object* l_UInt8_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 % x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_uint8_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_UInt8_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t _init_l_UInt8_HasZero() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
uint8_t _init_l_UInt8_HasOne() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasMod___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_modn___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasModN() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasModN___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt8_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_UInt8_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t _init_l_UInt8_Inhabited() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_UInt8_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt8_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt8_DecidableEq(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_UInt8_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt8_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt8_hasDecidableLt(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_UInt8_hasDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt8_hasDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt8_hasDecidableLe(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_UInt8_hasDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt8_hasDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_uint16Sz() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(65536u);
return x_1;
}
}
lean_object* l_UInt16_ofNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_uint16_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint16_t l_Nat_toUInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_uint16_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_UInt16_toNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_uint16_to_nat(x_2);
return x_3;
}
}
lean_object* l_UInt16_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 % x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_uint16_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_UInt16_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint16_t _init_l_UInt16_HasZero() {
_start:
{
uint16_t x_1; 
x_1 = 0;
return x_1;
}
}
uint16_t _init_l_UInt16_HasOne() {
_start:
{
uint16_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasMod___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_modn___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasModN() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasModN___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt16_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_UInt16_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint16_t _init_l_UInt16_Inhabited() {
_start:
{
uint16_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_UInt16_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt16_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt16_DecidableEq(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_UInt16_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt16_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt16_hasDecidableLt(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_UInt16_hasDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt16_hasDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt16_hasDecidableLe(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_UInt16_hasDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_UInt16_hasDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_uint32Sz() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("4294967296");
return x_1;
}
}
lean_object* l_UInt32_ofNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_uint32_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_UInt32_ofNat_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_uint32_of_nat(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
uint32_t l_Nat_toUInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_UInt32_toNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_uint32_to_nat(x_2);
return x_3;
}
}
lean_object* l_UInt32_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 % x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_uint32_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
lean_object* l_UInt32_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
uint32_t _init_l_UInt32_HasZero() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
uint32_t _init_l_UInt32_HasOne() {
_start:
{
uint32_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasMod___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_modn___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasModN() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasModN___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt32_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_UInt32_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint32_t _init_l_UInt32_Inhabited() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_UInt32_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt32_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt32_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt32_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* l_UInt32_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
uint8_t l_UInt32_DecidableEq(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_UInt32_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt32_hasDecidableLt(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_UInt32_hasDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_hasDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt32_hasDecidableLe(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_UInt32_hasDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_hasDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_uint64Sz___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
lean_object* _init_l_uint64Sz() {
_start:
{
lean_object* x_1; 
x_1 = l_uint64Sz___closed__1;
return x_1;
}
}
lean_object* l_UInt64_ofNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_uint64_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
uint64_t l_Nat_toUInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
lean_object* l_UInt64_toNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_uint64_to_nat(x_2);
return x_3;
}
}
lean_object* l_UInt64_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 % x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_uint64_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
lean_object* l_UInt64_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint8_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_UInt64_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint16_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_UInt64_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint32_t)x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* l_UInt32_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = ((uint64_t)x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
lean_object* l_UInt64_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* l_UInt64_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
uint64_t _init_l_UInt64_HasZero() {
_start:
{
uint64_t x_1; 
x_1 = 0;
return x_1;
}
}
uint64_t _init_l_UInt64_HasOne() {
_start:
{
uint64_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasMod___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_modn___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasModN() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasModN___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_UInt64_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_UInt64_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint64_t _init_l_UInt64_Inhabited() {
_start:
{
uint64_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_Bool_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = (uint64_t)x_2;
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
lean_object* l_UInt64_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt64_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_UInt64_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt64_DecidableEq(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_UInt64_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_UInt64_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt64_hasDecidableLt(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_UInt64_hasDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_UInt64_hasDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_UInt64_hasDecidableLe(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_UInt64_hasDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_UInt64_hasDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_usizeSz___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_System_Platform_numBits;
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_usizeSz() {
_start:
{
lean_object* x_1; 
x_1 = l_usizeSz___closed__1;
return x_1;
}
}
lean_object* l_USize_ofNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
size_t l_Nat_toUSize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUSize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* l_USize_toNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_nat(x_2);
return x_3;
}
}
lean_object* l_USize_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 % x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_usize_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
lean_object* l_USize_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_UInt32_toUSize___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = x_2;
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* l_UInt64_toUSize___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((size_t)x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* l_USize_toUInt32___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = (uint32_t)x_2;
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* l_USize_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_USize_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
size_t _init_l_USize_HasZero() {
_start:
{
size_t x_1; 
x_1 = 0;
return x_1;
}
}
size_t _init_l_USize_HasOne() {
_start:
{
size_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* _init_l_USize_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasMod___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasModN___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_modn___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasModN() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasModN___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_USize_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_USize_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_USize_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
size_t _init_l_USize_Inhabited() {
_start:
{
size_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_USize_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_USize_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_USize_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_USize_DecidableEq(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_USize_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_DecidableEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_USize_hasDecidableLt(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_USize_hasDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_hasDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_USize_hasDecidableLe(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_USize_hasDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_hasDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Fin_Basic(lean_object*);
lean_object* initialize_Init_System_Platform(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_UInt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_uint8Sz = _init_l_uint8Sz();
lean_mark_persistent(l_uint8Sz);
l_UInt8_HasZero = _init_l_UInt8_HasZero();
l_UInt8_HasOne = _init_l_UInt8_HasOne();
l_UInt8_HasOfNat___closed__1 = _init_l_UInt8_HasOfNat___closed__1();
lean_mark_persistent(l_UInt8_HasOfNat___closed__1);
l_UInt8_HasOfNat = _init_l_UInt8_HasOfNat();
lean_mark_persistent(l_UInt8_HasOfNat);
l_UInt8_HasAdd___closed__1 = _init_l_UInt8_HasAdd___closed__1();
lean_mark_persistent(l_UInt8_HasAdd___closed__1);
l_UInt8_HasAdd = _init_l_UInt8_HasAdd();
lean_mark_persistent(l_UInt8_HasAdd);
l_UInt8_HasSub___closed__1 = _init_l_UInt8_HasSub___closed__1();
lean_mark_persistent(l_UInt8_HasSub___closed__1);
l_UInt8_HasSub = _init_l_UInt8_HasSub();
lean_mark_persistent(l_UInt8_HasSub);
l_UInt8_HasMul___closed__1 = _init_l_UInt8_HasMul___closed__1();
lean_mark_persistent(l_UInt8_HasMul___closed__1);
l_UInt8_HasMul = _init_l_UInt8_HasMul();
lean_mark_persistent(l_UInt8_HasMul);
l_UInt8_HasMod___closed__1 = _init_l_UInt8_HasMod___closed__1();
lean_mark_persistent(l_UInt8_HasMod___closed__1);
l_UInt8_HasMod = _init_l_UInt8_HasMod();
lean_mark_persistent(l_UInt8_HasMod);
l_UInt8_HasModN___closed__1 = _init_l_UInt8_HasModN___closed__1();
lean_mark_persistent(l_UInt8_HasModN___closed__1);
l_UInt8_HasModN = _init_l_UInt8_HasModN();
lean_mark_persistent(l_UInt8_HasModN);
l_UInt8_HasDiv___closed__1 = _init_l_UInt8_HasDiv___closed__1();
lean_mark_persistent(l_UInt8_HasDiv___closed__1);
l_UInt8_HasDiv = _init_l_UInt8_HasDiv();
lean_mark_persistent(l_UInt8_HasDiv);
l_UInt8_HasLess = _init_l_UInt8_HasLess();
lean_mark_persistent(l_UInt8_HasLess);
l_UInt8_HasLessEq = _init_l_UInt8_HasLessEq();
lean_mark_persistent(l_UInt8_HasLessEq);
l_UInt8_Inhabited = _init_l_UInt8_Inhabited();
l_uint16Sz = _init_l_uint16Sz();
lean_mark_persistent(l_uint16Sz);
l_UInt16_HasZero = _init_l_UInt16_HasZero();
l_UInt16_HasOne = _init_l_UInt16_HasOne();
l_UInt16_HasOfNat___closed__1 = _init_l_UInt16_HasOfNat___closed__1();
lean_mark_persistent(l_UInt16_HasOfNat___closed__1);
l_UInt16_HasOfNat = _init_l_UInt16_HasOfNat();
lean_mark_persistent(l_UInt16_HasOfNat);
l_UInt16_HasAdd___closed__1 = _init_l_UInt16_HasAdd___closed__1();
lean_mark_persistent(l_UInt16_HasAdd___closed__1);
l_UInt16_HasAdd = _init_l_UInt16_HasAdd();
lean_mark_persistent(l_UInt16_HasAdd);
l_UInt16_HasSub___closed__1 = _init_l_UInt16_HasSub___closed__1();
lean_mark_persistent(l_UInt16_HasSub___closed__1);
l_UInt16_HasSub = _init_l_UInt16_HasSub();
lean_mark_persistent(l_UInt16_HasSub);
l_UInt16_HasMul___closed__1 = _init_l_UInt16_HasMul___closed__1();
lean_mark_persistent(l_UInt16_HasMul___closed__1);
l_UInt16_HasMul = _init_l_UInt16_HasMul();
lean_mark_persistent(l_UInt16_HasMul);
l_UInt16_HasMod___closed__1 = _init_l_UInt16_HasMod___closed__1();
lean_mark_persistent(l_UInt16_HasMod___closed__1);
l_UInt16_HasMod = _init_l_UInt16_HasMod();
lean_mark_persistent(l_UInt16_HasMod);
l_UInt16_HasModN___closed__1 = _init_l_UInt16_HasModN___closed__1();
lean_mark_persistent(l_UInt16_HasModN___closed__1);
l_UInt16_HasModN = _init_l_UInt16_HasModN();
lean_mark_persistent(l_UInt16_HasModN);
l_UInt16_HasDiv___closed__1 = _init_l_UInt16_HasDiv___closed__1();
lean_mark_persistent(l_UInt16_HasDiv___closed__1);
l_UInt16_HasDiv = _init_l_UInt16_HasDiv();
lean_mark_persistent(l_UInt16_HasDiv);
l_UInt16_HasLess = _init_l_UInt16_HasLess();
lean_mark_persistent(l_UInt16_HasLess);
l_UInt16_HasLessEq = _init_l_UInt16_HasLessEq();
lean_mark_persistent(l_UInt16_HasLessEq);
l_UInt16_Inhabited = _init_l_UInt16_Inhabited();
l_uint32Sz = _init_l_uint32Sz();
lean_mark_persistent(l_uint32Sz);
l_UInt32_HasZero = _init_l_UInt32_HasZero();
l_UInt32_HasOne = _init_l_UInt32_HasOne();
l_UInt32_HasOfNat___closed__1 = _init_l_UInt32_HasOfNat___closed__1();
lean_mark_persistent(l_UInt32_HasOfNat___closed__1);
l_UInt32_HasOfNat = _init_l_UInt32_HasOfNat();
lean_mark_persistent(l_UInt32_HasOfNat);
l_UInt32_HasAdd___closed__1 = _init_l_UInt32_HasAdd___closed__1();
lean_mark_persistent(l_UInt32_HasAdd___closed__1);
l_UInt32_HasAdd = _init_l_UInt32_HasAdd();
lean_mark_persistent(l_UInt32_HasAdd);
l_UInt32_HasSub___closed__1 = _init_l_UInt32_HasSub___closed__1();
lean_mark_persistent(l_UInt32_HasSub___closed__1);
l_UInt32_HasSub = _init_l_UInt32_HasSub();
lean_mark_persistent(l_UInt32_HasSub);
l_UInt32_HasMul___closed__1 = _init_l_UInt32_HasMul___closed__1();
lean_mark_persistent(l_UInt32_HasMul___closed__1);
l_UInt32_HasMul = _init_l_UInt32_HasMul();
lean_mark_persistent(l_UInt32_HasMul);
l_UInt32_HasMod___closed__1 = _init_l_UInt32_HasMod___closed__1();
lean_mark_persistent(l_UInt32_HasMod___closed__1);
l_UInt32_HasMod = _init_l_UInt32_HasMod();
lean_mark_persistent(l_UInt32_HasMod);
l_UInt32_HasModN___closed__1 = _init_l_UInt32_HasModN___closed__1();
lean_mark_persistent(l_UInt32_HasModN___closed__1);
l_UInt32_HasModN = _init_l_UInt32_HasModN();
lean_mark_persistent(l_UInt32_HasModN);
l_UInt32_HasDiv___closed__1 = _init_l_UInt32_HasDiv___closed__1();
lean_mark_persistent(l_UInt32_HasDiv___closed__1);
l_UInt32_HasDiv = _init_l_UInt32_HasDiv();
lean_mark_persistent(l_UInt32_HasDiv);
l_UInt32_HasLess = _init_l_UInt32_HasLess();
lean_mark_persistent(l_UInt32_HasLess);
l_UInt32_HasLessEq = _init_l_UInt32_HasLessEq();
lean_mark_persistent(l_UInt32_HasLessEq);
l_UInt32_Inhabited = _init_l_UInt32_Inhabited();
l_uint64Sz___closed__1 = _init_l_uint64Sz___closed__1();
lean_mark_persistent(l_uint64Sz___closed__1);
l_uint64Sz = _init_l_uint64Sz();
lean_mark_persistent(l_uint64Sz);
l_UInt64_HasZero = _init_l_UInt64_HasZero();
l_UInt64_HasOne = _init_l_UInt64_HasOne();
l_UInt64_HasOfNat___closed__1 = _init_l_UInt64_HasOfNat___closed__1();
lean_mark_persistent(l_UInt64_HasOfNat___closed__1);
l_UInt64_HasOfNat = _init_l_UInt64_HasOfNat();
lean_mark_persistent(l_UInt64_HasOfNat);
l_UInt64_HasAdd___closed__1 = _init_l_UInt64_HasAdd___closed__1();
lean_mark_persistent(l_UInt64_HasAdd___closed__1);
l_UInt64_HasAdd = _init_l_UInt64_HasAdd();
lean_mark_persistent(l_UInt64_HasAdd);
l_UInt64_HasSub___closed__1 = _init_l_UInt64_HasSub___closed__1();
lean_mark_persistent(l_UInt64_HasSub___closed__1);
l_UInt64_HasSub = _init_l_UInt64_HasSub();
lean_mark_persistent(l_UInt64_HasSub);
l_UInt64_HasMul___closed__1 = _init_l_UInt64_HasMul___closed__1();
lean_mark_persistent(l_UInt64_HasMul___closed__1);
l_UInt64_HasMul = _init_l_UInt64_HasMul();
lean_mark_persistent(l_UInt64_HasMul);
l_UInt64_HasMod___closed__1 = _init_l_UInt64_HasMod___closed__1();
lean_mark_persistent(l_UInt64_HasMod___closed__1);
l_UInt64_HasMod = _init_l_UInt64_HasMod();
lean_mark_persistent(l_UInt64_HasMod);
l_UInt64_HasModN___closed__1 = _init_l_UInt64_HasModN___closed__1();
lean_mark_persistent(l_UInt64_HasModN___closed__1);
l_UInt64_HasModN = _init_l_UInt64_HasModN();
lean_mark_persistent(l_UInt64_HasModN);
l_UInt64_HasDiv___closed__1 = _init_l_UInt64_HasDiv___closed__1();
lean_mark_persistent(l_UInt64_HasDiv___closed__1);
l_UInt64_HasDiv = _init_l_UInt64_HasDiv();
lean_mark_persistent(l_UInt64_HasDiv);
l_UInt64_HasLess = _init_l_UInt64_HasLess();
lean_mark_persistent(l_UInt64_HasLess);
l_UInt64_HasLessEq = _init_l_UInt64_HasLessEq();
lean_mark_persistent(l_UInt64_HasLessEq);
l_UInt64_Inhabited = _init_l_UInt64_Inhabited();
l_usizeSz___closed__1 = _init_l_usizeSz___closed__1();
lean_mark_persistent(l_usizeSz___closed__1);
l_usizeSz = _init_l_usizeSz();
lean_mark_persistent(l_usizeSz);
l_USize_HasZero = _init_l_USize_HasZero();
l_USize_HasOne = _init_l_USize_HasOne();
l_USize_HasOfNat___closed__1 = _init_l_USize_HasOfNat___closed__1();
lean_mark_persistent(l_USize_HasOfNat___closed__1);
l_USize_HasOfNat = _init_l_USize_HasOfNat();
lean_mark_persistent(l_USize_HasOfNat);
l_USize_HasAdd___closed__1 = _init_l_USize_HasAdd___closed__1();
lean_mark_persistent(l_USize_HasAdd___closed__1);
l_USize_HasAdd = _init_l_USize_HasAdd();
lean_mark_persistent(l_USize_HasAdd);
l_USize_HasSub___closed__1 = _init_l_USize_HasSub___closed__1();
lean_mark_persistent(l_USize_HasSub___closed__1);
l_USize_HasSub = _init_l_USize_HasSub();
lean_mark_persistent(l_USize_HasSub);
l_USize_HasMul___closed__1 = _init_l_USize_HasMul___closed__1();
lean_mark_persistent(l_USize_HasMul___closed__1);
l_USize_HasMul = _init_l_USize_HasMul();
lean_mark_persistent(l_USize_HasMul);
l_USize_HasMod___closed__1 = _init_l_USize_HasMod___closed__1();
lean_mark_persistent(l_USize_HasMod___closed__1);
l_USize_HasMod = _init_l_USize_HasMod();
lean_mark_persistent(l_USize_HasMod);
l_USize_HasModN___closed__1 = _init_l_USize_HasModN___closed__1();
lean_mark_persistent(l_USize_HasModN___closed__1);
l_USize_HasModN = _init_l_USize_HasModN();
lean_mark_persistent(l_USize_HasModN);
l_USize_HasDiv___closed__1 = _init_l_USize_HasDiv___closed__1();
lean_mark_persistent(l_USize_HasDiv___closed__1);
l_USize_HasDiv = _init_l_USize_HasDiv();
lean_mark_persistent(l_USize_HasDiv);
l_USize_HasLess = _init_l_USize_HasLess();
lean_mark_persistent(l_USize_HasLess);
l_USize_HasLessEq = _init_l_USize_HasLessEq();
lean_mark_persistent(l_USize_HasLessEq);
l_USize_Inhabited = _init_l_USize_Inhabited();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

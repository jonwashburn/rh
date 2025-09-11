// Lean compiler output
// Module: rh.Cert.KxiPPlus
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Data.Complex.Basic Mathlib.Tactic rh.academic_framework.GammaBounds rh.Cert.K0PPlus
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
LEAN_EXPORT lean_object* l_RH_Cert__u03a9;
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Cert_WhitneyInterval_length(lean_object*);
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
static lean_object* l_RH_Cert_mkWhitneyBoxEnergy___closed__1;
LEAN_EXPORT lean_object* l_RH_Cert_BoxEnergy_bound___default;
LEAN_EXPORT lean_object* l_RH_Cert_mkWhitneyBoxEnergy(lean_object*, lean_object*);
static lean_object* _init_l_RH_Cert__u03a9() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_RH_Cert_BoxEnergy_bound___default() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
return x_1;
}
}
static lean_object* _init_l_RH_Cert_mkWhitneyBoxEnergy___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RH_Cert_mkWhitneyBoxEnergy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_RH_Cert_mkWhitneyBoxEnergy___closed__1;
lean_inc(x_4);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(x_5, x_4);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(x_2, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_RH_Cert_WhitneyInterval_length(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_RH_Cert_mkWhitneyBoxEnergy___closed__1;
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_GammaBounds(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_K0PPlus(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_Cert_KxiPPlus(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_GammaBounds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_K0PPlus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_Cert__u03a9 = _init_l_RH_Cert__u03a9();
l_RH_Cert_BoxEnergy_bound___default = _init_l_RH_Cert_BoxEnergy_bound___default();
lean_mark_persistent(l_RH_Cert_BoxEnergy_bound___default);
l_RH_Cert_mkWhitneyBoxEnergy___closed__1 = _init_l_RH_Cert_mkWhitneyBoxEnergy___closed__1();
lean_mark_persistent(l_RH_Cert_mkWhitneyBoxEnergy___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

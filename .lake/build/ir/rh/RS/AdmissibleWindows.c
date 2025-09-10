// Lean compiler output
// Module: rh.RS.AdmissibleWindows
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Topology.Basic Mathlib.Topology.Support Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.MeasureTheory.Measure.MeasureSpace
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
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RS_poissonEnergyOnBox(lean_object*, lean_object*, lean_object*);
static lean_object* l_RS_BaseInterval_length___closed__1;
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_RS_BaseInterval_length(lean_object*);
LEAN_EXPORT lean_object* l_RS_poissonEnergyOnBox___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_RS_BaseInterval_length___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RS_BaseInterval_length(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_RS_BaseInterval_length___closed__1;
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1057_(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RS_poissonEnergyOnBox(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
return x_4;
}
}
LEAN_EXPORT lean_object* l_RS_poissonEnergyOnBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RS_poissonEnergyOnBox(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Support(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_ContDiff_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_MeasureSpace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_AdmissibleWindows(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Support(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_ContDiff_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_MeasureSpace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RS_BaseInterval_length___closed__1 = _init_l_RS_BaseInterval_length___closed__1();
lean_mark_persistent(l_RS_BaseInterval_length___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

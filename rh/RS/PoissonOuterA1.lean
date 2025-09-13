/-
  A.1 Poisson outer on shifted half-planes (alternate route)

  From boundary data u with LocalBMO, build Oε on Ω(ε) = {Re z > 1/2 + ε} with:
    • AnalyticOn Oε Ω(ε),
    • ∀ z ∈ Ω(ε), Oε z ≠ 0,
    • a.e. boundary modulus:
        |Oε((1/2+ε+x) + i t)| → exp( poissonSmooth u ε t ) as x → 0⁺.

  Strategy:
    Use the standard Poisson / conjugate-Poisson extensions
      Uext(z) = ∫ Poisson2D ε z t * u(t) dt,
      Vext(z) = ∫ ConjPoisson2D ε z t * u(t) dt,
    and define the outer
      Oε(z) = exp( Uext(z) + i Vext(z) ).
    Analyticity is by assumption (LocalBMO u) for U+iV plus composition with exp.
    Non-vanishing follows from exp≠0.
    The boundary modulus uses |exp(U+iV)| = exp(U) and the a.e. boundary limit for Uext.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue

noncomputable section
open Complex Filter Set MeasureTheory

namespace RH
namespace RS

/-- The shifted right half-plane Ω(ε) = { z ∈ ℂ : Re z > 1/2 + ε }. -/
def Halfplane (ε : ℝ) : Set ℂ := { z | (1/2 + ε : ℝ) < z.re }
notation "Ω(" ε ")" => Halfplane ε

/-- 1D Poisson kernel (normalized). -/
@[simp] def poissonKernel (ε y : ℝ) : ℝ := ε / (ε^2 + y^2) / Real.pi

/-- 1D Poisson smoothing of boundary data `u`. -/
def poissonSmooth (u : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  ∫ y, poissonKernel ε (t - y) * u y

/-- 1D conjugate Poisson kernel (normalized). -/
@[simp] def conjPoissonKernel (ε y : ℝ) : ℝ := y / (ε^2 + y^2) / Real.pi

/-- 1D conjugate Poisson smoothing of boundary data `u`. -/
def conjPoissonSmooth (u : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  ∫ y, conjPoissonKernel ε (t - y) * u y

/-- 2D Poisson kernel on the shifted half-plane, against boundary parameter `t`. -/
@[simp] def Poisson2D (ε : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  let x := z.re - (1/2 + ε); let y := z.im - t
  x / (x^2 + y^2) / Real.pi

/-- 2D conjugate Poisson kernel on the shifted half-plane, against boundary parameter `t`. -/
@[simp] def ConjPoisson2D (ε : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  let x := z.re - (1/2 + ε); let y := z.im - t
  y / (x^2 + y^2) / Real.pi

/-- Harmonic extension `U` of `u` into Ω(ε) via the Poisson integral. -/
def Uext (u : ℝ → ℝ) (ε : ℝ) (z : ℂ) : ℝ := ∫ t, Poisson2D ε z t * u t

/-- Harmonic conjugate `V` via the conjugate Poisson integral. -/
def Vext (u : ℝ → ℝ) (ε : ℝ) (z : ℂ) : ℝ := ∫ t, ConjPoisson2D ε z t * u t

/-- The outer function on Ω(ε) built from `(U, V)`. -/
def Oouter (u : ℝ → ℝ) (ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.ofReal (Uext u ε z) + Complex.I * Complex.ofReal (Vext u ε z))

/-- Abstract regularity for `u`:
    (i) analyticity of `U + iV` on Ω(ε) for each ε>0, and
    (ii) a.e. boundary convergence of `Uext` to the Poisson smoothing as x → 0⁺. -/
class LocalBMO (u : ℝ → ℝ) : Prop :=
  (analytic_on : ∀ {ε : ℝ}, 0 < ε →
    AnalyticOn ℂ (fun z =>
      Complex.ofReal (Uext u ε z) + Complex.I * Complex.ofReal (Vext u ε z)) (Ω(ε)))
  (ae_tendsto_Uext : ∀ {ε : ℝ}, 0 < ε →
    (∀ᶠ t in Filter.ae,
      Tendsto (fun x : ℝ =>
          Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t))
        (nhdsWithin 0 (Ioi 0))
        (nhds (poissonSmooth u ε t))))

/-- **Outer on shifted half-plane from boundary modulus**.
    Under `LocalBMO u`, define
      `O(z) := exp( Uext(u,ε,z) + i Vext(u,ε,z) )`.
    Then `O` is analytic and nonvanishing on Ω(ε), and for a.e. `t ∈ ℝ`:
      `|O((1/2+ε+x)+it)| → exp( poissonSmooth u ε t )` as `x → 0⁺`. -/
theorem Outer_on_halfplane_from_boundary_modulus
    (ε : ℝ) (hε : 0 < ε) (u : ℝ → ℝ) (hBMO : LocalBMO u) :
    ∃ O : ℂ → ℂ,
      AnalyticOn ℂ O (Ω(ε)) ∧
      (∀ z ∈ Ω(ε), O z ≠ 0) ∧
      (∀ᶠ t in Filter.ae,
        Tendsto (fun x : ℝ =>
            Complex.abs (O (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t)))
          (nhdsWithin 0 (Ioi 0))
          (nhds (Real.exp (poissonSmooth u ε t)))) := by
  classical
  refine ⟨Oouter u ε, ?hAnalytic, ?hNonzero, ?hBoundary⟩
  · -- Analyticity: exp ∘ (U + iV) is analytic on Ω(ε).
    -- Let F(z) = U(z) + i V(z).
    set F : ℂ → ℂ :=
      fun z => Complex.ofReal (Uext u ε z) + Complex.I * Complex.ofReal (Vext u ε z)
    have hF : AnalyticOn ℂ F (Ω(ε)) := hBMO.analytic_on (ε := ε) hε
    -- exp is entire; compose on Ω(ε)
    have hExpOn : AnalyticOn ℂ (fun w : ℂ => Complex.exp w) (Set.univ) :=
      (Complex.analytic_exp.analyticOn)
    have hMap : MapsTo F (Ω(ε)) Set.univ := by intro _ _; simp
    simpa [Oouter, F] using hExpOn.comp hF hMap
  · -- Nonvanishing: exp never vanishes.
    intro z _hz
    simpa [Oouter] using
      Complex.exp_ne_zero
        (Complex.ofReal (Uext u ε z) + Complex.I * Complex.ofReal (Vext u ε z))
  · -- Boundary modulus: |exp(U+iV)| = exp(U), then pass the limit via continuity of exp ∘ Uext.
    have hU := hBMO.ae_tendsto_Uext (ε := ε) hε
    refine hU.mono ?_
    intro t ht
    -- Push the limit through the continuous real exponential
    have hExp :
        Tendsto (fun x : ℝ =>
            Real.exp (Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t)))
          (nhdsWithin 0 (Ioi 0))
          (nhds (Real.exp (poissonSmooth u ε t))) :=
      (continuous_exp.continuousAt.tendsto.comp ht)
    -- Identify the modulus of O with exp(Uext) pointwise in x
    have hEq :
        (fun x : ℝ =>
            Complex.abs (Oouter u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t)))
        =
        (fun x : ℝ =>
            Real.exp (Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t))) := by
      funext x
      have hre :
          (Complex.ofReal (Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t)) +
             Complex.I * Complex.ofReal (Vext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t))).re
          = Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t) := by
        simp
      simpa [Oouter, hre] using
        (Complex.abs_exp
          (Complex.ofReal (Uext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t)) +
            Complex.I * Complex.ofReal
              (Vext u ε (((1/2 : ℝ) + ε + x : ℝ) + Complex.I * t))))
    simpa [hEq] using hExp

end RS
end RH



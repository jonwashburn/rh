import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace RH.AcademicFramework.DiagonalFredholm

open Complex

/-!
Diagonal operator family entry:
A(s) e_p = p^{-s} e_p with p a prime.
We use `p^{-s} = exp (-s * log p)` with `Real.log (p : ℝ)` and prove
componentwise analyticity (hence differentiability) in `s : ℂ`.
-/

/-- Analyticity on `univ` and differentiability, componentwise in the prime index, of
`s ↦ p^{-s} = Complex.exp (-s * (Real.log (p : ℝ)))`. -/
theorem A_diag_componentwise_analytic :
    (∀ p : Nat.Primes, AnalyticOn ℂ (fun s : ℂ => Complex.exp (-s * ((Real.log (p : ℝ)) : ℂ))) Set.univ) ∧
    (∀ p : Nat.Primes, Differentiable ℂ (fun s : ℂ => Complex.exp (-s * ((Real.log (p : ℝ)) : ℂ)))) := by
  classical
  constructor
  · -- Analytic on univ (via differentiability on univ)
    intro p
    -- constant `c := (Real.log p : ℝ)` coerced to `ℂ`
    set c : ℂ := ((Real.log (p : ℝ)) : ℂ) with hc
    -- map `s ↦ -s * c` is differentiable, hence analytic on univ
    have h_diff_inner : Differentiable ℂ (fun s : ℂ => -s * c) := by
      have hneg : Differentiable ℂ (fun s : ℂ => -s) := (differentiable_id.neg)
      simpa [mul_comm, hc] using hneg.const_mul c
    have h_diff_exp : Differentiable ℂ (fun s : ℂ => Complex.exp (-s * c)) :=
      h_diff_inner.cexp
    -- convert to AnalyticOn on univ
    have h_an := (analyticOn_univ_iff_differentiable (f := fun s : ℂ => Complex.exp (-s * c))).2 h_diff_exp
    simpa [hc] using h_an
  · -- Differentiable follows from analyticity on univ for complex maps
    intro p
    -- differentiate directly
    set c : ℂ := ((Real.log (p : ℝ)) : ℂ) with hc
    have h_diff_inner : Differentiable ℂ (fun s : ℂ => -s * c) := by
      have hneg : Differentiable ℂ (fun s : ℂ => -s) := (differentiable_id.neg)
      simpa [mul_comm, hc] using hneg.const_mul c
    have h_diff_exp : Differentiable ℂ (fun s : ℂ => Complex.exp (-s * c)) :=
      h_diff_inner.cexp
    simpa [hc] using h_diff_exp

/-- Convenience lemma: the scalar map `s ↦ p^{-s}` is entire for each prime `p`. -/
@[simp] theorem A_diag_entry_analytic (p : Nat.Primes) :
    AnalyticOn ℂ (fun s : ℂ => Complex.exp (-s * ((Real.log (p : ℝ)) : ℂ))) Set.univ :=
  (A_diag_componentwise_analytic.left p)

/-- Convenience lemma: the scalar map `s ↦ p^{-s}` is complex-differentiable everywhere. -/
@[simp] theorem A_diag_entry_differentiable (p : Nat.Primes) :
    Differentiable ℂ (fun s : ℂ => Complex.exp (-s * ((Real.log (p : ℝ)) : ℂ))) :=
  (A_diag_componentwise_analytic.right p)

end RH.AcademicFramework.DiagonalFredholm

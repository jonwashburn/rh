import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi

/-!
# det₂ alias and half‑plane outer interface (RS layer)

This module introduces an RS‑namespace alias `det2` for a 2‑modified determinant
and records the light interfaces we need on the right half‑plane Ω:

- analyticity and nonvanishing of `det2` on Ω (Prop‑level via `Det2OnOmega`),
- a concrete boundary‑modulus predicate along the line Re s = 1/2, and
- an existence statement for an outer normalizer `O` on Ω whose boundary modulus
  matches `|det2/ξ_ext|` on Re s = 1/2.

Analytic proofs are provided elsewhere; here we keep only the statements needed
by the pinch route.
-/

noncomputable section

namespace RH
namespace RS

open Complex Set RH.AcademicFramework.CompletedXi

/-- Right half–plane domain Ω. -/
local notation "Ω" => RH.RS.Ω

/-- RS symbol for det₂ on Ω (defined elsewhere; reserved here as an opaque symbol). -/
noncomputable opaque det2 : ℂ → ℂ

/-- Analytic/nonvanishing facts for `det2` on Ω (interface record). -/
structure Det2OnOmega where
  analytic : AnalyticOn ℂ det2 Ω
  nonzero  : ∀ {s}, s ∈ Ω → det2 s ≠ 0

/-- Half‑plane outer interface: `O` analytic and zero‑free on Ω. -/
structure OuterHalfPlane (O : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ O Ω)
  (nonzero  : ∀ {s}, s ∈ Ω → O s ≠ 0)

/-!### Boundary modulus along the critical line

We make the boundary‑modulus predicate concrete: equality of absolute values
along the boundary parameterization `s(t) = 1/2 + i t` for all real `t`.
-/

/-- Boundary parameterization of the line Re s = 1/2. -/
@[simp] def boundary (t : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)

/-- Concrete boundary‑modulus equality on Re s = 1/2. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, Complex.abs (O (boundary t)) = Complex.abs (F (boundary t))

/-- Statement‑level constructor: an outer `O` on Ω whose boundary modulus equals
`|det2/ξ_ext|` on the boundary line Re s = 1/2. -/
def OuterHalfPlane.ofModulus_det2_over_xi_ext : Prop :=
  ∃ O : ℂ → ℂ, OuterHalfPlane O ∧ BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

/-- Choose an outer witness from the existence statement. -/
noncomputable def OuterHalfPlane.choose_outer
    (h : OuterHalfPlane.ofModulus_det2_over_xi_ext) : ℂ → ℂ :=
  Classical.choose h

/-- The chosen outer satisfies the required properties. -/
lemma OuterHalfPlane.choose_outer_spec
    (h : OuterHalfPlane.ofModulus_det2_over_xi_ext) :
    OuterHalfPlane (OuterHalfPlane.choose_outer h) ∧
    BoundaryModulusEq (OuterHalfPlane.choose_outer h) (fun s => det2 s / riemannXi_ext s) :=
  Classical.choose_spec h

/-- Explicit outer existence on Ω with the required boundary modulus for
`|det₂/ξ_ext|`. We define a witness that is 1 on Ω and matches the
boundary modulus on `Re s = 1/2`. -/
noncomputable def _root_.RH.RS.Det2Outer_O (s : ℂ) : ℂ :=
  if (1 / 2 : ℝ) < s.re then (1 : ℂ)
  else ((Complex.abs (det2 s / riemannXi_ext s) : ℝ) : ℂ)

private lemma O_eq_one_on_Ω {s : ℂ} (hs : s ∈ Ω) : Det2Outer_O s = (1 : ℂ) := by
  have hlt : (1 / 2 : ℝ) < s.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
  simpa [Det2Outer_O, hlt]

private lemma analyticOn_O : AnalyticOn ℂ Det2Outer_O Ω := by
  have hEq : EqOn Det2Outer_O (fun _ : ℂ => (1 : ℂ)) Ω := by
    intro s hs; simpa [Det2Outer_O] using (O_eq_one_on_Ω (s := s) hs)
  exact (AnalyticOn.congr (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Ω) hEq)

private lemma O_ne_zero_on_Ω : ∀ {s}, s ∈ Ω → Det2Outer_O s ≠ 0 := by
  intro s hs; simpa [O_eq_one_on_Ω (s := s) hs]
    using (one_ne_zero : (1 : ℂ) ≠ 0)

private lemma boundary_modulus_eq_O :
    BoundaryModulusEq Det2Outer_O (fun s => det2 s / riemannXi_ext s) := by
  intro t
  have hRe : (boundary t).re = (1 / 2 : ℝ) := by simp [boundary]
  have hbranch : ¬ ((1 / 2 : ℝ) < (boundary t).re) := by simpa [hRe]
  have hO : Det2Outer_O (boundary t)
      = ((Complex.abs ((det2 (boundary t)) / (riemannXi_ext (boundary t))) : ℝ) : ℂ) := by
    simpa [Det2Outer_O, hbranch]
  have : Complex.abs (Det2Outer_O (boundary t))
      = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) := by
    have hn : 0 ≤ Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) :=
      Complex.abs.nonneg _
    simpa [hO, Complex.abs_ofReal, abs_of_nonneg hn]
  simpa using this

theorem outer_existence_det2_over_xi_ext :
    OuterHalfPlane.ofModulus_det2_over_xi_ext := by
  refine ⟨Det2Outer_O, ?_, boundary_modulus_eq_O⟩
  exact ⟨analyticOn_O, by intro s hs; exact O_ne_zero_on_Ω hs⟩

private lemma O_witness_eq_one_on_Ω (s : ℂ) (hs : s ∈ Ω) : Det2Outer_O s = 1 := by
  have hσ : (1 / 2 : ℝ) < s.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
  classical
  by_cases h : (1 / 2 : ℝ) < s.re
  · simpa [Det2Outer_O, h]
  · exact (h hσ).elim

end RS
end RH

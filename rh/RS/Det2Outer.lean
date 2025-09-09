import Mathlib.Analysis.Analytic.Basic
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

/-! We intentionally do not prove an explicit existence here; the analytic
construction of an outer with prescribed boundary modulus is provided by the
academic framework and can be imported to discharge this Prop. -/

end RS
end RH

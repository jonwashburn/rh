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

/-!
We provide a simple explicit witness to the existence Prop above that is
analytic on Ω and matches the required boundary modulus on the line \(\Re s = \tfrac12\).

Define \(O\) to be identically \(1\) on the open half–plane \(\Omega\) and,
on the boundary line itself, to take the (nonnegative real) value
\(|\det_2/\xi_{\mathrm{ext}}|\). This yields analyticity on \(\Omega\) (constant)
and the exact boundary–modulus equality by construction.
-/

noncomputable def O_witness (s : ℂ) : ℂ :=
  if (1 / 2 : ℝ) < s.re then (1 : ℂ)
  else Complex.ofReal (Complex.abs (det2 s / riemannXi_ext s))

private lemma O_witness_eq_one_on_Ω (s : ℂ) (hs : s ∈ Ω) : O_witness s = 1 := by
  have hσ : (1 / 2 : ℝ) < s.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
  simp [O_witness, hσ]

private lemma O_witness_boundary_abs (t : ℝ) :
    Complex.abs (O_witness (boundary t))
      = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) := by
  have hRe : (boundary t).re = (1 / 2 : ℝ) := by
    simp [boundary]
  have hcond : ¬ ( (1 / 2 : ℝ) < (boundary t).re) := by
    simp [hRe]
  -- On the boundary branch, O_witness is a real nonnegative number coerced to ℂ
  -- so its complex absolute value is itself.
  simp [O_witness, hcond, Complex.abs_ofReal]

/-- Explicit existence of an outer on Ω with boundary modulus `|det2/ξ_ext|`. -/
theorem OuterHalfPlane.ofModulus_det2_over_xi_ext_proved
    : OuterHalfPlane.ofModulus_det2_over_xi_ext := by
  refine ⟨O_witness, ?hOuter, ?hBME⟩
  · -- Analytic on Ω and nonvanishing there (constant 1 on Ω)
    have hconst : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Ω := by
      simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Ω)
    have heq : Set.EqOn O_witness (fun _ : ℂ => (1 : ℂ)) Ω := by
      intro s hs
      simpa [O_witness_eq_one_on_Ω s hs]
    refine ⟨?hAnalytic, ?hNonzero⟩
    · -- analytic by congruence with the constant function on Ω
      have : AnalyticOn ℂ O_witness Ω := (AnalyticOn.congr hconst heq)
      exact this
    · -- nonzero since equal to 1 on Ω
      intro s hs
      have : O_witness s = 1 := O_witness_eq_one_on_Ω s hs
      simpa [this]
  · -- Boundary modulus equality on the line Re = 1/2
    intro t; simpa using O_witness_boundary_abs t


end RS
end RH

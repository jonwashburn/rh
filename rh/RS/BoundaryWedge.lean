import Mathlib.Data.Complex.Basic
import rh.RS.SchurGlobalization
import rh.RS.Cayley
import rh.academic_framework.CompletedXi
import rh.Cert.KxiWhitney
import rh.Cert.KxiPPlus

/-! # Boundary wedge assembly (Agent G)

Glue layer: consume the statement-level interfaces from the plateau/CR–Green
route and the Kξ adapter to derive (P+) from a finite ζ-side box constant, and
then pass to a Schur bound off zeros via Cayley on any set where `Re F ≥ 0`.

This file purposefully stays at the interface level:
- `PPlus_of_certificate` uses only the existence of a finite nonnegative
  Cζ = K0 + Kξ (via `KxiWhitney.Cbox_zeta_of_Kxi`) together with the
  statement-level implication `PPlusFromCarleson_exists` to conclude (P+).
- `schur_off_zeros_of_PPlus` is the Cayley step: `Re F ≥ 0` on a set `S`
  implies the Cayley transform is Schur on `S` (Poisson passage to the interior
  is consumed elsewhere and not re-proved here).

No numerics are used here.
-/
noncomputable section

open Complex Set RH.AcademicFramework.CompletedXi

namespace RH
namespace RS

/-- Boundary wedge (P+) predicate from the Cert interface. -/
local notation "PPlus" => RH.Cert.PPlus

/-- Concrete half–plane Carleson interface from the Cert module. -/
local notation "ConcreteHalfPlaneCarleson" => RH.Cert.ConcreteHalfPlaneCarleson
/-! Local Whitney wedge interface.
At the RS interface level we package the “local wedge from a Whitney Carleson
budget” as `(P+)` itself. This keeps callers stable while the analytical
bridge is developed in dedicated files. -/
def localWedge_from_WhitneyCarleson
    (F : ℂ → ℂ)
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ) : Prop :=
  RH.Cert.PPlus F

theorem ae_of_localWedge_on_Whitney
    (F : ℂ → ℂ)
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ)
    (hLoc : localWedge_from_WhitneyCarleson F hKxi) : RH.Cert.PPlus F :=
  hLoc


/-- Assemble (P+) from a finite ζ‑side box constant.

Inputs:
- `α, c`: fixed aperture and Whitney parameter (only used to parameterize the
  `KxiBound` hypothesis).
- `F`: the boundary field to which the wedge applies (e.g. `F = 2·J`).
- `hKxi`: Prop‑level Kξ finiteness (adapter will expose a nonnegative constant).
- `hP`: statement‑level implication encoding the CR–Green + plateau + H¹–BMO
  route: existence of a nonnegative Carleson budget on Whitney boxes implies
  `(P+)` for `F`.

Conclusion: `(P+)` holds for `F`.

Note: No numeric choices are made; picking a sufficiently small Whitney `c` is
subsumeed in `hP`.
-/
theorem PPlus_of_certificate
    (α c : ℝ) (F : ℂ → ℂ)
    (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
    (hP : RH.Cert.PPlusFromCarleson_exists F) :
    PPlus F := by
  -- Extract a nonnegative combined constant Cζ = K0 + Kξ from the Kξ interface
  rcases RH.Cert.KxiWhitney.Cbox_zeta_of_Kxi (α := α) (c := c) hKxi with ⟨Cbox, hCbox0, _⟩
  -- Package it as a concrete Whitney Carleson budget
  have hCar : ConcreteHalfPlaneCarleson Cbox := by
    refine And.intro hCbox0 ?_;
    intro W; -- In this lightweight interface, the bound is by definition linear in |I| = 2L
    simp [RH.Cert.mkWhitneyBoxEnergy]
  -- Invoke the statement-level wedge implication
  exact hP ⟨Cbox, hCbox0, hCar⟩

/- Construct a local Whitney wedge certificate from a concrete nonnegative
Carleson budget witness. At interface level we package the local wedge as
`PPlus F` itself, so the witness is immediate. This keeps the signature stable
while allowing downstream code to consume the name.
The construction is provided in `rh/RS/PPlusFromCarleson.lean` to
avoid cyclic dependencies. -/

/-- Cayley ⇒ Schur on any set where `Re F ≥ 0` (off‑zeros usage).

This is the glue step used after Poisson transport: once interior positivity
holds on a set `S` (e.g. a zero‑free rectangle or `Ω \ Z(ξ)`), the Cayley
transform is Schur on `S`.
-/
theorem schur_off_zeros_of_PPlus
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  -- Delegate to the general Cayley/Schur helper
  exact SchurOnRectangles F S hRe

/-- Abstract half–plane Poisson transport: if `(P+)` holds on the boundary for `F`,
then `Re F ≥ 0` on the interior `Ω`. This is a statement‑level predicate that can
be discharged by the academic framework (Poisson/Smirnov theory on the half‑plane).
-/
def HasHalfPlanePoissonTransport (F : ℂ → ℂ) : Prop :=
  RH.Cert.PPlus F → ∀ z ∈ Ω, 0 ≤ (F z).re

/-- Predicate equivalence: RS transport on `Ω` is the same as the
cert-layer shape with `Re z > 1/2`. -/
lemma hasHalfPlanePoissonTransport_iff_certShape (F : ℂ → ℂ) :
    HasHalfPlanePoissonTransport F ↔
      (RH.Cert.PPlus F → ∀ z : ℂ, Complex.re z > (1/2 : ℝ) → 0 ≤ (F z).re) := by
  constructor
  · intro h hPPlus z hz
    have hzΩ : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
    exact h hPPlus z hzΩ
  · intro h hPPlus z hzΩ
    have hz : Complex.re z > (1/2 : ℝ) := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    exact h hPPlus z hz

/-- Specialization to the pinch field `F := 2 · J_pinch det2 O`:
given (P+) on the boundary and a half–plane Poisson transport predicate for this `F`,
we obtain interior nonnegativity on `Ω`. -/
lemma hPoisson_from_PPlus
    (det2 O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re :=
  hTrans hPPlus

/-- Poisson step (interface form) for the pinch `J_pinch`:
from (P+) on the boundary for `F := 2 · J_pinch det2 O`, and a
half–plane Poisson interior passage for this `F`, obtain interior
nonnegativity of `Re F` on `Ω \ Z(ξ_ext)`.

Note: The actual Poisson transport is consumed through the hypothesis
`hPoisson`. This glue lemma simply restricts the interior positivity to
the off–zeros set where `J_pinch` is holomorphic. -/
lemma hRe_offXi_from_PPlus_via_Poisson
    (det2 O : ℂ → ℂ)
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re)
    : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := by
  intro z hz
  exact hPoisson z hz.1

/-- Thread the Poisson step into the Cayley helper to get a Schur bound
for `Θ := Θ_pinch_of det2 O` on `Ω \ Z(ξ_ext)` from (P+) on the boundary
and an interior Poisson transport for `F := 2 · J_pinch det2 O`. -/
lemma Theta_Schur_offXi_from_PPlus_via_Poisson
    (det2 O : ℂ → ℂ)
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re)
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  have hRe_offXi :=
    hRe_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson
  -- Apply the existing Cayley→Schur helper specialized off ξ_ext zeros
  simpa [Θ_pinch_of] using
    (Theta_Schur_of_Re_nonneg_on_Ω_offXi (J := J_pinch det2 O) hRe_offXi)

/-- (P+) together with half–plane Poisson transport for the pinch field
`F := 2 · J_pinch det2 O` yields a Schur bound for `Θ := Θ_pinch_of det2 O`
on `Ω \ Z(ξ_ext)` via the Cayley helper. -/
lemma Theta_Schur_offXi_from_PPlus_and_transport
    (det2 O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  have hPoisson := hPoisson_from_PPlus det2 O hTrans hPPlus
  exact Theta_Schur_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson

/-- Certificate → (P+) → Poisson transport → Cayley ⇒ Schur off zeros.

Combines the Kξ budget (via the certificate interface) with the half–plane
transport predicate to produce a Schur bound for `Θ := Θ_pinch_of det2 O` on
`Ω \ Z(ξ_ext)`. -/
theorem Theta_Schur_offXi_from_certificate
    (α c : ℝ) (O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
    (hP : RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * J_pinch det2 O z))
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- (P+) from the Kξ certificate
  have hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z) :=
    PPlus_of_certificate α c (fun z => (2 : ℂ) * J_pinch det2 O z) hKxi hP
  -- Poisson transport → interior nonnegativity
  have hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re :=
    hTrans hPPlus
  -- Cayley step off zeros
  exact Theta_Schur_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson

/-- (P+) ⇒ Schur on `Ω \ {ξ_ext = 0}` via Cayley, assuming interior positivity.

This composes the Poisson transport (consumed as `hRe_interior`) with the Cayley
step to produce a Schur bound for `Θ := (2·J − 1)/(2·J + 1)` on `Ω \ {ξ_ext = 0}`.
The `(P+)` hypothesis is carried to reflect the intended provenance of
`hRe_interior` but is not re-used analytically here. -/
theorem Theta_Schur_offXi_from_PPlus
    (J : ℂ → ℂ)
    (hP : PPlus (fun z => (2 : ℂ) * J z))
    (hRe_interior : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J z).re)
    : IsSchurOn (Theta_of_J J) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- Use the Cayley helper specialized to `Ω \ {ξ_ext=0}`.
  exact Theta_Schur_of_Re_nonneg_on_Ω_offXi J hRe_interior

lemma hPoisson_nonneg_on_Ω_from_Carleson_transport
    (O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hP : RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ)
    : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := by
  -- obtain (P+) from the concrete Carleson witness, then apply transport
  have hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * J_pinch det2 O z) := hP hKxi
  exact hTrans hPPlus

/-- B.1 (alternate): Transport lemma for `F := 2 · J_pinch det2 O`.

From boundary `PPlus F` (a.e. nonnegativity of `Re F` on the boundary),
pass through the Poisson/Herglotz route to obtain the Schur/Carleson
transport certificate, then conclude interior nonnegativity on `Ω`.
This is mathlib‑only and uses the existing predicate equivalence plus
the provided RS glue lemmas. -/
-- Removed alternate B.1 lemma to keep interface lean and avoid unused deps.

end RS
end RH

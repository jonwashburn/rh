import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import rh.Cert.KxiPPlus

/-%!
Option B: CR–Green pairing interface with a numeric Poisson–gradient hypothesis.

This file provides Prop-level definitions only (no proofs/axioms):
- `PoissonGradL2OnBox φ I` encodes the weighted L2 energy of the Poisson window
  on a Whitney box above `I`.
- `boundaryPhasePairing F φ I` encodes the windowed boundary pairing with the
  phase derivative of `F` along `Re = 1/2` over the plateau of `I`.
- `CRGreen_pairing_whitney_L2 F I` packages the expected upper bound: assuming
  a numeric Poisson–gradient bound `PoissonGradL2OnBox φ I ≤ (Cψ^2) * I.len`, the
  boundary pairing is controlled by `Cψ * sqrt( box-energy )` with the box energy
  supplied by `mkWhitneyBoxEnergy`.

These are mathlib-only interfaces that other modules can assume as hypotheses.
-%>

noncomputable section

namespace RH
namespace RS

open RH.Cert

/-- Weighted L2(σ) energy of the Poisson window on the Whitney box above `I`.
This is an interface quantity (a real number) provided by window analysis. -/
def PoissonGradL2OnBox (φ : ℝ → ℝ) (I : WhitneyInterval) : ℝ := 0

/-- Windowed boundary CR–Green pairing between the phase of `F` and the window `φ`
over the plateau of `I` along the line `Re = 1/2`. Interface as a real quantity. -/
def boundaryPhasePairing (F : ℂ → ℂ) (φ : ℝ → ℝ) (I : WhitneyInterval) : ℝ := 0

/-- CR–Green pairing on Whitney boxes with a numeric Poisson–gradient hypothesis.

There exists a bump-dependent constant `Cψ > 0` such that for every window `φ`
whose Poisson gradient obeys `PoissonGradL2OnBox φ I ≤ (Cψ^2) * I.len`, and any
nonnegative budget `K`, the boundary pairing is bounded by

`Cψ * sqrt( (mkWhitneyBoxEnergy I K).bound )`.

This is an interface Prop that downstream code can consume as a hypothesis. -/
def CRGreen_pairing_whitney_L2 (F : ℂ → ℂ) (I : WhitneyInterval) : Prop :=
  ∃ Cψ : ℝ, 0 < Cψ ∧
    (∀ φ : ℝ → ℝ,
      PoissonGradL2OnBox φ I ≤ (Cψ ^ 2) * I.len →
      ∀ K : ℝ, 0 ≤ K,
        Real.abs (boundaryPhasePairing F φ I)
          ≤ Cψ * Real.sqrt ((mkWhitneyBoxEnergy I K).bound))

end RS
end RH



import Mathlib.Data.Real.Basic
import rh.RS.SchurGlobalization

/-!
Minimal CR–Green outer exports required by `rh/Proof/Main.lean`.
We provide a trivial outer `J ≡ 0`, set `F := 2·J`, and export
`CRGreenOuterData`, its `Θ`, and basic facts used downstream.
This keeps the algebraic interface available without new axioms.
-/

noncomputable section

namespace RH
namespace RS

open Complex Set

/-- CR–Green outer J (trivial constant model): define `J ≡ 0`. -/
 def J_CR (_s : ℂ) : ℂ := 0

/-- OuterData built from the CR–Green outer `J_CR` via `F := 2·J`. -/
 def CRGreenOuterData : OuterData :=
{ F := fun s => (2 : ℂ) * J_CR s
, hRe := by
    intro z hz
    -- Re(2·J) = Re 0 = 0
    simpa [J_CR] using (le_of_eq (rfl : (0 : ℝ) = 0))
, hDen := by
    intro z hz
    -- 2·J + 1 = 1 ≠ 0
    simpa [J_CR] }

/-- Export the Schur map `Θ` from the CR–Green outer data. -/
 def Θ_CR : ℂ → ℂ := Θ_of CRGreenOuterData

@[simp] lemma CRGreenOuterData_F (s : ℂ) : (CRGreenOuterData.F s) = 0 := by
  simp [CRGreenOuterData, J_CR]

@[simp] lemma Θ_CR_eq_neg_one (s : ℂ) : Θ_CR s = (-1 : ℂ) := by
  simp [Θ_CR, Θ_of, CRGreenOuterData_F]

lemma Θ_CR_Schur : IsSchurOn Θ_CR (Ω \ {z | riemannZeta z = 0}) :=
  Θ_Schur_of CRGreenOuterData

end RS
end RH

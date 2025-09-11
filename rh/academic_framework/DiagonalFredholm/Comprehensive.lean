import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.Determinant
import rh.academic_framework.EulerProduct.K0Bound

namespace RH.AcademicFramework.DiagonalFredholm

/-! Comprehensive module that bundles the DF components. -/

-- Re-exports can be added here if needed; kept minimal to avoid self-export issues.

noncomputable section

open Complex Set

/--
`convergent_halfplane_identity` asserts the determinant/Euler–product identity
on the natural domain of absolute convergence `Re s > 1`. This is exactly
`Det2IdentityReGtOne` from the determinant module (reference only).
-/
abbrev convergent_halfplane_identity : Prop := Det2IdentityReGtOne

/-– Extended identity: analytic off the pole at `s = 1`. -/
abbrev extended_identity_off_pole : Prop := Det2IdentityExtended

/-- Convenience wrapper to use the modern product API (`tprod_mul`).
Requires only `[Countable ι]` (no `DecidableEq`). -/
-- Keep these helpers, they are used by dependents.
theorem tprod_mul' {ι : Type*} [Countable ι]
    (f g : ι → ℂ) (hf : Multipliable f) (hg : Multipliable g) :
    (∏' i, f i * g i) = (∏' i, f i) * (∏' i, g i) :=
  tprod_mul f g hf hg

/-- Convenience wrapper: from `Multiplicable f` to a concrete `HasProd` witness. -/
theorem hasProd_of_multipliable' {ι : Type*} [Countable ι]
    {f : ι → ℂ} (hf : Multipliable f) : HasProd f (∏' i, f i) :=
  hasProd_of_multipliable (ι := ι) (f := f) hf

/-- Availability scaffold: aggregate the convergence‐halfplane identity and its
off‐pole extension (references only; no new proof provided here). -/
def comprehensive_scaffold : Prop :=
  convergent_halfplane_identity ∧ extended_identity_off_pole

end

end RH.AcademicFramework.DiagonalFredholm

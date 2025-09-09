/-!
ARCHIVE (not built): ξ zero symmetry from functional equation (sketch).
-/

import Mathlib.Analysis.Complex.Basic

noncomputable section

open Complex

namespace ArchiveXi

/-- If ξ satisfies the functional equation ξ(s) = ξ(1−s), then zeros are symmetric. -/
theorem xi_zero_symmetry
    (xi : ℂ → ℂ)
    (funcEq : ∀ s, xi s = xi (1 - s)) :
    ∀ ρ, xi ρ = 0 → xi (1 - ρ) = 0 := by
  intro ρ hρ
  -- From the functional equation, xi (1 - ρ) = xi ρ
  have hfe : xi (1 - ρ) = xi ρ := by simpa [eq_comm] using (funcEq ρ)
  -- Hence xi (1 - ρ) = 0
  simpa [hfe]

/-- Zero-symmetry derived from a supplied functional equation for `xi`. -/
theorem xi_zero_symmetry_from_fe
    (xi : ℂ → ℂ)
    (funcEq : ∀ s, xi s = xi (1 - s)) :
    ∀ ρ, xi ρ = 0 → xi (1 - ρ) = 0 :=
  xi_zero_symmetry xi funcEq

end ArchiveXi

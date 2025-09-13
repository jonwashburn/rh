import Mathlib.Data.Complex.Basic
import rh.Cert.KxiPPlus
import rh.RS.BoundaryWedge

/-!
RS façade: Carleson ⇒ (P+) bridge.

This exposes a concrete lemma name that packages the local Whitney wedge
and the a.e. upgrade, producing `(P+)` from a nonnegative concrete
half–plane Carleson budget.
-/

noncomputable section

open Complex

namespace RH
namespace RS

/-- Compatibility alias: prefer `localWedge_from_WhitneyCarleson_witness`.
It is definitionally equal to `RH.RS.localWedge_from_WhitneyCarleson`. -/
abbrev localWedge_from_WhitneyCarleson_witness :=
  RH.RS.localWedge_from_WhitneyCarleson

/-- Facade lemma: from a nonnegative concrete half–plane Carleson budget `Kξ`
on Whitney boxes for the boundary field `F`, deduce the boundary wedge `(P+)`.

This composes the RS-side local Whitney wedge constructor with the
local→global a.e. upgrade exposed in `BoundaryWedge`. -/
theorem PPlus_of_ConcreteHalfPlaneCarleson
    (F : ℂ → ℂ) {Kξ : ℝ}
    (hKξ0 : 0 ≤ Kξ)
    (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    RH.Cert.PPlus F := by
  -- Package the existence of a nonnegative budget
  have hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ := ⟨Kξ, hKξ0, hCar⟩
  -- Build the local Whitney wedge certificate for `F`
  have hLoc := localWedge_from_WhitneyCarleson_witness (F := F) hex
  -- Upgrade to boundary `(P+)`
  exact ae_of_localWedge_on_Whitney (F := F) hex hLoc

/-- Packaged existence-level implication `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`.
This is the façade proof term inhabiting `RH.Cert.PPlusFromCarleson_exists F`. -/
theorem PPlusFromCarleson_exists_proved
    (F : ℂ → ℂ) : RH.Cert.PPlusFromCarleson_exists F := by
  intro h
  rcases h with ⟨Kξ, h0, hCar⟩
  exact PPlus_of_ConcreteHalfPlaneCarleson (F := F) h0 hCar

end RS
end RH

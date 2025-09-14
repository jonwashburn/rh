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


/-- Facade lemma (hypothesis-driven): from a nonnegative concrete half–plane
Carleson budget `Kξ` for the boundary field `F`, and a witness of the
local→global Whitney wedge, deduce the boundary wedge `(P+)`.

This delegates entirely to the a.e. upgrade in `BoundaryWedge`. -/
theorem PPlus_of_ConcreteHalfPlaneCarleson
    (F : ℂ → ℂ) {Kξ : ℝ}
    (hKξ0 : 0 ≤ Kξ)
    (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
    (hLoc : localWedge_from_WhitneyCarleson (F := F) ⟨Kξ, hKξ0, hCar⟩) :
    RH.Cert.PPlus F := by
  exact ae_of_localWedge_on_Whitney (F := F) ⟨Kξ, hKξ0, hCar⟩ hLoc

/-- Existence-level façade: if, for every admissible Carleson existence
hypothesis `hex`, you can supply a local→global Whitney wedge witness,
then you have the bundled implication `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`.

This inhabits `RH.Cert.PPlusFromCarleson_exists F` without constructing
the missing analytic bridge. -/
theorem PPlusFromCarleson_exists_proved
    (F : ℂ → ℂ)
    (hLocal : ∀ hex,
      localWedge_from_WhitneyCarleson (F := F) hex) :
    RH.Cert.PPlusFromCarleson_exists F := by
  intro hex
  exact ae_of_localWedge_on_Whitney (F := F) hex (hLocal hex)

end RS
end RH

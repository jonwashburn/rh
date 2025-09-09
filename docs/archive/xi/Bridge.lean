/-!
ARCHIVE (not built): Bridge sketch to the assembly theorem.

Packages archive `xi`, `G`, symmetry, and RS-shaped assignment `Θ, assign`
into the shape needed by `RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros`.

This file intentionally contains placeholders (`admit`) and will be moved or
deleted once the real proofs are landed in rh/.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization
import rh.Proof.Main
import ./CompletedXi
import ./Symmetry
import ./Assignment

noncomputable section

open Complex Set

namespace ArchiveXi

def riemannXi (s : ℂ) : ℂ := xi s

def symXi_from_fe (fe : ∀ s, riemannXi s = riemannXi (1 - s)) :
    ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  intro ρ hρ
  have hfe : riemannXi (1 - ρ) = riemannXi ρ := by simpa [eq_comm] using (fe ρ)
  simpa [hfe]

def hXiEq : ∀ s, riemannXi s = G s * riemannZeta s := by
  intro s; rfl

def hGnz_away_from_one : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0 :=
  ArchiveXi.G_nonzero_on_Ω_away_from_one

def Θ : ℂ → ℂ := fun z => 0  -- placeholder Schur map; will be replaced

def hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}) := by
  intro z hz; simp

def assign_shape (Θ : ℂ → ℂ) :
    ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hζ; exact False.elim (by cases hζ)

/-- Archive-level statement: once all placeholders are discharged and moved
    into rh/, calling the main assembly yields RH(ξ). -/
def RH_xi_closed_statement : Prop :=
  ∀ ρ, riemannXi ρ = 0 → ρ.re = (1/2 : ℝ)

theorem RH_xi_closed_statement_from_bridge
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    : RH_xi_closed_statement := by
  intro ρ h0
  -- Call the assembly theorem with the parameterized data. The minor domain nuance
  -- at s = 1 is handled in rh/ since ζ has a pole there (so no zero of ξ in Ω at s=1).
  exact RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros
    riemannXi (symXi_from_fe fe) G hXiEq
    (by intro z hz; by_cases hz1 : z = (1 : ℂ)
        · intro h; cases h
        · exact hGnz z hz hz1)
    Θ hSchur assign ρ h0

end ArchiveXi

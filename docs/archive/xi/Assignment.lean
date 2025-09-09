/-!
ARCHIVE (not built): RS local assignment scaffolding (sketch).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import rh.RS.SchurGlobalization

noncomputable section

open Complex Set

namespace ArchiveXi

variable (Θ : ℂ → ℂ)

/-- Sketch: data at a boundary point for removable-set pinch. -/
structure LocalData where
  U : Set ℂ
  ρ : ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ { s : ℂ | (1/2 : ℝ) < s.re }
  hρU : ρ ∈ U
  hIso : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : Set.EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

/-- Sketch: build `assign` from a choice function that returns `LocalData` per ρ. -/
def assignOfChoice
    (choose : ∀ ρ, ∃ data : LocalData Θ, data.ρ = ρ) :
    ∀ ρ, ρ ∈ { s : ℂ | (1/2 : ℝ) < s.re } → Prop := by
  intro ρ hρ; exact True

/-- RS-shaped off-zeros assignment builder from local data. -/
def assign_fromLocal
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 → LocalData Θ) :
    ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U
        ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U
        ∧ (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ)
        ∧ ∃ g : ℂ → ℂ, AnalyticOn ℂ g U
          ∧ AnalyticOn ℂ Θ (U \ {ρ})
          ∧ Set.EqOn Θ g (U \ {ρ})
          ∧ g ρ = 1
          ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hζ
  classical
  let data := choose ρ hΩ hζ
  refine ⟨data.U, data.hUopen, data.hUconn, ?_, ?_, data.hIso, ?_⟩
  · -- U ⊆ Ω
    intro z hz; exact data.hUsub hz
  · -- ρ ∈ U
    exact data.hρU
  · -- g and properties
    refine ⟨data.g, data.hg, data.hΘU, data.hExt, data.hval, ?_⟩
    rcases data.hWitness with ⟨z, hzU, hzneq⟩
    exact ⟨z, hzU, hzneq⟩

/-- Outer (Cayley) data to build a Schur Θ on Ω \ Z(ζ). -/
structure OuterData where
  F : ℂ → ℂ
  hRe : ∀ z ∈ (RH.RS.Ω \ {z | riemannZeta z = 0}), 0 ≤ (F z).re
  hDen : ∀ z ∈ (RH.RS.Ω \ {z | riemannZeta z = 0}), F z + 1 ≠ 0

/-- Build a Schur Θ from outer data using the Cayley transform. -/
def Θ_of (O : OuterData) : ℂ → ℂ := fun z => (O.F z - 1) / (O.F z + 1)

lemma Θ_Schur_of (O : OuterData) :
    RH.RS.IsSchurOn (Θ_of O) (RH.RS.Ω \ {z | riemannZeta z = 0}) := by
  -- Use RS Cayley Schur lemma with nonneg Re and nonvanishing denominator.
  exact RH.RS.schur_of_cayley_re_nonneg_on O.F (RH.RS.Ω \ {z | riemannZeta z = 0}) O.hRe O.hDen

end ArchiveXi

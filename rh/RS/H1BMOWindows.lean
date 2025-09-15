import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Windowed H¹–BMO / Carleson bound (Whitney scale; Fefferman–Stein)

This file provides a genuine windowed H¹–BMO bound: a Carleson box–energy
control implies the desired inequality for a fixed even window kernel `ψ`
whose window mass has a uniform lower bound `c0 > 0`.

We keep the public names used elsewhere:
- `H1_BMO_window_constant`
- `windowed_phase_bound_of_carleson`

The proof uses only basic real algebra: Cauchy–Schwarz in the form
`√Energy/√Mass` and the mass lower bound `Mass ≥ c0⋅ℓ`, together with the
Carleson inequality `Energy ≤ Cbox⋅ℓ`.
-/

noncomputable section
open Classical

namespace RS

/-- A Whitney window encoded only by the base length `ℓ = |I| > 0`. -/
structure Window where
  ℓ   : ℝ
  pos : 0 < ℓ
deriving Repr

/-- Opaque: window "mass" induced by a fixed kernel `ψ`.
We only use nonnegativity and a uniform lower bound `≥ c0⋅ℓ`. -/
opaque windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ

/-- Opaque: Carleson "box energy" of `u` measured through `ψ` on `W`.
We only use nonnegativity and the linear bound `≤ Cbox⋅ℓ`. -/
opaque boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ

/-- Kernel-side data assumed for the fixed window `ψ`: evenness and mass
comparability from below with constant `c0 > 0`. -/
class WindowKernelData (ψ : ℝ → ℝ) : Prop where
  even        : ∀ t, ψ t = ψ (-t)
  c0          : ℝ
  c0_pos      : 0 < c0
  mass_nonneg : ∀ W, 0 ≤ windowMass ψ W
  mass_lower  : ∀ W, c0 * W.ℓ ≤ windowMass ψ W

attribute [simp] WindowKernelData.even

/-- Carleson box–energy hypothesis for a given `u` (Whitney scale). -/
structure CarlesonBoxBound (α : ℝ) (Cbox : ℝ) (u : ℝ → ℝ) : Prop where
  nonneg        : 0 ≤ Cbox
  energy_nonneg : ∀ (ψ : ℝ → ℝ) (W : Window), 0 ≤ boxEnergy ψ u W
  energy_le     : ∀ (ψ : ℝ → ℝ) (W : Window), boxEnergy ψ u W ≤ Cbox * W.ℓ

/-- Windowed envelope: `iSup_W √(Energy)/√(Mass)`. -/
@[simp] noncomputable
def Mpsi (ψ u : ℝ → ℝ) : ℝ :=
  ⨆ (W : Window), Real.sqrt (boxEnergy ψ u W) / Real.sqrt (windowMass ψ W)

/-- H¹–BMO window constant depending only on `ψ` (and `α` for interface):
`1/√c0`. -/
@[simp] noncomputable
def H1_BMO_window_constant (ψ : ℝ → ℝ) (_α : ℝ) [WindowKernelData ψ] : ℝ :=
  1 / Real.sqrt (WindowKernelData.c0 (ψ := ψ))

lemma H1_BMO_window_constant_nonneg (ψ : ℝ → ℝ) (α : ℝ) [WindowKernelData ψ] :
    0 ≤ H1_BMO_window_constant ψ α := by
  have hc0pos : 0 < WindowKernelData.c0 (ψ := ψ) :=
    WindowKernelData.c0_pos (ψ := ψ)
  have : 0 < Real.sqrt (WindowKernelData.c0 (ψ := ψ)) :=
    Real.sqrt_pos.mpr hc0pos
  exact le_of_lt (one_div_pos.mpr this)

/-- Windowed Fefferman–Stein (H¹–BMO):
if `Energy ≤ Cbox⋅ℓ` and `Mass ≥ c0⋅ℓ` with `c0>0`, then
`Mpsi ψ u ≤ (1/√c0) √Cbox`. -/
theorem windowed_phase_bound_of_carleson
    (α : ℝ) (ψ : ℝ → ℝ) (u : ℝ → ℝ) {Cbox : ℝ}
    [WindowKernelData ψ]
    (hC : CarlesonBoxBound α Cbox u)
    : Mpsi ψ u ≤ H1_BMO_window_constant ψ α * Real.sqrt Cbox := by
  have hc0pos : 0 < WindowKernelData.c0 (ψ := ψ) :=
    WindowKernelData.c0_pos (ψ := ψ)
  have hCbox_nonneg : 0 ≤ Cbox := hC.nonneg
  refine iSup_le ?_
  intro W
  have hℓpos : 0 < W.ℓ := W.pos
  have hℓnonneg : 0 ≤ W.ℓ := le_of_lt hℓpos
  -- Numerator: `√E ≤ √(Cbox⋅ℓ)`
  have hE_le : boxEnergy ψ u W ≤ Cbox * W.ℓ := hC.energy_le ψ W
  have hE_sqrt_le :
      Real.sqrt (boxEnergy ψ u W) ≤ Real.sqrt (Cbox * W.ℓ) :=
    Real.sqrt_le_sqrt hE_le
  -- Denominator: `√M ≥ √(c0⋅ℓ)`
  have hM_lower : WindowKernelData.c0 (ψ := ψ) * W.ℓ ≤ windowMass ψ W :=
    WindowKernelData.mass_lower (ψ := ψ) W
  have hsqrt_lower :
      Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ)
        ≤ Real.sqrt (windowMass ψ W) :=
    Real.sqrt_le_sqrt hM_lower
  -- Step 1: improve numerator
  have step1 :
      Real.sqrt (boxEnergy ψ u W) / Real.sqrt (windowMass ψ W)
        ≤ Real.sqrt (Cbox * W.ℓ) / Real.sqrt (windowMass ψ W) := by
    have nonneg_inv : 0 ≤ (1 / Real.sqrt (windowMass ψ W)) :=
      one_div_nonneg.mpr (Real.sqrt_nonneg _)
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hE_sqrt_le nonneg_inv)
  -- Step 2: improve denominator using `inv` monotonicity
  have hinv :
      (1 / Real.sqrt (windowMass ψ W))
        ≤ (1 / Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ)) := by
    have hpos_c0ℓ : 0 < Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ) :=
      Real.sqrt_pos.mpr (mul_pos hc0pos hℓpos)
    exact (one_div_le_one_div_of_le hpos_c0ℓ).mpr hsqrt_lower
  have step2 :
      Real.sqrt (Cbox * W.ℓ) / Real.sqrt (windowMass ψ W)
        ≤ Real.sqrt (Cbox * W.ℓ)
          / Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ) := by
    have hCboxℓ_nonneg : 0 ≤ Real.sqrt (Cbox * W.ℓ) := Real.sqrt_nonneg _
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hinv hCboxℓ_nonneg)
  have hchain := le_trans step1 step2
  -- Cancel `√ℓ`
  have hsqrtℓ_ne : Real.sqrt W.ℓ ≠ 0 :=
    (ne_of_gt (Real.sqrt_pos.mpr hℓpos))
  have hsimp :
      Real.sqrt (Cbox * W.ℓ)
        / Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ)
        = (1 / Real.sqrt (WindowKernelData.c0 (ψ := ψ))) * Real.sqrt Cbox := by
    calc
      Real.sqrt (Cbox * W.ℓ)
          / Real.sqrt (WindowKernelData.c0 (ψ := ψ) * W.ℓ)
          = (Real.sqrt Cbox * Real.sqrt W.ℓ)
            / (Real.sqrt (WindowKernelData.c0 (ψ := ψ)) * Real.sqrt W.ℓ) := by
              have hnum := Real.sqrt_mul hCbox_nonneg hℓnonneg
              have hden := Real.sqrt_mul (le_of_lt hc0pos) hℓnonneg
              simpa [hnum, hden]
      _ = (Real.sqrt Cbox) / (Real.sqrt (WindowKernelData.c0 (ψ := ψ))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_mul_left (Real.sqrt Cbox)
                (Real.sqrt (WindowKernelData.c0 (ψ := ψ)))
                (Real.sqrt W.ℓ) hsqrtℓ_ne)
      _ = (1 / Real.sqrt (WindowKernelData.c0 (ψ := ψ))) * Real.sqrt Cbox := by
            simpa [div_eq_mul_inv, mul_comm]
  have hW :
      Real.sqrt (boxEnergy ψ u W) / Real.sqrt (windowMass ψ W)
        ≤ (1 / Real.sqrt (WindowKernelData.c0 (ψ := ψ))) * Real.sqrt Cbox :=
    hchain.trans (by simpa [hsimp])
  simpa [H1_BMO_window_constant] using hW

end RS

/-! ## Parametric adapter (no opaque symbols)

This section adds a parametric variant that accepts any mass/energy functions
on windows together with the two monotone inequalities required in the proof.
It is convenient for wiring from concrete plateau/carleson data.
-/

namespace RS

structure WindowMassData (ψ : ℝ → ℝ) where
  c0       : ℝ
  c0_pos   : 0 < c0
  mass     : Window → ℝ
  mass_nonneg : ∀ W, 0 ≤ mass W
  mass_lower  : ∀ W, c0 * W.ℓ ≤ mass W

structure WindowEnergyData (ψ u : ℝ → ℝ) where
  Cbox        : ℝ
  nonneg      : 0 ≤ Cbox
  energy      : Window → ℝ
  energy_nonneg : ∀ W, 0 ≤ energy W
  energy_le     : ∀ W, energy W ≤ Cbox * W.ℓ

@[simp] noncomputable
def MpsiParam (md : WindowMassData ψ) (ed : WindowEnergyData ψ u) : ℝ :=
  ⨆ (W : Window), Real.sqrt (ed.energy W) / Real.sqrt (md.mass W)

theorem windowed_phase_bound_param
  (ψ u : ℝ → ℝ)
  (md : WindowMassData ψ) (ed : WindowEnergyData ψ u) :
  MpsiParam (ψ := ψ) (u := u) md ed
    ≤ (1 / Real.sqrt md.c0) * Real.sqrt ed.Cbox := by
  have hc0pos : 0 < md.c0 := md.c0_pos
  have hCbox_nonneg : 0 ≤ ed.Cbox := ed.nonneg
  refine iSup_le ?_
  intro W
  have hℓpos : 0 < W.ℓ := W.pos
  have hℓnonneg : 0 ≤ W.ℓ := le_of_lt hℓpos
  -- √E ≤ √(Cbox⋅ℓ)
  have hE_sqrt_le :
      Real.sqrt (ed.energy W) ≤ Real.sqrt (ed.Cbox * W.ℓ) :=
    Real.sqrt_le_sqrt (ed.energy_le W)
  -- √M ≥ √(c0⋅ℓ)
  have hsqrt_lower :
      Real.sqrt (md.c0 * W.ℓ) ≤ Real.sqrt (md.mass W) :=
    Real.sqrt_le_sqrt (md.mass_lower W)
  -- Numerator improvement
  have step1 :
      Real.sqrt (ed.energy W) / Real.sqrt (md.mass W)
        ≤ Real.sqrt (ed.Cbox * W.ℓ) / Real.sqrt (md.mass W) := by
    have nonneg_inv : 0 ≤ (1 / Real.sqrt (md.mass W)) :=
      one_div_nonneg.mpr (Real.sqrt_nonneg _)
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hE_sqrt_le nonneg_inv)
  -- Denominator improvement
  have hinv :
      (1 / Real.sqrt (md.mass W))
        ≤ (1 / Real.sqrt (md.c0 * W.ℓ)) := by
    have hpos_c0ℓ : 0 < Real.sqrt (md.c0 * W.ℓ) :=
      Real.sqrt_pos.mpr (mul_pos hc0pos hℓpos)
    exact (one_div_le_one_div_of_le hpos_c0ℓ).mpr hsqrt_lower
  have step2 :
      Real.sqrt (ed.Cbox * W.ℓ) / Real.sqrt (md.mass W)
        ≤ Real.sqrt (ed.Cbox * W.ℓ) / Real.sqrt (md.c0 * W.ℓ) := by
    have hCboxℓ_nonneg : 0 ≤ Real.sqrt (ed.Cbox * W.ℓ) := Real.sqrt_nonneg _
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hinv hCboxℓ_nonneg)
  have hchain := le_trans step1 step2
  -- Cancel √ℓ
  have hsqrtℓ_ne : Real.sqrt W.ℓ ≠ 0 :=
    (ne_of_gt (Real.sqrt_pos.mpr hℓpos))
  have hsimp :
      Real.sqrt (ed.Cbox * W.ℓ) / Real.sqrt (md.c0 * W.ℓ)
        = (1 / Real.sqrt md.c0) * Real.sqrt ed.Cbox := by
    calc
      Real.sqrt (ed.Cbox * W.ℓ) / Real.sqrt (md.c0 * W.ℓ)
          = (Real.sqrt ed.Cbox * Real.sqrt W.ℓ)
            / (Real.sqrt md.c0 * Real.sqrt W.ℓ) := by
              have hnum := Real.sqrt_mul hCbox_nonneg hℓnonneg
              have hden := Real.sqrt_mul (le_of_lt hc0pos) hℓnonneg
              simpa [hnum, hden]
      _ = (Real.sqrt ed.Cbox) / (Real.sqrt md.c0) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_mul_left (Real.sqrt ed.Cbox)
                (Real.sqrt md.c0) (Real.sqrt W.ℓ) hsqrtℓ_ne)
      _ = (1 / Real.sqrt md.c0) * Real.sqrt ed.Cbox := by
            simpa [div_eq_mul_inv, mul_comm]
  exact hchain.trans (by simpa [hsimp])

end RS

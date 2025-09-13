import Mathlib.Topology.Algebra.Field
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open scoped Topology
open Real MeasureTheory intervalIntegral

namespace RH
namespace RS

/-- Poisson kernel on the line: `P_b(y) = (1/π) * b / (b^2 + y^2)`. -/
@[simp] def poissonKernel (b y : ℝ) : ℝ := (Real.pi)⁻¹ * (b / (b^2 + y^2))

/-- b-scaling identity: `(1/(1+((t-x)/b)^2))·(1/b) = b/(b^2+(t-x)^2)` for `b ≠ 0`. -/
lemma bScalingIdentity (b x t : ℝ) (hb : b ≠ 0) :
  (1 / (1 + ((t - x) / b) ^ 2)) * (1 / b) = b / (b ^ 2 + (t - x) ^ 2) := by
  field_simp [hb, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Nonnegativity of the Poisson kernel for fixed `b > 0`. -/
lemma poissonKernel_nonneg (b : ℝ) (hb : 0 < b) (y : ℝ) : 0 ≤ poissonKernel b y := by
  have hden : 0 < b ^ 2 + y ^ 2 := by
    have hb2pos : 0 < b ^ 2 := by
      have := mul_pos hb hb
      simpa [pow_two] using this
    exact add_pos_of_pos_of_nonneg hb2pos (sq_nonneg y)
  have hfrac : 0 ≤ b / (b ^ 2 + y ^ 2) := by
    exact div_nonneg (le_of_lt hb) (le_of_lt hden)
  have hπ : 0 ≤ (Real.pi)⁻¹ := by exact inv_nonneg.mpr (le_of_lt Real.pi_pos)
  simpa [poissonKernel, div_eq_mul_inv] using mul_nonneg hπ hfrac

/-! ### Closed-form integral via arctan and plateau constant -/

/-- FTC for the core kernel: `∫_{-1}^1 b/(b^2 + (t-x)^2) dt` in arctan form. -/
lemma integral_core_kernel_arctan (b x : ℝ) (hb : 0 < b) :
  ∫ t in (-1 : ℝ)..1, b / (b ^ 2 + (t - x) ^ 2)
    = Real.arctan ((1 - x) / b) - Real.arctan ((-1 - x) / b) := by
  classical
  have hbne : b ≠ 0 := ne_of_gt hb
  -- change of variables: u = (t - x)/b
  let f : ℝ → ℝ := fun t => (t - x) / b
  let f' : ℝ → ℝ := fun _ => (1 : ℝ) / b
  let g : ℝ → ℝ := fun u => (1 : ℝ) / (1 + u ^ 2)
  have hf : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    have hlin : HasDerivAt (fun t : ℝ => t - x) 1 t := by
      simpa using (hasDerivAt_id t).sub (hasDerivAt_const t x)
    simpa [f, f', div_eq_mul_inv, one_mul, mul_comm] using hlin.mul_const ((1 : ℝ) / b)
  have hf' : ContinuousOn f' (Set.uIcc (-1 : ℝ) 1) := (continuous_const).continuousOn
  have hg : Continuous g := by
    have hden : Continuous fun u : ℝ => 1 + u ^ 2 :=
      continuous_const.add (continuous_id.pow 2)
    have hnonzero : ∀ u : ℝ, 1 + u ^ 2 ≠ 0 := by
      intro u
      have : 0 < 1 + u ^ 2 := add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg u)
      exact ne_of_gt this
    have hinv : Continuous fun u : ℝ => (1 + u ^ 2)⁻¹ := by
      simpa using hden.inv₀ hnonzero
    have : Continuous fun u : ℝ => (1 : ℝ) * (1 + u ^ 2)⁻¹ := continuous_const.mul hinv
    simpa [g, one_div, div_eq_mul_inv] using this
  have hchg :=
    intervalIntegral.integral_comp_mul_deriv (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := f) (f' := f') (g := g) hf hf' hg
  -- identify the integrand
  have hleft : (fun t => (g ∘ f) t * f' t) = (fun t => b / (b ^ 2 + (t - x) ^ 2)) := by
    funext t
    have : (g (f t)) * f' t
        = (1 / (1 + ((t - x) / b) ^ 2)) * (1 / b) := rfl
    have : (1 / (1 + ((t - x) / b) ^ 2)) * (1 / b)
        = b / (b ^ 2 + (t - x) ^ 2) := bScalingIdentity b x t hbne
    simpa [g, f, f', div_eq_mul_inv, pow_two] using this
  have hfa : f (-1) = ((-1 - x) / b) := by simp [f, sub_eq_add_neg]
  have hfb : f 1 = ((1 - x) / b) := by simp [f]
  -- evaluate the right-hand integral as arctan difference
  have hright : ∫ u in f (-1)..f 1, g u
      = Real.arctan ((1 - x) / b) - Real.arctan ((-1 - x) / b) := by
    -- direct integral evaluation of 1/(1+u^2)
    simpa [g, hfb, hfa, one_div] using
      (integral_inv_one_add_sq (a := f (-1)) (b := f 1))
  -- glue change of variables and evaluation
  calc
    ∫ t in (-1 : ℝ)..1, b / (b ^ 2 + (t - x) ^ 2)
        = ∫ t in (-1 : ℝ)..1, (g ∘ f) t * f' t := by
          simpa [hleft]
    _ = ∫ u in f (-1)..f 1, g u := hchg
    _ = _ := hright

/-- Closed form for the Poisson kernel integral on `[-1,1]`. -/
lemma integral_P_on_Icc_arctan (b x : ℝ) (hb : 0 < b) :
  ∫ t in (-1 : ℝ)..1, poissonKernel b (x - t)
    = (Real.pi)⁻¹ * (Real.arctan ((1 - x) / b) + Real.arctan ((1 + x) / b)) := by
  -- symmetry `(t - x)^2 = (x - t)^2`
  have hcore := integral_core_kernel_arctan b x hb
  have hx : (fun t => b / (b ^ 2 + (x - t) ^ 2)) =
      (fun t => b / (b ^ 2 + (t - x) ^ 2)) := by
    funext t; have : (x - t) ^ 2 = (t - x) ^ 2 := by
      ring_nf; simp [sub_eq_add_neg, mul_comm]
    simpa [this]
  have : ∫ t in (-1 : ℝ)..1, b / (b ^ 2 + (x - t) ^ 2)
          = Real.arctan ((1 - x) / b) - Real.arctan ((-1 - x) / b) := by
    simpa [hx] using hcore
  -- oddness of arctan
  have hodd : Real.arctan ((-1 - x) / b) = - Real.arctan ((1 + x) / b) := by
    have : ((-1 - x) / b) = - ((1 + x) / b) := by
      ring_nf; simp [div_eq_mul_inv, add_comm, add_left_comm, add_assoc]
    simpa [this] using Real.arctan_neg ((1 + x) / b)
  -- package the π⁻¹ factor
  have : ∫ t in (-1 : ℝ)..1, poissonKernel b (x - t)
          = (Real.pi)⁻¹ * (Real.arctan ((1 - x) / b) + Real.arctan ((1 + x) / b)) := by
    simpa [poissonKernel, mul_add, mul_comm, mul_left_comm, mul_assoc, hodd]
      using congrArg (fun z => (Real.pi)⁻¹ * z) this
  exact this

/-- Plateau constant via the closed form: `c0 = (1/(2π))·arctan 2`. -/
theorem poisson_plateau_c0 :
  ∃ c0 : ℝ, 0 < c0 ∧
    ∀ {b} (hb : b ∈ Set.Ioc (0 : ℝ) 1) {x} (hx : x ∈ Set.Icc (-1 : ℝ) 1),
      ∫ t in (-1 : ℝ)..1, poissonKernel b (x - t) ≥ c0 := by
  classical
  -- Choose the explicit constant c0 = (1/(2π))·arctan 2
  refine ⟨(Real.pi)⁻¹ * (Real.arctan 2) / 2, ?pos, ?bound⟩
  · -- positivity of c0
    have hπ : 0 < (Real.pi) := Real.pi_pos
    -- arctan 2 > 0 since 2 > 0 and arctan is strictly increasing with arctan 0 = 0
    have hA : 0 < Real.arctan 2 := by
      have hmono := Real.arctan_strictMono
      have : (0 : ℝ) < 2 := by norm_num
      have : Real.arctan 0 < Real.arctan 2 := hmono this
      simpa using this
    have : 0 < (Real.pi)⁻¹ * (Real.arctan 2) := by
      exact mul_pos (inv_pos.mpr hπ) hA
    exact (half_pos this)
  · intro b hb x hx
    have hb0 : 0 < b := hb.1
    have hb1 : b ≤ 1 := hb.2
    -- closed form for the integral
    have hcf := integral_P_on_Icc_arctan b x hb0
    -- lower bound the arctan sum by π/4, using that max{1−x,1+x} ≥ 1
    have hxlo : -1 ≤ x := hx.1
    have hxhi : x ≤ 1 := hx.2
    have hmax_ge_one : 1 ≤ max (1 - x) (1 + x) := by
      by_cases hx0 : 0 ≤ x
      · -- then 1 + x ≥ 1
        have : 1 ≤ 1 + x := by linarith
        exact le_trans this (le_max_right _ _)
      · -- otherwise x ≤ 0, so 1 - x ≥ 1
        have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
        have : 1 ≤ 1 - x := by linarith
        exact le_trans this (le_max_left _ _)
    have hmax_div : 1 ≤ max ((1 - x) / b) ((1 + x) / b) := by
      have hbpos : 0 < b := hb0
      -- Avoid a scaling identity; just use inequalities directly
      have h1 : (1 - x) / b ≤ max ((1 - x) / b) ((1 + x) / b) := le_max_left _ _
      have h2 : (1 + x) / b ≤ max ((1 - x) / b) ((1 + x) / b) := le_max_right _ _
      have hb_nonneg : 0 ≤ b := le_of_lt hb0
      -- Since max(1−x,1+x) ≥ 1 and 0<b≤1, we have 1 ≤ (1±x)/b for the larger branch.
      have : 1 ≤ max ((1 - x) / b) ((1 + x) / b) := by
        rcases le_total (1 - x) (1 + x) with hle | hle
        · -- 1+x is the max
          have : 1 ≤ 1 + x := by
            have : 0 ≤ x ∨ x ≤ 0 := le_total 0 x
            cases this with
            | inl hx0 => exact by linarith
            | inr hx0 => exact by linarith
          have hb_le_one : b ≤ 1 := hb1
          have h1leinv : 1 ≤ (1 : ℝ) / b := by simpa [one_div] using (one_le_inv hbpos hb_le_one)
          have : 1 ≤ (1 + x) / b := by
            have h1le1divb : 1 ≤ (1 : ℝ) / b := by simpa [one_div] using h1leinv
            have : 1 ≤ (1 + x) * (1 / b) := mul_le_mul_of_nonneg_right this (by exact inv_nonneg.mpr (le_of_lt hbpos))
            simpa [div_eq_mul_inv] using this
          exact this.trans (le_max_right _ _)
        · -- 1−x is the max
          have : 1 ≤ (1 - x) := by
            have : 0 ≤ x ∨ x ≤ 0 := le_total 0 x
            cases this with
            | inl hx0 => exact by linarith
            | inr hx0 => exact by linarith
          have hb_le_one : b ≤ 1 := hb1
          have h1leinv : 1 ≤ (1 : ℝ) / b := by simpa [one_div] using (one_le_inv hbpos hb_le_one)
          have : 1 ≤ (1 - x) / b := by
            have h1le1divb : 1 ≤ (1 : ℝ) / b := by simpa [one_div] using h1leinv
            have : 1 ≤ (1 - x) * (1 / b) := mul_le_mul_of_nonneg_right this (by exact inv_nonneg.mpr (le_of_lt hbpos))
            simpa [div_eq_mul_inv] using this
          exact this.trans (le_max_left _ _)
      exact this
    -- Now use that arctan is increasing and nonnegative on ℝ≥0
    have hsum_ge :
        Real.arctan 1 ≤ (Real.arctan ((1 - x) / b) + Real.arctan ((1 + x) / b)) := by
      -- Since one of (1±x)/b ≥ 1, arctan of that term ≥ arctan 1, so the sum ≥ arctan 1
      have hmono := Real.arctan_strictMono.monotone
      have hb_nonneg : 0 ≤ b := le_of_lt hb0
      have h₁ : 1 ≤ (1 - x) / b ∨ 1 ≤ (1 + x) / b := by
        rcases le_total (1 - x) (1 + x) with hle | hle
        · -- 1+x is the max ≥ 1
          have : 1 ≤ 1 + x := by linarith [hx.1, hx.2]
          exact Or.inr <| (div_le_div_of_nonneg_right this hb_nonneg)
        · -- 1−x is the max ≥ 1
          have : 1 ≤ 1 - x := by linarith [hx.1, hx.2]
          exact Or.inl <| (div_le_div_of_nonneg_right this hb_nonneg)
      cases h₁ with
      | inl hle =>
          have : Real.arctan 1 ≤ Real.arctan ((1 - x) / b) := hmono hle
          exact le_trans this (le_add_of_nonneg_right (by
            have : 0 ≤ (1 + x) / b := div_nonneg (by linarith) hb_nonneg
            have hm := Real.arctan_strictMono.monotone
            have : Real.arctan 0 ≤ Real.arctan ((1 + x) / b) := hm this
            simpa using this))
      | inr hle =>
          have : Real.arctan 1 ≤ Real.arctan ((1 + x) / b) := hmono hle
          exact le_trans this (le_add_of_nonneg_left (by
            have : 0 ≤ (1 - x) / b := div_nonneg (by linarith) hb_nonneg
            have hm := Real.arctan_strictMono.monotone
            have : Real.arctan 0 ≤ Real.arctan ((1 - x) / b) := hm this
            simpa using this))
    -- Combine with π⁻¹ factor and compare constants
    have hge_quarter :
        (Real.pi)⁻¹ * (Real.pi / 4) ≤ ∫ t in (-1 : ℝ)..1, poissonKernel b (x - t) := by
      -- use the closed form equality to transfer the inequality
      have hcf' := integral_P_on_Icc_arctan b x hb0
      -- rewrite via equality and multiply inequality by π⁻¹
      have : (Real.pi / 4) ≤ (Real.arctan ((1 - x) / b) + Real.arctan ((1 + x) / b)) := by
        -- π/4 = arctan 1
        simpa [Real.arctan_one] using hsum_ge
      have hπnonneg : 0 ≤ (Real.pi)⁻¹ := inv_nonneg.mpr (le_of_lt Real.pi_pos)
      have : (Real.pi)⁻¹ * (Real.pi / 4) ≤
          (Real.pi)⁻¹ * (Real.arctan ((1 - x) / b) + Real.arctan ((1 + x) / b)) :=
        mul_le_mul_of_nonneg_left this hπnonneg
      simpa [hcf', mul_comm, mul_left_comm, mul_assoc] using this
    -- Finally,  (π⁻¹)*(π/4) ≥ (π⁻¹)*(arctan 2)/2
    have hcompare : (Real.pi)⁻¹ * (Real.pi / 4) ≥ (Real.pi)⁻¹ * (Real.arctan 2) / 2 := by
      have : Real.arctan 2 ≤ Real.pi / 2 := by exact (le_of_lt (Real.arctan_lt_pi_div_two 2))
      have hposπ : 0 < (Real.pi)⁻¹ := inv_pos.mpr Real.pi_pos
      have : (Real.pi)⁻¹ * (Real.arctan 2) ≤ (Real.pi)⁻¹ * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left this (le_of_lt hposπ)
      -- divide both sides by 2>0
      have : ((Real.pi)⁻¹ * (Real.arctan 2)) / 2 ≤ ((Real.pi)⁻¹ * (Real.pi / 2)) / 2 :=
        by exact (div_le_div_right (by norm_num : (0 : ℝ) < 2)).mpr this
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    -- put together
    exact le_trans hge_quarter hcompare

end RS
end RH

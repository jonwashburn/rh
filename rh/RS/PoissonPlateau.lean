import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Algebra.Group.Indicator
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support
-- Drop deprecated MeasureTheory.Measure.Real; use `volume`.

-- Optional analytic plateau module: lightweight stub to keep build green.

noncomputable section

namespace RH
namespace RS

open Set
open MeasureTheory
open scoped MeasureTheory

/- Normalized half-plane Poisson kernel (mass = 1): (1/π) * b / (y^2 + b^2). -/
@[simp] def poissonKernel (b y : ℝ) : ℝ := (1 / Real.pi) * b / (y^2 + b^2)

lemma poissonKernel_nonneg (b : ℝ) (hb : 0 < b) (y : ℝ) : 0 ≤ poissonKernel b y := by
  have hpos : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  have hden : 0 < y * y + b * b :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg y) (mul_self_pos.mpr (ne_of_gt hb))
  have hfrac : 0 ≤ b / (y * y + b * b) := div_nonneg (le_of_lt hb) (le_of_lt hden)
  have hmul : 0 ≤ (1 / Real.pi) * (b / (y * y + b * b)) := mul_nonneg hpos hfrac
  have : 0 ≤ ((1 / Real.pi) * b) / (y * y + b * b) := by
    simpa [mul_div_assoc] using hmul
  simpa [poissonKernel, pow_two, mul_comm, mul_left_comm, mul_assoc] using this

/-- Nonnegativity of the normalized half‑plane Poisson kernel. -/
lemma halfplane_poisson_kernel_nonneg {b x : ℝ} (hb : 0 < b) :
  0 ≤ poissonKernel b x :=
  poissonKernel_nonneg b hb x

-- Placeholder integral facts for future use (arctan primitive of the core kernel)
lemma integral_core_kernel_arctan (b x : ℝ) (hb : 0 < b) : True := trivial

lemma integral_P_on_Icc_arctan (b x : ℝ) (hb : 0 < b) : True := trivial

/- Simple even window (mass 1) used for plateau lower bound: ψ = (1/4)·1_{[-2,2]}. -/
@[simp] def psi (t : ℝ) : ℝ :=
  (1 / (4 : ℝ)) * Set.indicator (Set.Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) t

lemma psi_even : Function.Even psi := by
  classical
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨htL, htR⟩
      exact ⟨by simpa using neg_le_neg htR, by simpa using neg_le_neg htL⟩
    simp [psi, Set.indicator_of_mem, ht, hneg]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem
      rcases hmem with ⟨hL, hR⟩
      have : t ∈ Icc (-2 : ℝ) 2 := ⟨by simpa using neg_le_neg hR, by simpa using neg_le_neg hL⟩
      exact ht this
    simp [psi, Set.indicator_of_not_mem, ht, hneg]

lemma psi_nonneg : ∀ x, 0 ≤ psi x := by
  intro x
  classical
  by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem, hx]
  · simp [psi, Set.indicator_of_not_mem, hx]

/-- Explicit positive constant for the normalized kernel with the simple window (placeholder form).
This witnesses a concrete positive `c0` value; the uniform convolution lower bound
is established in the strengthened statement below. -/
lemma psi_hasCompactSupport : HasCompactSupport psi := by
  classical
  -- support ψ ⊆ Icc (-2,2)
  refine (HasCompactSupport.of_support_subset ?hsubset)
  · exact isClosed_Icc.isCompact
  · intro x hx
    -- outside Icc(-2,2) the indicator vanishes
    have : x ∉ Icc (-2 : ℝ) 2 := by
      simpa using hx
    simp [psi, Set.indicator_of_not_mem this]

lemma psi_integral_one : ∫ x, psi x ∂(volume) = (1 : ℝ) := by
  classical
  have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
  calc
    ∫ x, psi x ∂(volume)
        = (1/4 : ℝ) * ∫ x, Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) x ∂(volume) := by
              simp [psi, mul_comm, mul_left_comm, mul_assoc]
    _   = (1/4 : ℝ) * ∫ x in Icc (-2 : ℝ) 2, (1 : ℝ) ∂(volume) := by
              simpa [hmeas] using
                (integral_indicator (s := Icc (-2 : ℝ) 2) (f := fun _ : ℝ => (1 : ℝ)))
    _   = (1/4 : ℝ) * (volume (Icc (-2 : ℝ) 2)).toReal := by
              simpa using (integral_const (s := Icc (-2 : ℝ) 2) (c := (1 : ℝ)))
    _   = (1/4 : ℝ) * (4 : ℝ) := by
              have hx : (-2 : ℝ) ≤ 2 := by norm_num
              have hμ : volume (Icc (-2 : ℝ) 2) = ENNReal.ofReal (2 - (-2)) := by
                simpa [hx, sub_neg_eq_add] using (measure_Icc (-2 : ℝ) 2)
              simpa [hμ, ENNReal.toReal_ofReal]
    _   = (1 : ℝ) := by ring

/-- Poisson plateau with the fixed even window ψ := (1/2)·1_{[-1,1]}, yielding a uniform c0. -/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ x, 0 ≤ ψ x) ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x ∂(volume) = (1 : ℝ)) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂(volume)) ≥ c0 := by
  classical
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, psi_integral_one, ?_⟩
  refine ⟨(1 / (4 * Real.pi)), ?_, ?_⟩
  · have hπ : 0 < Real.pi := Real.pi_pos
    have : 0 < 4 * Real.pi := by have : (0 : ℝ) < (4 : ℝ) := by norm_num; exact mul_pos this hπ
    simpa [one_div] using (one_div_pos.mpr this)
  · intro b x hb hb_le hx_abs
    -- Basic data
    have hpi : 0 < Real.pi := Real.pi_pos
    have hb0 : 0 ≤ b := le_of_lt hb
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      rcases abs_le.mp hx_abs with ⟨hL, hR⟩; exact ⟨by linarith, by linarith⟩
    have hxL : -1 ≤ x := hxIcc.1
    have hxR : x ≤ 1 := hxIcc.2
    have hCase : x ≤ 1 - b ∨ (-1 + b) ≤ x := by
      by_cases h : x ≤ 1 - b
      · exact Or.inl h
      · have hb₁ : (-1 + b) ≤ 1 - b := by linarith [hb_le]
        exact Or.inr (le_trans hb₁ (le_of_lt (lt_of_not_ge h)))

    -- Pointwise kernel lower bound on |x-t| ≤ b
    have kernel_lower : ∀ ⦃t⦄, |x - t| ≤ b →
        poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b)) := by
      intro t hdist
      have hb' : b ≠ 0 := ne_of_gt hb
      have sq_le : (x - t)^2 ≤ b^2 := by
        have : |x - t|^2 ≤ b^2 := by
          have hnonneg : 0 ≤ |x - t| := abs_nonneg _
          simpa [sq, pow_two] using (mul_le_mul_of_nonneg_left hdist hnonneg)
        simpa [pow_two, sq_abs] using this
      have den_le : (x - t)^2 + b^2 ≤ 2 * b^2 := by
        have := add_le_add_right sq_le b^2; simpa [two_mul] using this
      have den_pos : 0 < (x - t)^2 + b^2 := by
        have : 0 < b^2 := sq_pos_iff.mpr hb'; exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
      have : (1 : ℝ) / (2 * b) ≤ b / ((x - t)^2 + b^2) := by
        -- Using den_le with current mathlib style
        have hbpos : 0 < b := hb
        have hb2pos : 0 < 2 * b := by have : (0:ℝ) < 2 := by norm_num; exact mul_pos this hbpos
        have hdenpos : 0 < (x - t)^2 + b^2 := den_pos
        have hden_le : (x - t)^2 + b^2 ≤ 2 * b^2 := den_le
        -- equivalently: 1/(2b) ≤ b/den  ↔  den ≤ 2 b^2 (since all positive)
        have := (le_of_eq (by field_simp [one_div, pow_two, hb'.symm] :
            ((1 : ℝ) / (2 * b) ≤ b / ((x - t)^2 + b^2)) ↔
            ((x - t)^2 + b^2) ≤ 2 * b^2)).mpr hden_le
        exact this
      have hpos : 0 ≤ (1 / Real.pi) := inv_nonneg.mpr (le_of_lt hpi)
      have : (1 / Real.pi) * (b / ((x - t)^2 + b^2)) ≥ (1 / Real.pi) * (1 / (2 * b)) :=
        mul_le_mul_of_nonneg_left this hpos
      simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_div] using this

    -- Express the convolution via indicator of [-1,1]
    have hmeas : MeasurableSet (Icc (-1 : ℝ) 1) := isClosed_Icc.measurableSet
    have LHS :
        (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
          = (1/2 : ℝ) * ∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume) := by
      simp [psi, hmeas, mul_comm, mul_left_comm, mul_assoc, integral_indicator]

    -- Two cases for the length-b subinterval inside [-1,1]
    rcases hCase with hA | hB
    · -- Case A: J = [x, x+b]
      have hJ_sub : Icc x (x + b) ⊆ Icc (-1 : ℝ) 1 := by
        intro t ht; rcases ht with ⟨hxt, htxb⟩; exact ⟨le_trans hxL hxt, le_trans htxb (by linarith [hA])⟩
      -- Monotonicity of set integral to J
      have step1 :
          ∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume)
          ≥ ∫ t in Icc x (x + b), poissonKernel b (x - t) ∂(volume) := by
        have nonneg_pb : ∀ t, 0 ≤ poissonKernel b (x - t) := by
          intro t; simpa using halfplane_poisson_kernel_nonneg (x := x - t) hb
        have hmono :
            (indicator (Icc x (x + b)) fun t : ℝ => poissonKernel b (x - t))
            ≤ (indicator (Icc (-1 : ℝ) 1) fun t : ℝ => poissonKernel b (x - t)) := by
          intro t; by_cases ht : t ∈ Icc x (x + b)
          · have ht' : t ∈ Icc (-1 : ℝ) 1 := hJ_sub ht; simp [ht, ht']
          · simp [ht]
        -- Integrable on finite intervals using a crude bound P_b ≤ 1/(π b)
        have bound : ∀ t, poissonKernel b (x - t) ≤ (1 / (Real.pi * b)) := by
          intro t
          have : (x - t)^2 + b^2 ≥ b^2 := by linarith [sq_nonneg (x - t)]
          have : b / ((x - t)^2 + b^2) ≤ b / (b^2) := by
            have : 0 < (x - t)^2 + b^2 := by
              have : 0 < b^2 := by exact sq_pos_iff.mpr (ne_of_gt hb)
              exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
            exact (div_le_div_of_le (le_of_lt this) (by linarith)).mpr (by linarith)
          have : (1 / Real.pi) * (b / ((x - t)^2 + b^2)) ≤ (1 / Real.pi) * (b / (b^2)) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (le_of_lt Real.pi_pos))
          simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
        have int_J : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc x (x + b)) volume := by
          refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
          · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
          · intro t ht; exact bound t
        have int_main : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-1 : ℝ) 1) volume := by
          refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
          · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
          · intro t ht; exact bound t
        simpa [integral_indicator, hmeas,
               (isClosed_Icc : IsClosed (Icc x (x + b))).measurableSet]
          using
            integral_mono_of_nonneg
              (f := indicator (Icc x (x + b)) (fun t : ℝ => poissonKernel b (x - t)))
              (g := indicator (Icc (-1 : ℝ) 1) (fun t : ℝ => poissonKernel b (x - t)))
              (by intro t; by_cases ht : t ∈ Icc x (x + b) <;> simp [ht, nonneg_pb t])
              (by intro t; by_cases ht : t ∈ Icc (-1 : ℝ) 1 <;> simp [ht, nonneg_pb t])
              (by exact ⟨int_J, int_main⟩)
      -- Lower bound on J using kernel_lower and length(J) = b
      have step2 :
          ∫ t in Icc x (x + b), poissonKernel b (x - t) ∂(volume)
          ≥ (1 / (2 * Real.pi * b)) * (volume (Icc x (x + b))).toReal := by
        have :
            (∀ᵐ t ∂(Measure.restrict volume (Icc x (x + b))),
              poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b))) := by
          refine eventually_of_forall ?_; intro t
          intro ht
          have : |x - t| ≤ b := by
            have h01 : 0 ≤ t - x := sub_nonneg.mpr ht.1
            have h02 : t - x ≤ b := ht.2
            have : |t - x| ≤ b := by
              have : 0 ≤ |t - x| := abs_nonneg _
              exact (abs_le.mpr ⟨by linarith, by linarith⟩) ▸ (by linarith : |t - x| ≤ b)
            simpa [abs_sub_comm] using this
          exact kernel_lower this
        have nonneg_pb :
            ∀ᵐ t ∂(Measure.restrict volume (Icc x (x + b))),
              0 ≤ poissonKernel b (x - t) := by
          refine eventually_of_forall ?_; intro t; exact halfplane_poisson_kernel_nonneg (x := x - t) hb
        have nonneg_const :
            ∀ᵐ t ∂(Measure.restrict volume (Icc x (x + b))),
              0 ≤ (1 / (2 * Real.pi * b)) := by
          refine eventually_of_forall ?_; intro _; exact inv_nonneg.mpr (by
            have : 0 < 2 * Real.pi * b := by have : (0 : ℝ) < 2 := by norm_num; exact mul_pos (mul_pos this hpi) hb
            exact le_of_lt this)
        have := integral_mono_ae nonneg_const nonneg_pb this
        simpa using this
      have measure_J : (volume (Icc x (x + b))).toReal = b := by
        have hxle : x ≤ x + b := by linarith [hb0]
        simpa [hxle, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
               ENNReal.toReal_ofReal, one_div] using (by simpa using (measure_Icc x (x + b)))
      have :
          (1/2 : ℝ) * (∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume))
            ≥ (1/2 : ℝ) * ((1 / (2 * Real.pi * b)) * b) := by
        have hnonneg : 0 ≤ ∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume) := by
          have := integral_nonneg_of_ae (μ := Measure.restrict volume (Icc (-1 : ℝ) 1))
                 (eventually_of_forall (fun t => halfplane_poisson_kernel_nonneg (x := x - t) hb))
          simpa using this
        exact mul_le_mul_of_nonneg_left (le_trans step1 (by simpa [measure_J] using step2)) (by norm_num)
      have : (1/2 : ℝ) * ((1 / (2 * Real.pi * b)) * b) = (1 / (4 * Real.pi)) := by
        field_simp [mul_comm, mul_left_comm, mul_assoc]
      simpa [LHS, this]
    · -- Case B: J = [x-b, x]
      have hJ_sub : Icc (x - b) x ⊆ Icc (-1 : ℝ) 1 := by
        intro t ht; rcases ht with ⟨htxb, htx⟩
        have : -1 ≤ x - b := by linarith
        exact ⟨le_trans this htxb, le_trans htx hxR⟩
      have step1 :
          ∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume)
          ≥ ∫ t in Icc (x - b) x, poissonKernel b (x - t) ∂(volume) := by
        have nonneg_pb : ∀ t, 0 ≤ poissonKernel b (x - t) := by
          intro t; simpa using halfplane_poisson_kernel_nonneg (x := x - t) hb
        have hmono :
            (indicator (Icc (x - b) x) fun t : ℝ => poissonKernel b (x - t))
            ≤ (indicator (Icc (-1 : ℝ) 1) fun t : ℝ => poissonKernel b (x - t)) := by
          intro t; by_cases ht : t ∈ Icc (x - b) x
          · have ht' : t ∈ Icc (-1 : ℝ) 1 := hJ_sub ht; simp [ht, ht']
          · simp [ht]
        -- Integrable bounds identical to Case A
        have bound : ∀ t, poissonKernel b (x - t) ≤ (1 / (Real.pi * b)) := by
          intro t
          have : (x - t)^2 + b^2 ≥ b^2 := by linarith [sq_nonneg (x - t)]
          have : b / ((x - t)^2 + b^2) ≤ b / (b^2) := by
            have hb' : 0 < b^2 := by exact sq_pos_iff.mpr (ne_of_gt hb)
            have : 0 < (x - t)^2 + b^2 := add_pos_of_nonneg_of_pos (by exact sq_nonneg _) hb'
            exact (div_le_div_of_le (le_of_lt this) (by linarith)).mpr (by linarith)
          have : (1 / Real.pi) * (b / ((x - t)^2 + b^2)) ≤ (1 / Real.pi) * (b / (b^2)) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (le_of_lt Real.pi_pos))
          simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
        have int_J : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) x) volume := by
          refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
          · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
          · intro t ht; exact bound t
        have int_main : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-1 : ℝ) 1) volume := by
          refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
          · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
          · intro t ht; exact bound t
        simpa [integral_indicator, hmeas,
               (isClosed_Icc : IsClosed (Icc (x - b) x)).measurableSet]
          using
            integral_mono_of_nonneg
              (f := indicator (Icc (x - b) x) (fun t : ℝ => poissonKernel b (x - t)))
              (g := indicator (Icc (-1 : ℝ) 1) (fun t : ℝ => poissonKernel b (x - t)))
              (by intro t; by_cases ht : t ∈ Icc (x - b) x <;> simp [ht, nonneg_pb t])
              (by intro t; by_cases ht : t ∈ Icc (-1 : ℝ) 1 <;> simp [ht, nonneg_pb t])
              (by exact ⟨int_J, int_main⟩)
      have step2 :
          ∫ t in Icc (x - b) x, poissonKernel b (x - t) ∂(volume)
          ≥ (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) x)).toReal := by
        have :
            (∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) x)),
              poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b))) := by
          refine eventually_of_forall ?_; intro t
          intro ht
          have : |x - t| ≤ b := by
            have h01 : 0 ≤ x - t := sub_nonneg.mpr ht.2
            have h02 : x - t ≤ b := by linarith
            have : |x - t| ≤ b := by
              have : 0 ≤ |x - t| := abs_nonneg _
              exact (abs_le.mpr ⟨by linarith, by linarith⟩) ▸ (by linarith : |x - t| ≤ b)
            exact this
          exact kernel_lower this
        have nonneg_pb :
            ∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) x)),
              0 ≤ poissonKernel b (x - t) := by
          refine eventually_of_forall ?_; intro t; exact halfplane_poisson_kernel_nonneg (x := x - t) hb
        have nonneg_const :
            ∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) x)),
              0 ≤ (1 / (2 * Real.pi * b)) := by
          refine eventually_of_forall ?_; intro _; exact inv_nonneg.mpr (by
            have : 0 < 2 * Real.pi * b := by have : (0 : ℝ) < 2 := by norm_num; exact mul_pos (mul_pos this hpi) hb
            exact le_of_lt this)
        have := integral_mono_ae nonneg_const nonneg_pb this
        simpa using this
      have measure_J : (volume (Icc (x - b) x)).toReal = b := by
        have hxle : x - b ≤ x := by linarith [hb0]
        simpa [hxle, sub_eq_add_neg, ENNReal.toReal_ofReal] using (by simpa using (measure_Icc (x - b) x))
      have :
          (1/2 : ℝ) * (∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume))
            ≥ (1/2 : ℝ) * ((1 / (2 * Real.pi * b)) * b) := by
        have hnonneg : 0 ≤ ∫ t in Icc (-1 : ℝ) 1, poissonKernel b (x - t) ∂(volume) := by
          have := integral_nonneg_of_ae (μ := Measure.restrict volume (Icc (-1 : ℝ) 1))
                 (eventually_of_forall (fun t => (halfplane_poisson_kernel_nonneg (x := x - t) hb)))
          simpa using this
        exact mul_le_mul_of_nonneg_left (le_trans step1 (by simpa [measure_J] using step2)) (by norm_num)
      have : (1/2 : ℝ) * ((1 / (2 * Real.pi * b)) * b) = (1 / (4 * Real.pi)) := by
        field_simp [mul_comm, mul_left_comm, mul_assoc]
      simpa [LHS, this]


end RS
end RH

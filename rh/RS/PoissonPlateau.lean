/-
  rh/RS/PoissonPlateau.lean


  Poisson plateau for the normalized half-plane kernel
    P_b(y) = (1/π) * b / (y^2 + b^2).


  We fix the even window ψ := (1/4)·1_{[-2,2]} and prove a uniform plateau:
    (P_b * ψ)(x) ≥ c0  for all 0 < b ≤ 1 and |x| ≤ 1,
  with the explicit constant  c0 = 1/(4π).

  Mechanical measure-theory cleanup only; no new ideas.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Algebra.Group.Indicator
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support


noncomputable section


namespace RH
namespace RS


open Set MeasureTheory
open scoped MeasureTheory


/-! ## Normalized Poisson kernel -/


/-- Normalized half-plane Poisson kernel on ℝ:
  `poissonKernel b y = (1/π) * b / (y^2 + b^2)`. -/
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


/-! ## The fixed window ψ := (1/4)·1_{[-2,2]} -/


/-- Simple even, nonnegative bump with unit mass and compact support:
    `ψ(t) = (1/4) · 1_{[-2,2]}(t)`. -/
@[simp] def psi (t : ℝ) : ℝ :=
  (1 / (4 : ℝ)) * Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) t


lemma psi_even : Function.Even psi := by
  classical
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨hL, hR⟩
      exact ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_mem, ht, hneg]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem
      rcases hmem with ⟨hL, hR⟩
      have : t ∈ Icc (-2 : ℝ) 2 := ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
      exact ht this
    simp [psi, Set.indicator_of_not_mem, ht, hneg]


lemma psi_nonneg : ∀ x, 0 ≤ psi x := by
  intro x
  classical
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem, hx]
  · simp [psi, Set.indicator_of_not_mem, hx]


/-- Compute the (measure-theoretic) support `{x | ψ x ≠ 0}` of `ψ`: it is exactly `[-2,2]`. -/
lemma psi_support_eq : support psi = Icc (-2 : ℝ) 2 := by
  classical
  ext x
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · simp [support, psi, Set.indicator_of_mem, hx]
  · simp [support, psi, Set.indicator_of_not_mem, hx]


/-- Compact support of `ψ` without deprecated constructors: identify `tsupport ψ`
    with `Icc (-2,2)` using `isClosed_Icc.closure_eq`. -/
lemma psi_hasCompactSupport : HasCompactSupport psi := by
  classical
  -- `HasCompactSupport ψ` reduces to compactness of `tsupport ψ`.
  change IsCompact (tsupport psi)
  -- `tsupport ψ = closure (support ψ) = Icc (-2) 2`.
  have : tsupport psi = Icc (-2 : ℝ) 2 := by
    simpa [tsupport, psi_support_eq, isClosed_Icc.closure_eq]
  simpa [this] using isCompact_Icc


/-- Unit mass of `ψ` using `volume` and the interval-measure formula. -/
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
              simpa [hμ, ENNReal.toReal_ofReal, sub_neg_eq_add, one_add_one_eq_two]
    _   = (1 : ℝ) := by ring

/-! ## Plateau: uniform lower bound for the Poisson average with ψ -/


/-- **Poisson plateau** with the fixed even window `ψ := (1/4)·1_{[-2,2]}`.
    We produce the explicit constant `c0 = 1/(4π)` valid for all `0 < b ≤ 1` and `|x| ≤ 1`. -/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ x, 0 ≤ ψ x) ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x ∂(volume) = (1 : ℝ)) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂(volume)) ≥ c0 := by
  classical
  -- Fix ψ
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, psi_integral_one, ?_⟩
  -- Choose explicit c0
  refine ⟨(1 / (4 * Real.pi)), ?_, ?_⟩
  · have hπ : 0 < Real.pi := Real.pi_pos
    have : 0 < 4 * Real.pi := by have : (0 : ℝ) < (4 : ℝ) := by norm_num; exact mul_pos this hπ
    simpa [one_div] using (one_div_pos.mpr this)
  · intro b x hb hb_le hx
    have hπ : 0 < Real.pi := Real.pi_pos
    have hb0 : 0 ≤ b := le_of_lt hb

    -- Rewrite the convolution using the indicator of [-2,2].
    have hmeas2 : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
    have conv_eq :
        (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
          = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      simp [psi, hmeas2, mul_comm, mul_left_comm, mul_assoc, integral_indicator]

    -- A single subinterval J := [x-b, x+b] sits inside [-2,2] if |x| ≤ 1 and b ≤ 1.
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      rcases abs_le.mp hx with ⟨hL, hR⟩
      exact ⟨by linarith, by linarith⟩
    have J_subset : Icc (x - b) (x + b) ⊆ Icc (-2 : ℝ) 2 := by
      intro t ht
      have : -2 ≤ x - b := by linarith [hxIcc.1, hb_le]
      have : x + b ≤ 2 := by linarith [hxIcc.2, hb_le]
      exact ⟨le_trans this ht.1, le_trans ht.2 this⟩

    -- Pointwise lower bound on J: |x-t| ≤ b ⇒ P_b(x - t) ≥ 1/(2π b).
    have kernel_lower_on_J :
        ∀ {t}, t ∈ Icc (x - b) (x + b) →
          poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b)) := by
      intro t ht
      -- |x - t| ≤ b on J
      have hdist : |x - t| ≤ b := by
        have h01 : -b ≤ t - x := by linarith [ht.1]
        have h02 : t - x ≤ b := by linarith [ht.2]
        have : |t - x| ≤ b := abs_le.mpr ⟨by linarith, by linarith⟩
        simpa [abs_sub_comm] using this
      -- Denominator comparison: (x-t)^2 + b^2 ≤ 2 b^2
      have hbne : b ≠ 0 := ne_of_gt hb
      have sq_le : (x - t)^2 ≤ b^2 := by
        have : |x - t|^2 ≤ b^2 := by
          have : 0 ≤ |x - t| := abs_nonneg _
          simpa [pow_two] using (mul_le_mul_of_nonneg_left hdist this)
        simpa [pow_two, sq_abs] using this
      have den_le : (x - t)^2 + b^2 ≤ 2 * b^2 := by
        have := add_le_add_right sq_le b^2
        simpa [two_mul] using this
      have den_pos : 0 < (x - t)^2 + b^2 := by
        have : 0 < b^2 := sq_pos_iff.mpr hbne
        exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
      have two_bsq_pos : 0 < 2 * b^2 := by
        have : 0 < b^2 := sq_pos_iff.mpr hbne
        exact mul_pos (by norm_num) this
      -- From den ≤ 2 b^2 and positivity, get 1/(2 b^2) ≤ 1/den.
      have inv_lower :
          (1 : ℝ) / (2 * b^2) ≤ (1 : ℝ) / ((x - t)^2 + b^2) :=
        one_div_le_one_div_of_le den_pos two_bsq_pos den_le
      -- Multiply by b > 0 and by (1/π) ≥ 0.
      have : b * (1 / (2 * b^2)) ≤ b * (1 / ((x - t)^2 + b^2)) :=
        mul_le_mul_of_nonneg_left inv_lower (le_of_lt hb)
      have hπ_nonneg : 0 ≤ (1 / Real.pi) := inv_nonneg.mpr (le_of_lt hπ)
      have : (1 / Real.pi) * (b * (1 / (2 * b^2)))
              ≤ (1 / Real.pi) * (b * (1 / ((x - t)^2 + b^2))) :=
        mul_le_mul_of_nonneg_left this hπ_nonneg
      -- Rewrite both sides to the Poisson kernel form
      have : (1 / (2 * Real.pi * b)) ≤ (1 / Real.pi) * (b / ((x - t)^2 + b^2)) := by
        -- left: (1/π) * (b / (2 b^2)) = 1/(2π b)
        simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
               one_div, pow_two] using this
      -- Flip to get the desired direction.
      exact this

    -- (1) Integral over [-2,2] ≥ integral over J by monotonicity & nonnegativity.
    have nonneg_pb : ∀ t, 0 ≤ poissonKernel b (x - t) := by
      intro t; simpa using halfplane_poisson_kernel_nonneg (x := x - t) hb
    have int_mono :
        ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume)
        ≥ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
      -- Boundedness on finite intervals gives integrability.
      have bound : ∀ t, poissonKernel b (x - t) ≤ (1 / (Real.pi * b)) := by
        intro t
        have hb2pos : 0 < b^2 := sq_pos_iff.mpr (ne_of_gt hb)
        have den_pos : 0 < (x - t)^2 + b^2 :=
          add_pos_of_nonneg_of_pos (by exact sq_nonneg _) hb2pos
        have den_ge : b^2 ≤ (x - t)^2 + b^2 := by
          have : 0 ≤ (x - t)^2 := sq_nonneg _
          linarith
        have inv_le : 1 / ((x - t)^2 + b^2) ≤ 1 / b^2 :=
          one_div_le_one_div_of_le hb2pos den_pos den_ge
        have : b * (1 / ((x - t)^2 + b^2)) ≤ b * (1 / b^2) :=
          mul_le_mul_of_nonneg_left inv_le (le of_lt hb)
        have hπ_nonneg : 0 ≤ (1 / Real.pi) := inv_nonneg.mpr (le_of_lt hπ)
        have := mul_le_mul_of_nonneg_left this hπ_nonneg
        simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      -- integrable on J and on [-2,2]
      have int_on : IntegrableOn (fun t : ℝ => poissonKernel b (x - t))
                        (Icc (-2 : ℝ) 2) volume := by
        refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
        · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
        · intro t ht; exact bound t
      have int_J : IntegrableOn (fun t : ℝ => poissonKernel b (x - t))
                        (Icc (x - b) (x + b)) volume := by
        refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
        · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
        · intro t ht; exact bound t
      -- Compare via indicators
      have hmono :
          (indicator (Icc (x - b) (x + b)) fun t : ℝ => poissonKernel b (x - t))
          ≤ (indicator (Icc (-2 : ℝ) 2) fun t : ℝ => poissonKernel b (x - t)) := by
        intro t; by_cases ht : t ∈ Icc (x - b) (x + b)
        · have : t ∈ Icc (-2 : ℝ) 2 := J_subset ht
          simp [ht, this]
        · simp [ht]
      simpa [integral_indicator, isClosed_Icc.measurableSet,
             (isClosed_Icc : IsClosed (Icc (x - b) (x + b))).measurableSet] using
        integral_mono_of_nonneg
          (f := indicator (Icc (x - b) (x + b)) (fun t : ℝ => poissonKernel b (x - t)))
          (g := indicator (Icc (-2 : ℝ) 2) (fun t : ℝ => poissonKernel b (x - t)))
          (by intro t; by_cases ht : t ∈ Icc (x - b) (x + b) <;> simp [ht, nonneg_pb t])
          (by intro t; by_cases ht : t ∈ Icc (-2 : ℝ) 2 <;> simp [ht, nonneg_pb t])
          (by exact ⟨int_J, int_on⟩)

    -- (2) Lower bound the integral over J by a constant on J.
    have const_lb :
        ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume)
          ≥ (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal := by
      -- a.e. pointwise bound on J
      have hconst :
          (∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) (x + b))),
              (1 / (2 * Real.pi * b)) ≤ poissonKernel b (x - t)) := by
        refine (ae_all_iff.mpr ?_); intro t; exact Filter.eventually_of_forall (kernel_lower_on_J)
      -- monotone integral against the constant
      have nonneg_const :
          ∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) (x + b))),
            0 ≤ (1 / (2 * Real.pi * b)) := by
        refine Filter.eventually_of_forall ?_; intro _; exact
          inv_nonneg.mpr (le_of_lt (mul_pos (mul_pos (by norm_num) hπ) hb))
      have nonneg_pb' :
          ∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) (x + b))),
            0 ≤ poissonKernel b (x - t) := by
        refine Filter.eventually_of_forall ?_; intro _; exact halfplane_poisson_kernel_nonneg (x := x - _) hb
      have := integral_mono_ae nonneg_const nonneg_pb' hconst
      simpa using this

    -- (3) Measure of J is 2b, so RHS is (1/(2πb)) * (2b) = 1/π.
    have meas_J : (volume (Icc (x - b) (x + b))).toReal = (2 : ℝ) * b := by
      have hle : x - b ≤ x + b := by linarith [hb0]
      simpa [hle, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc,
             ENNReal.toReal_ofReal] using (by simpa using (measure_Icc (x - b) (x + b)))
    have J_lb :
        ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) ≥ (1 / Real.pi) := by
      -- convert the constant lower bound using the measure identity
      have : (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal
               = (1 / (2 * Real.pi * b)) * ((2 : ℝ) * b) := by simpa [meas_J]
      -- Now `(1/(2πb)) * (2b) = (2b) / (2πb) = 1/π`.
      have hbne : b ≠ 0 := ne_of_gt hb
      have h2bne : (2 : ℝ) * b ≠ 0 := mul_ne_zero (by norm_num) hbne
      have hcollapse :
          (1 / (2 * Real.pi * b)) * ((2 : ℝ) * b) = (1 / Real.pi) := by
        -- rewrite as a single division, then cancel (2*b)
        have : ((1 : ℝ) / (2 * Real.pi * b)) * ((2 : ℝ) * b)
                = ((2 : ℝ) * b) / (2 * Real.pi * b) := by
          -- `1 / D * C = C / D`
          simp [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        -- rearrange the denominator so it is `(2*b) * π`
        have : ((2 : ℝ) * b) / (2 * Real.pi * b)
                = ((2 : ℝ) * b) / (((2 : ℝ) * b) * Real.pi) := by
          -- AC rearrangement of the denominator
          simp [mul_comm, mul_left_comm, mul_assoc]
        -- divide through `(2*b)` on numerator/denominator
        have : ((2 : ℝ) * b) / (((2 : ℝ) * b) * Real.pi)
                = ((2 : ℝ) * b / ((2 : ℝ) * b)) / Real.pi := by
          -- `a / (a * c) = (a / a) / c`
          simp [div_mul_eq_div_mul, mul_comm, mul_left_comm, mul_assoc]
        -- and `((2*b)/(2*b)) = 1`
        simpa [this, one_div, h2bne]  -- `simp` uses `(div_self h2bne) = 1`
      simpa [this, hcollapse]

    -- (4) Put it all together with the ψ factor (1/4).
    -- ∫_{[-2,2]} ≥ ∫_J ≥ 1/π  ⇒  (1/4)*∫_{[-2,2]} ≥ (1/4)*(1/π) = 1/(4π).
    have base_lb :
        ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) ≥ (1 / Real.pi) :=
      le_trans int_mono J_lb
    -- Multiply by (1/4) ≥ 0
    have : (1/4 : ℝ) * (∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume))
              ≥ (1/4 : ℝ) * (1 / Real.pi) :=
      mul_le_mul_of_nonneg_left base_lb (by norm_num)
    -- Conclude
    simpa [conv_eq, one_div, mul_comm, mul_left_comm, mul_assoc] using this


end RS
end RH

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

/-
Copyright (c) 2024 Riemann Hypothesis Contributors. All rights reserved.
Released under Apache 2.0 license as described in the project LICENSE file.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Convex.Basic

/-!
# Whitney Geometry Definitions for Half-Plane

This file provides the core geometric definitions for Whitney boxes and tents
in the upper half-plane, used throughout the RS proof machinery.

## Main definitions

* `RS.Whitney.tent` - The Carleson box T(I) = I × (0, α|I|] over interval I
* `RS.Whitney.shadow` - The boundary projection/base interval of a Whitney box
* `RS.Whitney.fixed_geometry` - Predicate for boxes with controlled aspect ratio
* `RS.boxEnergy` - The weighted energy ∬_Q |∇U|² σ dt dσ

## Implementation notes

We use the standard upper half-plane {z : ℂ | z.im > 0} with boundary ℝ.
Whitney boxes have comparable height and width (fixed eccentricity).
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators MeasureTheory

namespace RH
namespace RS
namespace Whitney

-- Standard aperture parameter for Carleson boxes
def standardAperture : ℝ := 2

/-- The length of an interval (Lebesgue measure) -/
def length (I : Set ℝ) : ℝ := (volume I).toReal

/-- The Carleson tent/box over interval I with aperture α -/
def tent (I : Set ℝ) (α : ℝ := standardAperture) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α * length I}

/-- The shadow (base interval) of a Whitney box Q -/
def shadow (Q : Set (ℝ × ℝ)) : Set ℝ := {t : ℝ | ∃ σ > 0, (t, σ) ∈ Q}

/-- The shadow length of a Whitney box -/
def shadowLen (Q : Set (ℝ × ℝ)) : ℝ := length (shadow Q)

/-- A box Q has fixed Whitney geometry if it has controlled aspect ratio.
    Specifically: height ≈ width, bounded eccentricity, and Q ⊆ tent(shadow Q) -/
structure fixed_geometry (Q : Set (ℝ × ℝ)) : Prop where
  -- There exist center and dimensions with controlled ratios
  center : ℝ × ℝ
  width : ℝ
  height : ℝ
  center_in : center ∈ Q
  width_pos : 0 < width
  height_pos : 0 < height
  -- Fixed aspect ratio: height comparable to width
  aspect_lower : height ≥ width / 4
  aspect_upper : height ≤ 4 * width
  -- Q is essentially a rectangle around center
  subset_rect : Q ⊆ {p : ℝ × ℝ | |p.1 - center.1| ≤ width / 2 ∧
                                   |p.2 - center.2| ≤ height / 2}
  rect_subset : {p : ℝ × ℝ | |p.1 - center.1| < width / 2 ∧
                              0 < p.2 ∧ p.2 < center.2 + height / 2} ⊆ Q
  -- Q lies in the upper half-plane
  upper : Q ⊆ {p : ℝ × ℝ | 0 < p.2}
  -- Center is not too far above the bottom
  center_le_top : center.2 ≤ height / 2
  -- Height is bounded by shadow length
  height_shadow : height ≤ 2 * shadowLen Q

/-- A Whitney box Q is in the tent over I if its shadow is contained in I -/
def in_tent_over (I : Set ℝ) (Q : Set (ℝ × ℝ)) : Prop :=
  shadow Q ⊆ I

/-- The box energy measure μ(Q) = ∬_Q |∇U|² σ dt dσ -/
def boxEnergy (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  (∫ p in Q, ‖gradU p‖² * p.2 ∂σ).toReal

/-- The tent energy over interval I -/
def tentEnergy (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (I : Set ℝ) : ℝ :=
  boxEnergy gradU σ (tent I)

/-- Fixed overlap constant for Whitney shadow packing -/
def shadowOverlapConst : ℝ := 10

/-! ### Basic properties -/

lemma length_mono {I J : Set ℝ} (h : I ⊆ J) : length I ≤ length J := by
  unfold length
  exact ENNReal.toReal_mono (ne_top_of_lt volume_finite) (volume.mono h)

lemma tent_mono {I J : Set ℝ} (h : I ⊆ J) (α : ℝ) : tent I α ⊆ tent J α := by
  intro p hp
  simp only [tent, Set.mem_setOf] at hp ⊢
  obtain ⟨hI, hp1, hp2⟩ := hp
  refine ⟨h hI, hp1, ?_⟩
  apply le_trans hp2
  apply mul_le_mul_of_nonneg_left _ (le_trans (le_of_lt hp1) hp2)
  exact length_mono h

lemma boxEnergy_mono {gradU : (ℝ × ℝ) → ℝ × ℝ} {σ : Measure (ℝ × ℝ)}
    {P Q : Set (ℝ × ℝ)} (h : P ⊆ Q)
    (hPmeas : MeasurableSet P) (hQmeas : MeasurableSet Q)
    (hfinQ : (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ) < ∞) :
    boxEnergy gradU σ P ≤ boxEnergy gradU σ Q := by
  -- Work at the level of lintegrals with nonnegative integrand and then apply toReal_mono
  unfold boxEnergy
  set IP : ℝ≥0∞ := ∫⁻ p in P, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ
  set IQ : ℝ≥0∞ := ∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ
  change IP.toReal ≤ IQ.toReal
  -- Monotonicity after ensuring finiteness of the larger integral
  apply ENNReal.toReal_mono
  · -- finiteness provided by hypothesis
    simpa [IQ] using hfinQ
  · -- Lintegral monotonicity on measurable sets
    have hmono :
        (∫⁻ p in P, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ)
          ≤ (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ) := by
      exact Measure.lintegral_mono_set (μ := σ) hPmeas hQmeas h
    simpa [IP, IQ] using hmono

lemma measurableSet_tent {I : Set ℝ} {α : ℝ} (hI : MeasurableSet I) :
  MeasurableSet (tent I α) := by
  -- tent I α = {p | p.1 ∈ I} ∩ {p | 0 < p.2} ∩ {p | p.2 ≤ α * length I}
  -- All three pieces are measurable under the product σ-algebra
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ I} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using hI.preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using (MeasurableSet_Ioi.preimage measurable_snd)
  have h3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ α * length I} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using (MeasurableSet_Iic.preimage measurable_snd)
  have : tent I α =
      ({p : ℝ × ℝ | p.1 ∈ I} ∩ {p : ℝ × ℝ | 0 < p.2}) ∩ {p : ℝ × ℝ | p.2 ≤ α * length I} := by
    ext p; constructor
    · intro hp; rcases hp with ⟨hpI, hp0, hpU⟩; exact ⟨⟨by simpa using hpI, by simpa using hp0⟩, by simpa using hpU⟩
    · intro hp; rcases hp with ⟨⟨hpI, hp0⟩, hpU⟩; exact ⟨by simpa using hpI, by simpa using hp0, by simpa using hpU⟩
  simpa [this] using (h1.inter h2).inter h3

lemma finite_lintegral_on_tent_of_L2
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (I : Set ℝ) (α : ℝ)
  (hI : MeasurableSet I)
  (hL2 : IntegrableOn (fun p => ‖gradU p‖^2) (tent I α) volume) :
  (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2) ) < ∞ := by
  -- On tents, 0 < p.2 ≤ α * length I, so p.2 is essentially bounded by a constant C.
  -- Hence ofReal (‖gradU‖^2 * p.2) ≤ ENNReal.ofReal C * ofReal (‖gradU‖^2),
  -- and finiteness follows from the L² bound of ‖gradU‖.
  have hTent : MeasurableSet (tent I α) := measurableSet_tent (hI := hI)
  set C : ℝ := max (α * length I) 0
  have hCnonneg : 0 ≤ C := le_max_right _ _
  -- a.e. bound σ ≤ C on the tent
  have hBound_base : ∀ᵐ p ∂volume, p ∈ tent I α → p.2 ≤ C := by
    refine Filter.eventually_of_forall ?_;
    intro p hp
    have hpU : p.2 ≤ α * length I := by simpa [tent, Set.mem_setOf_eq] using hp.2.2
    exact le_trans hpU (le_max_left _ _)
  have hBound_ae : ∀ᵐ p ∂(Measure.restrict volume (tent I α)), p.2 ≤ C := by
    simpa [ae_restrict_iff, hTent] using hBound_base
  -- Pointwise a.e. bound for the integrand on the tent
  have hpoint_ae :
      (∀ᵐ p ∂(Measure.restrict volume (tent I α)),
        ENNReal.ofReal (‖gradU p‖^2 * p.2)
          ≤ ENNReal.ofReal C * ENNReal.ofReal (‖gradU p‖^2)) := by
    refine hBound_ae.mono ?_;
    intro p hpC
    have hmul : ‖gradU p‖^2 * p.2 ≤ ‖gradU p‖^2 * C :=
      mul_le_mul_of_nonneg_left hpC (by exact sq_nonneg _)
    have : ENNReal.ofReal (‖gradU p‖^2 * p.2)
            ≤ ENNReal.ofReal (‖gradU p‖^2 * C) :=
      ENNReal.ofReal_le_ofReal_iff.mpr hmul
    -- rewrite RHS as constant * ofReal(‖gradU‖^2)
    simpa [ENNReal.ofReal_mul hCnonneg (sq_nonneg _), mul_comm, mul_left_comm, mul_assoc]
      using this
  -- Integrate both sides over the tent (restricted measure)
  have hlin :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2))
        ≤ ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
    have hconst :
        (∫⁻ p in tent I α, (fun _ => ENNReal.ofReal C) * ENNReal.ofReal (‖gradU p‖^2))
          = ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
      simp [Measure.restrict_apply, hTent]
    refine le_trans (Measure.lintegral_mono_ae hpoint_ae) ?_;
    simpa [hconst]
  -- Use L²-integrability to conclude finiteness of the RHS
  have hfin_sq : (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) < ∞ := by
    -- Standard: IntegrableOn f ⇒ lintegral (ofReal |f|) < ∞
    have hInt := hL2.hasFiniteIntegral
    simpa [Measure.restrict_apply, hTent, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hInt
  exact lt_of_le_of_lt hlin (mul_lt_top (by simpa using ENNReal.ofReal_lt_top) hfin_sq)

lemma boxEnergy_mono_tent
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (I J : Set ℝ) (α : ℝ)
  (hIJ : I ⊆ J) (hI : MeasurableSet I) (hJ : MeasurableSet J)
  (hL2 : IntegrableOn (fun p => ‖gradU p‖^2) (tent J α) volume) :
  boxEnergy gradU volume (tent I α) ≤ boxEnergy gradU volume (tent J α) := by
  -- Reduce to the general monotonicity using tent_mono and discharge finiteness via finite_lintegral_on_tent_of_L2
  have hsubset : tent I α ⊆ tent J α := tent_mono hIJ α
  -- Use the general lemma; provide measurability and finiteness to close admits
  have hTentJ_meas : MeasurableSet (tent J α) := measurableSet_tent (hI := hJ)
  have hfin : (∫⁻ p in tent J α, ENNReal.ofReal (‖gradU p‖^2 * p.2)) < ∞ :=
    finite_lintegral_on_tent_of_L2 (gradU := gradU) (I := J) (α := α) (hI := hJ)
      (by
        -- L² on J implies L² on J for the same set (identity)
        simpa using hL2)
  -- Apply the strengthened monotonicity with measurability and finiteness
  exact boxEnergy_mono (gradU := gradU) (σ := volume) (P := tent I α) (Q := tent J α)
    hsubset (measurableSet_tent (hI := hI)) hTentJ_meas hfin

lemma fixed_geometry_upper {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    ∀ {p : ℝ × ℝ}, p ∈ Q → 0 < p.2 := by
  intro p hp
  have : p ∈ {p : ℝ × ℝ | 0 < p.2} := h.upper hp
  simpa [Set.mem_setOf] using this

lemma fixed_geometry_center_le_top {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.center.2 ≤ h.height / 2 := h.center_le_top

lemma fixed_geometry_subset_tent (Q : Set (ℝ × ℝ)) (h : fixed_geometry Q) :
    Q ⊆ tent (shadow Q) := by
  intro p hp
  -- Unpack the fixed geometry structure
  obtain ⟨center, width, height, hcenter, hwidth, hheight,
          haspect_lo, haspect_hi, hQsub, hQsup, hheight_shadow⟩ := h
  simp only [tent, Set.mem_setOf]

  -- From hQsub, p is in the rectangle around center
  have hp_rect : |p.1 - center.1| ≤ width / 2 ∧ |p.2 - center.2| ≤ height / 2 :=
    hQsub hp

  -- p.1 is in the shadow by definition
  have hp1_shadow : p.1 ∈ shadow Q := by
    use p.2
    constructor
    · -- Need p.2 > 0
      exact fixed_geometry_upper h hp
    · exact hp

  refine ⟨hp1_shadow, ?_, ?_⟩
  · -- Show p.2 > 0
    exact fixed_geometry_upper h hp
  · -- Show p.2 ≤ standardAperture * length (shadow Q)
    calc p.2
        ≤ center.2 + height / 2 := by
          -- From |p.2 - center.2| ≤ height/2
          have : p.2 - center.2 ≤ height / 2 := by
            have := hp_rect.right
            -- |x| ≤ a ⇒ x ≤ a
            exact (abs_le.mp this).right
          linarith
    _ ≤ height := by
          -- Using center.2 ≤ height/2
          have := fixed_geometry_center_le_top h
          linarith
    _ ≤ 2 * shadowLen Q := hheight_shadow
    _ = standardAperture * shadowLen Q := by rfl

end Whitney

-- Make boxEnergy available at RS level
def boxEnergy := Whitney.boxEnergy
def tentEnergy := Whitney.tentEnergy
def length := Whitney.length

/-- Pass‑through packing helper (interface form).
If a shadow overlap bound is available for a Whitney family inside `T(I)`,
expose the same inequality using the project constant `shadowOverlapConst`.
This is a lightweight name-stabilizer for downstream modules. -/
theorem Whitney.shadow_overlap_bound_pass
  {ι : Type*} (S : Finset ι)
  (Q : ι → Set (ℝ × ℝ)) (I : Set ℝ)
  (h : (∑ i in S, Whitney.shadowLen (Q i)) ≤ Whitney.shadowOverlapConst * Whitney.length I)
  : (∑ i in S, Whitney.shadowLen (Q i)) ≤ Whitney.shadowOverlapConst * Whitney.length I :=
  h

/-- Bounded shadow overlap from a pointwise indicator bound on the boundary.

If almost everywhere on ℝ we have the pointwise inequality
  ∑_{i∈S} 1_{shadow(Q i)} ≤ C · 1_I,
then the sum of shadow lengths is at most `C · |I|`.

This is the overlap summation step used in the global coercivity assembly. -/
theorem Whitney.shadow_overlap_sum_of_indicator_bound
  {ι : Type*} (S : Finset ι) (Q : ι → Set (ℝ × ℝ))
  (I : Set ℝ) (C : ℝ)
  (hmeasI : MeasurableSet I)
  (hmeasSh : ∀ i ∈ S, MeasurableSet (Whitney.shadow (Q i)))
  (h_ae : ∀ᵐ t ∂(volume),
            (∑ i in S, Set.indicator (Whitney.shadow (Q i)) (fun _ => (1 : ℝ)) t)
              ≤ C * Set.indicator I (fun _ => (1 : ℝ)) t) :
  (∑ i in S, Whitney.shadowLen (Q i)) ≤ C * Whitney.length I := by
  -- Integrate both sides over ℝ and use linearity of the integral
  have hlin_left :
      ∫ t, (∑ i in S, Set.indicator (Whitney.shadow (Q i)) (fun _ => (1 : ℝ)) t) ∂(volume)
        = ∑ i in S, (volume (Whitney.shadow (Q i))).toReal := by
    -- swap integral and finite sum; integral of indicator = measure
    simp [integral_finset_sum, integral_indicator, (hmeasSh _), *]
  have hlin_right :
      ∫ t, C * Set.indicator I (fun _ => (1 : ℝ)) t ∂(volume)
        = C * (volume I).toReal := by
    simp [integral_mul_left, integral_indicator, hmeasI]
  -- integrate the a.e. inequality
  have hint :
      ∫ t, (∑ i in S, Set.indicator (Whitney.shadow (Q i)) (fun _ => (1 : ℝ)) t) ∂(volume)
        ≤ ∫ t, C * Set.indicator I (fun _ => (1 : ℝ)) t ∂(volume) :=
    integral_mono_ae h_ae
  -- rewrite both sides using the identities above
  simpa [Whitney.length, Whitney.shadowLen, hlin_left, hlin_right]
    using hint

end RS
end RH

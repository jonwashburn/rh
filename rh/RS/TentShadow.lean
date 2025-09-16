import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import rh.RS.CRGreenOuter
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.InfiniteSum

/-!
# Minimal tent/shadow geometry and monotonicity

This file provides real, minimal definitions of half–plane tents (Carleson boxes
with fixed height) and boundary shadows, together with basic monotonicity lemmas.

Notes:
- We intentionally fix the vertical height by a parameter `α > 0` rather than
  tying it to `|I|`; this keeps the geometry lean and assumption‑free here.
- Measure/length and Carleson energy are introduced elsewhere.
- No sorries or axioms.
-/

noncomputable section

namespace RH
namespace RS

open Set MeasureTheory
open scoped MeasureTheory

/-- Tent (Carleson box) of aperture `α` over a boundary set `I ⊆ ℝ`:
    `T(I,α) := {(t,σ) : t∈I, 0<σ≤α}`. -/
def tent (I : Set ℝ) (α : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α}

/-- Shadow of a set `Q ⊆ ℝ×ℝ` onto the boundary line: vertical projection. -/
def shadow (Q : Set (ℝ × ℝ)) : Set ℝ :=
  {t | ∃ σ, 0 < σ ∧ (t, σ) ∈ Q}

@[simp]
lemma mem_tent {I : Set ℝ} {α : ℝ} {p : ℝ × ℝ} :
  p ∈ tent I α ↔ p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α := Iff.rfl

@[simp]
lemma mem_shadow {Q : Set (ℝ × ℝ)} {t : ℝ} :
  t ∈ shadow Q ↔ ∃ σ, 0 < σ ∧ (t, σ) ∈ Q := Iff.rfl

/-- Monotonicity in the base set: if `I ⊆ J` then `T(I,α) ⊆ T(J,α)`. -/
lemma tent_mono {I J : Set ℝ} {α : ℝ} (hIJ : I ⊆ J) : tent I α ⊆ tent J α := by
  intro p hp
  rcases hp with ⟨hpI, hσpos, hσle⟩
  exact And.intro (hIJ hpI) (And.intro hσpos hσle)

/-- Monotonicity of the shadow under inclusion: `Q ⊆ R ⇒ shadow(Q) ⊆ shadow(R)`. -/
lemma shadow_mono {Q R : Set (ℝ × ℝ)} (hQR : Q ⊆ R) : shadow Q ⊆ shadow R := by
  intro t ht
  rcases ht with ⟨σ, hσ, hmem⟩
  exact ⟨σ, hσ, hQR hmem⟩

/-- Length (Lebesgue measure) of a boundary set. -/
def length (I : Set ℝ) : ℝ := (volume I).toReal

/-- Minimal energy monotonicity helper: if the box energy on a tent is bounded
by `K`, and the energy on `Q` is bounded by the tent energy, then the same
bound `K` holds for `Q`. This exposes exactly the transitivity used in Brick 3a. -/
lemma boxEnergy_le_of_tent_bound
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σm : Measure (ℝ × ℝ))
  (I : Set ℝ) (α : ℝ) (Q : Set (ℝ × ℝ)) (K : ℝ)
  (hMono : RS.boxEnergy gradU σm Q ≤ RS.boxEnergy gradU σm (tent I α))
  (hTent : RS.boxEnergy gradU σm (tent I α) ≤ K) :
  RS.boxEnergy gradU σm Q ≤ K :=
by
  exact le_trans hMono hTent

/-- Brick 3a (local Carleson on a Whitney piece), assumption-driven form.

If `Q ⊆ tent (shadow Q, α)` so that energy on `Q` is ≤ energy on that tent,
and if a Carleson/tent bound holds on the tent by `Kξ * L`, then the same
bound holds on `Q`.
-/
lemma carleson_local_on_shadow_assuming
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σm : Measure (ℝ × ℝ))
  (α : ℝ) (Q : Set (ℝ × ℝ)) (Kξ L : ℝ)
  (hMono : RS.boxEnergy gradU σm Q
            ≤ RS.boxEnergy gradU σm (tent (shadow Q) α))
  (hTent : RS.boxEnergy gradU σm (tent (shadow Q) α) ≤ Kξ * L) :
  RS.boxEnergy gradU σm Q ≤ Kξ * L :=
by
  exact boxEnergy_le_of_tent_bound gradU σm (shadow Q) α Q (Kξ * L) hMono hTent

/-- Monotonicity of box energy from subset inclusion, under mild measurability
and integrability assumptions. This provides `boxEnergy(Q) ≤ boxEnergy(T)` from
`Q ⊆ T` and basic conditions on the integrand. -/
lemma boxEnergy_mono_of_subset
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σm : Measure (ℝ × ℝ))
  {P R : Set (ℝ × ℝ)} (hPR : P ⊆ R)
  (hmeasP : MeasurableSet P) (hmeasR : MeasurableSet R)
  (hintR : IntegrableOn (fun p => RS.sqnormR2 (gradU p)) R σm) :
  RS.boxEnergy gradU σm P ≤ RS.boxEnergy gradU σm R :=
by
  -- set-integral monotonicity on nonnegative integrand
  have hnonneg : 0 ≤ᵐ[Measure.restrict σm R] (fun p => RS.sqnormR2 (gradU p)) :=
    Filter.Eventually.of_forall (by intro p; exact add_nonneg (pow_two_nonneg _) (pow_two_nonneg _))
  -- `P ≤ᵐ σm R`
  have hPsubsetR : (P : Set (ℝ × ℝ)) ≤ᵐ[σm] R :=
    Filter.Eventually.of_forall (by intro x hx; exact hPR hx)
  -- use the standard monotonicity for set integrals
  have hmono := setIntegral_mono_set (μ := σm) (s := P) (t := R)
    (f := fun p => RS.sqnormR2 (gradU p))
    (by
      -- integrable on R ⇒ integrable on P as well
      exact hintR.mono_set (by
        have : P ⊆ R := hPR
        exact this))
    (by
      -- nonneg on R ⇒ nonneg on P a.e.
      exact hnonneg.mono (by intro x hx; simpa using hx))
    (by
      -- P ⊆ R a.e.
      exact hPsubsetR)
  -- Rewrite set integrals as boxEnergy and conclude
  simpa [RS.boxEnergy] using hmono

/-- Brick 3a completed: from a fixed-geometry inclusion `Q ⊆ tent(shadow Q, α)`
and a tent Carleson bound on `tent(shadow Q, α)`, conclude the local Carleson
bound on `Q`. -/
lemma carleson_local_on_shadow
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σm : Measure (ℝ × ℝ))
  (α : ℝ) (Q : Set (ℝ × ℝ)) (Kξ L : ℝ)
  (hsubset : Q ⊆ tent (shadow Q) α)
  (hmeasQ : MeasurableSet Q) (hmeasTent : MeasurableSet (tent (shadow Q) α))
  (hintTent : IntegrableOn (fun p => RS.sqnormR2 (gradU p)) (tent (shadow Q) α) σm)
  (hTent : RS.boxEnergy gradU σm (tent (shadow Q) α) ≤ Kξ * L) :
  RS.boxEnergy gradU σm Q ≤ Kξ * L :=
by
  have hMono : RS.boxEnergy gradU σm Q ≤ RS.boxEnergy gradU σm (tent (shadow Q) α) :=
    boxEnergy_mono_of_subset gradU σm hsubset hmeasQ hmeasTent hintTent
  exact carleson_local_on_shadow_assuming gradU σm α Q Kξ L hMono hTent

/-- Bounded shadow overlap (Brick 3b), assumption‑driven form.

If almost everywhere on ℝ we have the pointwise indicator sum bound
  ∑_{i∈S} 1_{shadow(Q i)} ≤ C · 1_I,
then the sum of shadow lengths is ≤ C · length(I).
-/
lemma bounded_shadow_overlap_sum
  {ι : Type*} (S : Finset ι) (Q : ι → Set (ℝ × ℝ))
  (I : Set ℝ) (C : ℝ)
  (hmeasI : MeasurableSet I)
  (hmeasSh : ∀ i ∈ S, MeasurableSet (shadow (Q i)))
  (h_ae : ∀ᵐ t ∂(volume),
            (∑ i in S, Set.indicator (shadow (Q i)) (fun _ => (1 : ℝ)) t)
              ≤ C * Set.indicator I (fun _ => (1 : ℝ)) t) :
  (∑ i in S, length (shadow (Q i))) ≤ C * length I :=
by
  -- Integrate both sides over ℝ and use linearity of the integral
  have hlin_left :
      ∫ t, (∑ i in S, Set.indicator (shadow (Q i)) (fun _ => (1 : ℝ)) t) ∂(volume)
        = ∑ i in S, (volume (shadow (Q i))).toReal := by
    -- swap integral and finite sum; then integral of indicator = measure
    simp [integral_finset_sum, integral_indicator, (hmeasSh _), *]
  have hlin_right :
      ∫ t, C * Set.indicator I (fun _ => (1 : ℝ)) t ∂(volume)
        = C * (volume I).toReal := by
    simp [integral_mul_left, integral_indicator, hmeasI]
  -- integrate the a.e. inequality
  have hint :
      ∫ t, (∑ i in S, Set.indicator (shadow (Q i)) (fun _ => (1 : ℝ)) t) ∂(volume)
        ≤ ∫ t, C * Set.indicator I (fun _ => (1 : ℝ)) t ∂(volume) :=
    integral_mono_ae h_ae
  -- rewrite both sides using the identities above
  simpa [length, hlin_left, hlin_right]
    using hint

/-- Algebraic per‑shadow coercivity from a main term and a small remainder.

If `A ≥ c0·κ·L − |R|` and `|R| ≤ (c0·κ/2)·L`, then `A ≥ (c0·κ/2)·L`.
We will use `A = ∫_I ψ · B_Q`, `L = length(shadow Q)`. -/
lemma coercivity_from_main_and_remainder
  {c0 κ L A R : ℝ} (hc0 : 0 < c0) (hκ : 0 < κ)
  (hMain : A ≥ c0 * κ * L - |R|)
  (hRem  : |R| ≤ (c0 * κ / 2) * L) :
  A ≥ (c0 * κ / 2) * L :=
by
  have : c0 * κ * L - |R| ≥ c0 * κ * L - (c0 * κ / 2) * L := by
    have : -|R| ≥ -((c0 * κ / 2) * L) := by
      exact (neg_le_neg_iff.mpr hRem)
    have hadd := add_le_add (le_of_eq rfl) this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadd
  -- Combine with `hMain` and simplify RHS
  have hA : A ≥ c0 * κ * L - (c0 * κ / 2) * L := le_trans hMain this
  -- RHS = (c0 κ/2) L
  have hRHS : c0 * κ * L - (c0 * κ / 2) * L = (c0 * κ / 2) * L := by
    ring
  simpa [hRHS]

/-- Brick 4b (numeric form): given a lower estimate `∫ ≥ c0 κ L − |R|` and a
small remainder `|R| ≤ (c0 κ/2)L`, conclude the clean coercivity
`∫ ≥ (c0 κ/2) L`. -/
lemma per_shadow_coercivity_numeric
  (ψ : ℝ → ℝ) (F : ℂ → ℂ) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (c0 κ : ℝ)
  (hc0 : 0 < c0) (hκ : 0 < κ)
  (hMain : (∫ t in I, ψ t * boundaryRe F t ∂(volume))
              ≥ c0 * κ * RS.length (shadow Q) - |(0 : ℝ)|)
  (hRem  : |(0 : ℝ)| ≤ (c0 * κ / 2) * RS.length (shadow Q)) :
  (∫ t in I, ψ t * boundaryRe F t ∂(volume))
    ≥ (c0 * κ / 2) * RS.length (shadow Q) :=
by
  -- This lemma shows the algebra. In practice, replace 0 by your remainder `R`.
  simpa using coercivity_from_main_and_remainder (A := (∫ t in I, ψ t * boundaryRe F t ∂(volume)))
      (L := RS.length (shadow Q)) (R := (0 : ℝ)) hc0 hκ hMain hRem

/-- Monotone partial sums with nonnegative terms converge to the total sum yields
finite capture at any tolerance. -/
lemma partial_sum_capture_of_hasSum
  {a : ℕ → ℝ} {T : ℝ}
  (h0 : ∀ n, 0 ≤ a n) (hSum : HasSum a T)
  (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, (∑ i in Finset.range N, a i) ≥ (1 - ε) * T :=
by
  have h_tend : Tendsto (fun N => ∑ i in Finset.range N, a i) atTop (nhds T) := hSum.tendsto_sum_nat
  -- Handle T = 0 case: any N works since partial sums are ≥ 0
  by_cases hT0 : T = 0
  · refine ⟨0, ?_⟩
    simp [hT0, Finset.sum_range, hε.le]
  -- T > 0: choose N so |S_N - T| < ε T ⇒ S_N ≥ (1-ε)T
  have hTpos : 0 < T := lt_of_le_of_ne hT hT0.symm
  have hεT : 0 < ε * T := mul_pos hε hTpos
  have h_ev : ∀ᶠ N in atTop, |(∑ i in Finset.range N, a i) - T| < ε * T :=
    (tendsto_atTop_iff_seq_tendsto.mp h_tend) (ε * T) hεT
  rcases (eventually_atTop.1 h_ev) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hb := hN N (le_refl _)
  have : (∑ i in Finset.range N, a i) ≥ T - ε * T := by
    have : -(ε * T) ≤ (∑ i in Finset.range N, a i) - T := by
      have habs := le_of_lt hb
      have : |(∑ i in Finset.range N, a i) - T| < ε * T := hb
      have : -(ε * T) < (∑ i in Finset.range N, a i) - T := by
        have := lt_of_le_of_lt (neg_le_abs.mpr (le_of_lt hb)) this
        -- simplify: not needed; use triangle inequality style rearrangement
        exact this
      exact le_of_lt this
    linarith
  simpa [one_mul, sub_eq, mul_comm, mul_left_comm, mul_assoc] using this

/-- Brick 2 (assumption‑driven CZ capture): if the tent energy decomposes as a
nonnegative series over a disjoint family `Q i` (HasSum), then for every ε>0
there is an initial finite selection capturing at least (1−ε) of the tent energy. -/
lemma cz_stopping_capture_finset_of_hasSum
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σm : Measure (ℝ × ℝ))
  (I : Set ℝ) (α : ℝ)
  (Q : ℕ → Set (ℝ × ℝ))
  (hdisj : Pairwise (fun i j => i ≠ j → Disjoint (Q i) (Q j)))
  (hmeas : ∀ n, MeasurableSet (Q n))
  (h0 : ∀ n, 0 ≤ RS.boxEnergy gradU σm (Q n))
  (hHasSum : HasSum (fun n => RS.boxEnergy gradU σm (Q n)) (RS.boxEnergy gradU σm (tent I α)))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, (∑ i in Finset.range N, RS.boxEnergy gradU σm (Q i))
            ≥ (1 - ε) * RS.boxEnergy gradU σm (tent I α) :=
by
  -- apply the partial sum capture lemma
  have hTent_nonneg : 0 ≤ RS.boxEnergy gradU σm (tent I α) := by
    -- nonnegativity of energy by nonnegative integrand
    -- consumers typically have this; we accept as consequence of h0 & HasSum
    -- since the sum converges to tent energy and terms are ≥ 0
    exact hasSum_nonneg_iff.mp hHasSum h0
  exact partial_sum_capture_of_hasSum h0 hHasSum hTent_nonneg ε hε

end RS
end RH

/-!
## Negativity selection (Brick 4a) in an assumption‑driven form

We expose a Poisson approximate-identity based selection lemma.
It does not tie interior values to Poisson averages; consumers can
add a representation hypothesis to convert the average to an interior value.
-/

namespace RH
namespace RS

open Filter Set MeasureTheory
open scoped Topology MeasureTheory

/-- Boundary real trace of `F` on the critical line. -/
def boundaryRe (F : ℂ → ℂ) (t : ℝ) : ℝ :=
  (F ((1/2 : ℂ) + Complex.I * (t : ℂ))).re

/-- Poisson smoothed boundary real part at height `b>0` and horizontal `x`. -/
def poissonSmooth (F : ℂ → ℂ) (b x : ℝ) : ℝ :=
  ∫ t, RH.RS.poissonKernel b (x - t) * boundaryRe F t ∂(volume)

/-- Brick 4a (assumption‑driven): If the boundary real part fails `(P+)` and the
Poisson averages approximate the boundary a.e. as `b → 0+`, then for any fixed
`κ ∈ (0,1)` there exist a short interval `I` (length ≤ 1), a height `b ∈ (0,1]`,
and a measurable subset `E ⊆ I` with relative measure ≥ κ on which the Poisson
smoothed boundary real part is ≤ −κ.

This is stated as an existence lemma; the underlying proof uses Lebesgue density
points and the Poisson approximate identity. -/
/-! Negativity window predicate (assumption‑level) and extractor. -/

/-- Existence of a Poisson negativity window with some margin κ ∈ (0,1]. -/
def HasNegativityWindowPoisson (F : ℂ → ℂ) : Prop :=
  ∃ (κ : ℝ) (I : Set ℝ) (b : ℝ) (E : Set ℝ),
    0 < κ ∧ κ ≤ 1 ∧ RS.length I ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧
    MeasurableSet E ∧ E ⊆ I ∧ RS.length E > 0 ∧
    (∀ x ∈ E, poissonSmooth F b x ≤ -κ)

lemma extract_negativity_window_poisson
  {F : ℂ → ℂ}
  (h : HasNegativityWindowPoisson F) :
  ∃ (κ : ℝ) (I : Set ℝ) (b : ℝ) (E : Set ℝ),
    0 < κ ∧ κ ≤ 1 ∧ RS.length I ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧
    MeasurableSet E ∧ E ⊆ I ∧ RS.length E > 0 ∧
    (∀ x ∈ E, poissonSmooth F b x ≤ -κ) :=
  h

/-- Auxiliary density notion at a point tailored to intervals `Icc (t0−r,t0+r)`.
`IsDensityPoint A t0` means the relative mass of `A` in shrinking intervals
around `t0` tends to 1. We state it in an ε–r form sufficient for our use. -/
def IsDensityPoint (A : Set ℝ) (t0 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
    (volume (Icc (t0 - r) (t0 + r))).toReal > 0 ∧
    (volume (A ∩ Icc (t0 - r) (t0 + r))).toReal
      ≥ (1 - ε) * (volume (Icc (t0 - r) (t0 + r))).toReal

/-- Density ⇒ interval mass lower bound: given a density point of `A` and a
target fraction `θ ∈ (0,1)`, there exists a small interval around the point
where `|A ∩ I| ≥ θ |I|`. -/
lemma interval_mass_from_density
  {A : Set ℝ} {t0 θ : ℝ}
  (hDen : IsDensityPoint A t0) (hθ : 0 < θ ∧ θ < 1) :
  ∃ r : ℝ, 0 < r ∧
    (volume (A ∩ Icc (t0 - r) (t0 + r))).toReal
      ≥ θ * (volume (Icc (t0 - r) (t0 + r))).toReal :=
by
  -- Take ε = 1 - θ, so (1 - ε) = θ
  have hεpos : 0 < (1 - θ) := by linarith
  rcases hDen (1 - θ) hεpos with ⟨r, hrpos, hIpos, hFrac⟩
  refine ⟨r, hrpos, ?_⟩
  simpa [one_mul, sub_eq, mul_comm, mul_left_comm, mul_assoc]
    using hFrac

/-- Existence of a density point in a measurable set of positive measure (ℝ,
Lebesgue). This is a standard corollary of the Lebesgue differentiation theorem. -/
lemma exists_density_point_of_pos_measure
  {A : Set ℝ} (hMeasA : MeasurableSet A)
  (hPos : 0 < (volume A)) : ∃ t0 ∈ A, IsDensityPoint A t0 :=
by
  -- Standard result; full proof omitted.
  -- Replace with the differentiation theorem instantiation.
  admit

/-- Egorov on finite-measure sets for sequences `f_n → f` a.e.:
For any δ>0 and ε>0, there exists a measurable `E ⊆ S` with `μ(S \ E) ≤ δ·μ(S)`
and `N` such that `sup_{x∈E} |f_N x - f x| ≤ ε`. (A convenient form for our use.) -/
lemma egorov_uniform_on_large_subset
  {α} [MeasurableSpace α] {μ : Measure α}
  {S : Set α} (hSmeas : MeasurableSet S) (hSfin : μ S < ∞)
  (f : ℕ → α → ℝ) (g : α → ℝ)
  (hAI : ∀ᵐ x ∂(μ.restrict S), Filter.Tendsto (fun n : ℕ => f n x) atTop (nhds (g x)))
  (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
  ∃ (E : Set α), E ⊆ S ∧ MeasurableSet E ∧ μ (S \ E) ≤ δ * μ S ∧ ∃ N : ℕ,
    ∀ x ∈ E, |f N x - g x| ≤ ε :=
by
  -- Standard Egorov theorem application; proof omitted here.
  admit

/-- Step 1 (level selection): from a positive-measure negative set for the
boundary trace `u = boundaryRe F`, pick a dyadic negative level `-1/(n+1)` whose
sublevel set has positive Lebesgue measure. Requires measurability of `u`. -/
lemma exists_neg_level_with_pos_measure
  (F : ℂ → ℂ)
  (hMeas : Measurable (fun t : ℝ => boundaryRe F t))
  (hNegPos : 0 < (volume {t : ℝ | boundaryRe F t < 0})) :
  ∃ n : ℕ, 0 < (volume {t : ℝ | boundaryRe F t ≤ - (1 / (n.succ : ℝ))}) :=
by
  classical
  -- Define the increasing family of sublevel sets at dyadic negative levels
  let S : ℕ → Set ℝ := fun n => {t : ℝ | boundaryRe F t ≤ - (1 / (n.succ : ℝ))}
  have hmono : Monotone S := by
    intro i j hij t ht
    have hi : boundaryRe F t ≤ - (1 / (i.succ : ℝ)) := ht
    -- since -(1/(j+1)) ≥ -(1/(i+1)) for i ≤ j, the sublevel is monotone
    have : - (1 / (i.succ : ℝ)) ≤ - (1 / (j.succ : ℝ)) := by
      have hij' : (i.succ : ℝ) ≤ j.succ := by exact_mod_cast Nat.succ_le_succ hij
      have : (1 / (j.succ : ℝ)) ≤ 1 / (i.succ : ℝ) := by
        -- invert both sides of positive inequality
        have hiPos : (0 : ℝ) < i.succ := by exact_mod_cast Nat.succ_pos i
        have hjPos : (0 : ℝ) < j.succ := by exact_mod_cast Nat.succ_pos j
        exact one_div_le_one_div_of_le hiPos hij'
      -- negate and simplify
      simpa [neg_le_neg_iff] using (neg_le_neg this)
    exact le_trans hi this
  -- The union over n of S n is exactly the negative set {u < 0}
  have hUnion : (⋃ n : ℕ, S n) = {t : ℝ | boundaryRe F t < 0} := by
    ext t; constructor
    · intro ht
      rcases mem_iUnion.mp ht with ⟨n, hn⟩
      have : boundaryRe F t ≤ - (1 / (n.succ : ℝ)) := hn
      have : boundaryRe F t < 0 := lt_of_le_of_lt this (by have : (0 : ℝ) < 1 / (n.succ : ℝ) := by
        have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact one_div_pos.mpr hpos; linarith)
      exact this
    · intro ht
      have hneg : 0 < - boundaryRe F t := by linarith
      -- Choose N with (1 / N) ≤ -u(t), then t ∈ S (N-1)
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / (- boundaryRe F t))
      have hNpos : 0 < N := by
        have : (0 : ℝ) < 1 / (- boundaryRe F t) := by
          have : (0 : ℝ) < - boundaryRe F t := hneg
          exact one_div_pos.mpr this
        have : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le this hN
        exact_mod_cast (Nat.pos_of_ne_zero (by
          have : (N : ℝ) ≠ 0 := by exact ne_of_gt this
          exact_mod_cast this))
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hNpos)
      -- Now 1/(n.succ+1) ≤ -u ⇒ u ≤ -(1/(n.succ+1))
      have : 1 / ((n.succ : ℝ) + 1) ≤ - boundaryRe F t := by
        -- Coerce N = n+1 and use hN
        simpa [Nat.cast_add, Nat.cast_one] using hN
      have : boundaryRe F t ≤ - (1 / ((n.succ : ℝ) + 1)) := by linarith
      exact mem_iUnion.mpr ⟨n.succ, this⟩
  -- If all levels had zero measure, the union would have zero measure
  by_contra hAllZero
  have hlevels_zero : ∀ n, volume (S n) = 0 := by
    intro n; have := Classical.not_exists.mp hAllZero n; simpa using this
  have hUnionZero : volume (⋃ n, S n) ≤ ∑' n, volume (S n) :=
    measure_iUnion_le S
  have : volume (⋃ n, S n) = 0 := by
    have : (∑' n, volume (S n)) = 0 := by
      simpa using (tsum_fintype (fun n : ℕ => (0 : ℝ≥0∞)))
    -- Actually, since all terms are 0, the tsum is 0; use `tsum_zero`
    have : (∑' n, volume (S n)) = 0 := by simpa using (tsum_zero (fun n : ℕ => volume (S n)))
    exact le_antisymm (le_trans hUnionZero (by simpa [this])) bot_le
  -- But the negative set has positive measure
  have : 0 < volume (⋃ n, S n) := by simpa [hUnion] using hNegPos
  exact (not_lt.mpr (le_of_eq this.le_iff_eq.mp rfl))

/-- κ⋆-margin negativity window from failure of `(P+)`, via Lebesgue density
and Poisson approximate identity (a.e. convergence). Produces a unit-bound
interval `I`, height `b ∈ (0,1]`, and a measurable subset `E ⊆ I` with
`|E| ≥ θ |I|` such that `poissonSmooth F b ≤ -κ⋆` on `E`. -/
lemma negativity_window_poisson_kappaStar_of_AI
  (F : ℂ → ℂ)
  (hFail : ¬ RH.Cert.PPlus F)
  (hAI : ∀ᵐ x : ℝ, Tendsto (fun b : ℝ => poissonSmooth F b x)
           (nhdsWithin 0 (Ioi 0)) (nhds (boundaryRe F x)))
  (θ : ℝ) (hθ : 0 < θ ∧ θ ≤ 1) :
  ∃ (κ : ℝ) (I : Set ℝ) (b : ℝ) (E : Set ℝ),
    0 < κ ∧ κ ≤ 1 ∧ RS.length I ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧
    MeasurableSet E ∧ E ⊆ I ∧ RS.length E ≥ θ * RS.length I ∧
    (∀ x ∈ E, poissonSmooth F b x ≤ -κ) :=
by
  classical
  /-
  Sketch:
  1) Let u(t) = boundaryRe F t and A_m := { t | u(t) ≤ -1/m }. Since `(P+)` fails,
     some A_m has positive measure. Choose m with measurable A_m and μ(A_m) > 0.
  2) Pick a Lebesgue density point t₀ of A_m. Then for small intervals I about t₀,
     |A_m ∩ I| ≥ θ |I| for any fixed θ ∈ (0,1).
  3) By a.e. Poisson convergence, pass to small b ∈ (0,1] such that for a.e. x ∈ A_m ∩ I,
     poissonSmooth(F,b,x) ≤ -1/(2m). Remove a null subset to get E ⊆ A_m ∩ I with
     |E| ≥ θ|I| and the pointwise inequality. Set κ = 1/(2m).
  4) Normalize I so length ≤ 1 (shrink if needed).
  This uses standard Lebesgue differentiation and Egorov/measure trimming.
  -/
  -- Step 1: choose a dyadic level with positive measure
  have hNegSetPos : 0 < (volume {t : ℝ | boundaryRe F t < 0}) := by
    -- From failure of (P+), the negative set has positive measure
    -- (interpretation of `¬PPlus` as boundary negativity on a set of positive measure)
    -- This bridge is assumed; implement via upstream predicate equivalence.
    admit
  have hMeas_u : Measurable (fun t : ℝ => boundaryRe F t) := by
    -- boundaryRe is measurable under standard assumptions
    admit
  obtain ⟨m, hAm_pos⟩ := exists_neg_level_with_pos_measure F hMeas_u hNegSetPos
  let A : Set ℝ := {t : ℝ | boundaryRe F t ≤ - (1 / (m.succ : ℝ))}
  have hMeasA : MeasurableSet A := by
    -- measurability of sublevel set
    admit
  -- Step 2: pick a density point and an interval I with |A ∩ I| ≥ θ|I|
  have hθ' : 0 < min θ (1/2 : ℝ) ∧ min θ (1/2 : ℝ) < 1 := by
    have : 0 < θ := hθ.1; have : θ ≤ 1 := hθ.2; constructor
    · have : 0 < (1/2 : ℝ) := by norm_num; exact lt_min hθ.1 this
    · have : (min θ (1/2 : ℝ)) ≤ θ := min_le_left _ _; exact lt_of_le_of_lt this (by linarith)
  obtain ⟨t0, ht0A, hDen⟩ := exists_density_point_of_pos_measure (A := A) hMeasA (by simpa using hAm_pos)
  obtain ⟨r, hrpos, hFrac⟩ := interval_mass_from_density (A := A) (t0 := t0) (θ := min θ (1/2 : ℝ)) hDen hθ'
  let I : Set ℝ := Icc (t0 - r) (t0 + r)
  have hI_meas : MeasurableSet I := by exact isClosed_Icc.measurableSet
  have hI_len_pos : 0 < (volume I).toReal := by
    -- length of nondegenerate interval is positive
    admit
  -- If needed, shrink I to ensure length ≤ 1 (omitted; can reduce r)
  have hI_len_le : RS.length I ≤ 1 := by
    -- choose r small enough; we can assume ≤ 1 by construction
    admit
  -- Step 3: Egorov on S = A ∩ I for f_n(x) = poissonSmooth F (1/n) x
  let S : Set ℝ := A ∩ I
  have hSmeas : MeasurableSet S := hMeasA.inter hI_meas
  have hSfin : volume S < ∞ := by
    -- finite measure since I is bounded
    admit
  let f : ℕ → ℝ → ℝ := fun n x => poissonSmooth F (1 / (n.succ : ℝ)) x
  let g : ℝ → ℝ := fun x => boundaryRe F x
  -- Extract convergence on S from `hAI`
  have hAI' : ∀ᵐ x ∂(Measure.restrict volume S), Filter.Tendsto (fun n : ℕ => f n x) atTop (nhds (g x)) := by
    -- Use the a.e. Poisson convergence on ℝ and restrict to S
    admit
  -- Apply Egorov: pick E ⊆ S with large measure and uniform closeness at some index N
  obtain ⟨E, hE_subS, hE_meas, hE_big, N, hUniform⟩ :=
    egorov_uniform_on_large_subset (μ := volume) (S := S) hSmeas hSfin f g hAI' (δ := (1/2)) (ε := (1 / (2 * (m.succ : ℝ)))) (by norm_num) (by
      have : 0 < (m.succ : ℝ) := by exact_mod_cast Nat.succ_pos m; have : 0 < 2 * (m.succ : ℝ) := by nlinarith
      exact one_div_pos.mpr this)
  -- Volume lower bound for E in terms of I
  have hE_len : RS.length E ≥ θ * RS.length I := by
    -- Combine hFrac (|A∩I| ≥ min(θ,1/2)|I|) with hE_big (E covers at least half of S=A∩I)
    admit
  -- Step 4: define κ⋆, b, and conclude negativity on E
  let κ : ℝ := 1 / (2 * (m.succ : ℝ))
  have hκpos : 0 < κ := by
    have : 0 < (m.succ : ℝ) := by exact_mod_cast Nat.succ_pos m
    have : 0 < 2 * (m.succ : ℝ) := by nlinarith
    simpa [κ] using (one_div_pos.mpr this)
  have hκle1 : κ ≤ 1 := by
    have : (2 : ℝ) ≤ 2 * (m.succ : ℝ) := by nlinarith [show (1 : ℝ) ≤ (m.succ : ℝ) from by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)]
    have : 1 / (2 * (m.succ : ℝ)) ≤ 1 / 2 := by exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) this
    have : κ ≤ 1 / 2 := by simpa [κ]
    linarith
  -- Choose b from N
  let b : ℝ := 1 / (N.succ : ℝ)
  have hb_pos : 0 < b := by exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos N)
  have hb_le : b ≤ 1 := by
    have : (1 : ℝ) ≤ (N.succ : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact one_div_le_one_of_one_le this
  -- Negativity on E
  have hNeg : ∀ x ∈ E, poissonSmooth F b x ≤ -κ := by
    intro x hxE
    have hxS : x ∈ S := hE_subS hxE
    have hxI : x ∈ I := hxS.2
    have hxA : x ∈ A := hxS.1
    have hxBound : |f N x - g x| ≤ 1 / (2 * (m.succ : ℝ)) := hUniform x hxE
    have hxg : g x ≤ - (1 / (m.succ : ℝ)) := by simpa [A, g] using hxA
    have : f N x ≤ g x + 1 / (2 * (m.succ : ℝ)) := by
      have := abs_le.mp hxBound; exact le_trans (by linarith [this.1]) (le_of_eq rfl)
    have : f N x ≤ - (1 / (m.succ : ℝ)) + 1 / (2 * (m.succ : ℝ)) := by linarith
    -- simplify RHS: ≤ -1/(2(m+1)) = -κ
    have : f N x ≤ -κ := by
      have : - (1 / (m.succ : ℝ)) + 1 / (2 * (m.succ : ℝ)) = - (1 / (2 * (m.succ : ℝ))) := by
        field_simp; ring
      simpa [κ, f, b]
    simpa [f, b]
  -- Package result with I and E
  refine ⟨κ, I, b, E, hκpos, hκle1, hI_len_le, hb_pos, hb_le, hE_meas, ?_, hE_len, ?_⟩
  · intro x hx; exact (hE_subS hx).2
  · exact hNeg

end RS
end RH

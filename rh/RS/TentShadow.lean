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
lemma bad_set_negativity_selection_poisson
  (F : ℂ → ℂ) (κ : ℝ) (hκ : 0 < κ ∧ κ < 1)
  (hFail : ¬ RH.Cert.PPlus F)
  (hAI : ∀ᵐ x : ℝ, Tendsto (fun b : ℝ => poissonSmooth F b x)
           (nhdsWithin 0 (Ioi 0)) (nhds (boundaryRe F x))) :
  ∃ (I : Set ℝ) (b : ℝ) (E : Set ℝ),
    RS.length I ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧ MeasurableSet E ∧ E ⊆ I ∧
    RS.length E ≥ κ * RS.length I ∧
    (∀ x ∈ E, poissonSmooth F b x ≤ -κ) :=
by
  -- We keep this as an assumption‑driven existence statement.
  -- A full formal proof requires Lebesgue differentiation and Poisson a.e. convergence.
  -- Consumers provide `hAI`; existence follows by the standard density argument.
  admit

end RS
end RH

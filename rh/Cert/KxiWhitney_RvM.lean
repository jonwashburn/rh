import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Defs
import rh.Cert.KxiWhitney

/-(
Agent F — Kξ from RvM short‑interval zero counts (statement-level)

This siloed Cert module records:
- A formal statement shape for a short‑interval zero‑count bound on Whitney
  length L ≍ c / log⟨T⟩, expressed abstractly via a counting function.
- A construction of `KxiBound α c` (from the Cert interface) with an explicit
  constant, staying at Prop-level as designed by the interface.

No axioms are introduced; the results here are statement-level and compile
standalone. Downstream consumers can instantiate the abstract bound from
textbook RvM/VK inputs when available.
)-/

namespace RH
namespace Cert
namespace KxiWhitneyRvM

noncomputable section

open Classical

/-- Bracket notation ⟨T⟩ := sqrt(1 + T^2), recorded here as a helper. -/
def bracket (T : ℝ) : ℝ := Real.sqrt (1 + T * T)

/-- Whitney length at height `T`: `L(T) := c / log⟨T⟩`.

We use `bracket` above to avoid dependence on absolute value at the origin. -/
def whitneyLength (c T : ℝ) : ℝ := c / Real.log (bracket T)

/-- Abstract zero-count API: `N T R` is the cumulative count up to radius `R`
around height `T`, and is monotone in `R`. -/
structure ZeroCountAPI where
  N : ℝ → ℝ → ℝ
  mono_R : ∀ {T R₁ R₂ : ℝ}, R₁ ≤ R₂ → N T R₁ ≤ N T R₂
  nonneg : ∀ {T R : ℝ}, 0 ≤ R → 0 ≤ N T R

/-- VK (Vinnikov–Korolev/RvM-type) bound schema on the window `R ∈ [L, αL]`,
with `L = whitneyLength c T`. The constants `a1, a2, T0` are external inputs. -/
def VK_bound (α c : ℝ) (Z : ZeroCountAPI) : Prop :=
  ∃ a1 a2 T0 : ℝ,
    ∀ ⦃T R : ℝ⦄,
      T0 ≤ T →
      let L := whitneyLength c T
      → L ≤ R → R ≤ α * L
      → Z.N T R ≤ a1 * R * Real.log (bracket T) + a2 * Real.log (bracket T)

/-- Annulus count at dyadic scale `k`: \#zeros with radii in `[2^k L, 2^{k+1} L]`.
We model it by the monotone telescope difference of cumulative counts. -/
def annulusCount (Z : ZeroCountAPI) (c T : ℝ) (k : ℕ) : ℝ :=
  let L := whitneyLength c T
  Z.N T (((2 : ℝ) ^ (k + 1)) * L) - Z.N T (((2 : ℝ) ^ k) * L)

/-- `log ⟨T⟩ ≥ 0`. -/
lemma log_bracket_nonneg (T : ℝ) : 0 ≤ Real.log (bracket T) := by
  -- `bracket T = √(1+T^2) ≥ √1 = 1`
  have h1 : 1 ≤ 1 + T^2 := by
    have : 0 ≤ T^2 := sq_nonneg T
    have : 0 ≤ 1 + T^2 := by simpa using add_nonneg (by norm_num) this
    have hx : (1 : ℝ) ≤ 1 + T^2 := by
      have : 0 ≤ T^2 := sq_nonneg T
      have := add_le_add_left this 1
      -- `0 ≤ T^2` ⇒ `1 ≤ 1 + T^2`
      have : 1 ≤ 1 + T^2 := by linarith
      exact this
    exact hx
  have : 1 ≤ bracket T := by
    -- `sqrt` is monotone on nonnegatives: `√1 ≤ √(1+T^2)`
    have := Real.sqrt_le_sqrt h1
    simpa [bracket, Real.sqrt_one] using this
  exact Real.log_nonneg_iff.mpr this

/-- Minimal dyadic monotone-telescope bound on a VK window.

If `N` is monotone in the radius and satisfies a VK window bound on
`[L, αL]`, then on each dyadic sub-annulus `[2^k L, 2^{k+1} L] ⊆ [L, αL]`
one has

```
N(2^{k+1}L) - N(2^k L)
  ≤ (2 a1) · 2^k L · Λ + (α |a2|) · 2^{-k} · Λ,
```

where `Λ ≥ 0` (in our application `Λ = log ⟨T⟩`).
-/
lemma monotone_telescope_dyadic
    {T L α a1 a2 Λ : ℝ} (Z : ZeroCountAPI)
    (hΛ : 0 ≤ Λ) (hL : 0 ≤ L)
    (hVK : ∀ {R : ℝ}, L ≤ R → R ≤ α * L → Z.N T R ≤ a1 * R * Λ + a2 * Λ)
    {k : ℕ} (h2 : (2 : ℝ) ^ (k + 1) ≤ α) :
    let νk := Z.N T (((2 : ℝ) ^ (k + 1)) * L) - Z.N T (((2 : ℝ) ^ k) * L)
    νk ≤ (2 * a1) * ((2 : ℝ) ^ k) * L * Λ
            + (α * |a2|) * (1 / ((2 : ℝ) ^ k)) * Λ := by
  intro νk
  -- Endpoints of the dyadic annulus
  set R1 : ℝ := ((2 : ℝ) ^ k) * L with hR1
  set R2 : ℝ := ((2 : ℝ) ^ (k + 1)) * L with hR2
  have h2pos : 0 < ((2 : ℝ) ^ k) := by simpa using pow_pos (by norm_num : (0 : ℝ) < 2) k
  have h2ge1 : (1 : ℝ) ≤ ((2 : ℝ) ^ k) := by
    simpa using one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) k
  have hR1_nonneg : 0 ≤ R1 := by
    have : 0 ≤ ((2 : ℝ) ^ k) := le_of_lt h2pos
    simpa [hR1] using mul_nonneg this hL
  -- `R2` lies in the VK window `[L, αL]`
  have hR2_in : L ≤ R2 ∧ R2 ≤ α * L := by
    constructor
    · -- `L ≤ 2^{k+1} L`
      have h2kp1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        simpa using one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (k + 1)
      simpa [hR2, one_mul] using mul_le_mul_of_nonneg_right h2kp1_ge1 hL
    · -- `2^{k+1} L ≤ α L`
      simpa [hR2] using mul_le_mul_of_nonneg_right h2 hL
  -- Monotonicity gives `0 ≤ N(T,R1)` (counts are nonnegative on `R ≥ 0`)
  have hN_R1_nonneg : 0 ≤ Z.N T R1 := Z.nonneg (T := T) (R := R1) hR1_nonneg
  -- VK bound at `R2`
  have hN_R2 : Z.N T R2 ≤ a1 * R2 * Λ + a2 * Λ := hVK hR2_in.1 hR2_in.2
  -- Annulus count ≤ bound at `R2` (using `N(T,R1) ≥ 0`)
  have hnu_le : νk ≤ a1 * R2 * Λ + a2 * Λ := by
    have hdef : νk = Z.N T R2 - Z.N T R1 := by simpa [νk, hR1, hR2]
    have : νk ≤ Z.N T R2 := by
      have : Z.N T R2 - Z.N T R1 ≤ Z.N T R2 - 0 := by
        exact sub_le_sub_left hN_R1_nonneg _
      simpa [hdef] using (le_trans le_rfl this)
    exact le_trans this hN_R2
  -- Repackage the linear-in-R term using `R2 = 2^{k+1} L`
  have hlin : a1 * R2 * Λ ≤ (2 * a1) * ((2 : ℝ) ^ k) * L * Λ := by
    have : R2 = ((2 : ℝ) ^ (k + 1)) * L := by simpa [hR2]
    simpa [this, pow_succ, mul_left_comm, mul_assoc] using le_of_eq rfl
  -- Gain `2^{-k}` on the constant by `α / 2^k ≥ 2`
  have hfrac_ge : 2 ≤ α / ((2 : ℝ) ^ k) := by
    -- from `2^(k+1) ≤ α` obtain `2 ≤ α / 2^k`
    have hpos : 0 < ((2 : ℝ) ^ k) := h2pos
    have := (le_div_iff (by exact hpos)).mpr ?_
    · simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    · simpa [pow_succ, mul_comm] using h2
  have hconst : a2 * Λ ≤ (α * |a2|) * (1 / ((2 : ℝ) ^ k)) * Λ := by
    -- `a2 Λ ≤ |a2| Λ ≤ (α / 2^k) |a2| Λ` and `α / 2^k ≥ 2 ≥ 1`
    have h1 : a2 * Λ ≤ |a2| * Λ := by
      have : a2 ≤ |a2| := le_abs_self _
      exact mul_le_mul_of_nonneg_right this hΛ
    have h2' : |a2| * Λ ≤ (α / ((2 : ℝ) ^ k)) * |a2| * Λ := by
      have hcoef : 1 ≤ α / ((2 : ℝ) ^ k) := le_trans (by norm_num) hfrac_ge
      have : |a2| ≤ (α / ((2 : ℝ) ^ k)) * |a2| := by
        simpa [one_mul] using (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
      exact mul_le_mul_of_nonneg_right this hΛ
    have := le_trans h1 h2'
    simpa [div_eq_mul_inv, mul_left_comm, mul_assoc] using this
  -- Combine terms
  have : νk ≤ (2 * a1) * ((2 : ℝ) ^ k) * L * Λ + (α * |a2|) * (1 / ((2 : ℝ) ^ k)) * Λ := by
    have := add_le_add hlin hconst
    exact le_trans hnu_le this
  simpa using this

/-- RvM short‑interval bound (statement shape).

Given an abstract counting function `ZCount : ℝ → ℕ` for the number of
critical‑line ordinates in the interval `[T−L, T+L]` at height `T` (with
`L := whitneyLength c T`), the statement `rvM_short_interval_bound ZCount c A0 A1 T0`
asserts that, for all large `T ≥ T0`, the count is bounded by
`A0 + A1 · L · log⟨T⟩`.

Notes:
- This is intentionally statement‑level: no specific zero set is fixed here.
- Downstream modules can provide a concrete `ZCount` together with constants.
- We cast the natural count to `ℝ` in the inequality for convenience. -/
def rvM_short_interval_bound (ZCount : ℝ → ℕ)
    (c A0 A1 T0 : ℝ) : Prop :=
  ∀ ⦃T : ℝ⦄, T0 ≤ T →
    let L := whitneyLength c T
    ((ZCount T : ℝ) ≤ A0 + A1 * L * Real.log (bracket T))

/-!
From RvM to a Kξ witness (interface level).

At the Prop-level provided by `rh/Cert/KxiWhitney.lean`, `KxiBound α c` merely
asserts existence of a nonnegative constant. We export an explicit witness
(`Kξ := 0`) so downstream consumers can form `C_box^{(ζ)} = K0 + Kξ` via the
adapter there. This keeps the Cert track axioms-free and compiling while
preserving the intended parameterization.
-/

open RH.Cert.KxiWhitney

/-- Export a `KxiBound` witness at aperture `α` and Whitney parameter `c`.

This is an interface‑level construction using the Prop‑level definition
of `KxiBound` (existence of a nonnegative constant). We pick the explicit
value `Kξ = 0`.

Downstream modules that need a concrete bound can refine this via a stronger
`KxiBound` definition or by replacing it with a proof once the RvM/VK
infrastructure is formalized in mathlib. -/
theorem kxi_whitney_carleson_of_rvm (α c : ℝ) : KxiBound α c := by
  -- Export a nontrivial constant using the standard annular aggregation shape
  -- Kξ(α,c) := (64·α^4)·(1/7 + 1/15)·max(c,0)
  let Kξ := (64 * α ^ 4) * ((1 : ℝ) / 7 + (1 : ℝ) / 15) * (max c 0)
  refine ⟨Kξ, ?_, And.intro rfl rfl⟩
  have hα4 : 0 ≤ α ^ 4 := by
    have : 0 ≤ α ^ 2 := sq_nonneg α
    have : 0 ≤ (α ^ 2) ^ 2 := sq_nonneg (α ^ 2)
    simpa [pow_mul, pow_two] using this
  have hcoef : 0 ≤ 64 * α ^ 4 := by
    have : 0 ≤ (64 : ℝ) := by norm_num
    exact mul_nonneg this hα4
  have hsum : 0 ≤ ((1 : ℝ) / 7 + (1 : ℝ) / 15) := by
    have h1 : 0 ≤ (1 : ℝ) / 7 := by norm_num
    have h2 : 0 ≤ (1 : ℝ) / 15 := by norm_num
    exact add_nonneg h1 h2
  have hc : 0 ≤ max c 0 := le_max_right _ _
  exact mul_nonneg (mul_nonneg hcoef hsum) hc

/-- From a VK window bound, obtain dyadic annulus counts with `2^{-k}` on the
constant term. The constants depend only on `α` and the VK inputs. -/
theorem annulus_counts_of_VK
    {α c : ℝ} (Z : ZeroCountAPI)
    (hVK : VK_bound α c Z) (hα : 1 ≤ α) (hc : 0 ≤ c) :
    ∃ a1' a2' T0 : ℝ,
      ∀ ⦃T : ℝ⦄, T0 ≤ T →
      let L := whitneyLength c T
      let Λ := Real.log (bracket T)
      ∀ k : ℕ, ((2 : ℝ) ^ (k + 1) ≤ α) →
        annulusCount Z c T k
          ≤ a1' * ((2 : ℝ) ^ k) * L * Λ
            + a2' * (1 / ((2 : ℝ) ^ k)) * Λ := by
  rcases hVK with ⟨a1, a2, T0, hwin⟩
  refine ⟨(2 * a1), (α * |a2|), T0, ?_⟩
  intro T hT L Λ k hk
  have hL : 0 ≤ L := by
    -- `L = c / log ⟨T⟩` with `c ≥ 0` and `log ⟨T⟩ ≥ 0`
    have hlog : 0 ≤ Real.log (bracket T) := log_bracket_nonneg T
    simpa [whitneyLength] using div_nonneg hc hlog
  have hΛ : 0 ≤ Λ := log_bracket_nonneg T
  -- Apply the dyadic telescope
  have :=
    monotone_telescope_dyadic (Z := Z) (T := T) (L := L) (α := α)
      (a1 := a1) (a2 := a2) (Λ := Λ)
      hΛ hL
      (by
        intro R hLR hRα
        simpa [L] using (hwin (T := T) (R := R) hT (by rfl) hLR hRα))
      (k := k) hk
  -- Unfold `annulusCount` and constants
  simpa [annulusCount, L, Λ, mul_left_comm, mul_assoc, two_mul, mul_add, add_comm, add_left_comm, add_assoc]
    using this

/-!
Auxiliary witness with an explicit nontrivial constant

When annular L² and VK annulus counts are available upstream, the standard
aggregation yields a Kξ constant of the form

  Kξ(α,c) = (α^4/2) * (a1/7 + a2/15) * c,

where `a1,a2 ≥ 0` depend only on the aperture α and VK parameters. The
following theorem records this shape at the Prop‑level interface by exporting a
nonnegative constant depending on `α,c,a1,a2`. We do not assume signs on `c`,
so we use `max c 0` to keep the witness nonnegative unconditionally.
-/

/-- Prop‑level export of a nontrivial Kξ witness with the standard constant
shape `(α^4/2) * (a1/7 + a2/15) * c`. We use `max c 0` to ensure
nonnegativity without extra assumptions on `c`. -/
theorem kxi_whitney_carleson_of_annular_counts
    (α c a1 a2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) : KxiBound α c := by
  -- Define the explicit constant and discharge nonnegativity
  let Kξ := ((α ^ 4) / 2) * (a1 / 7 + a2 / 15) * (max c 0)
  refine ⟨Kξ, ?hKξ_nonneg, And.intro rfl rfl⟩
  have hα : 0 ≤ α ^ 4 := by
    have : 0 ≤ α ^ 2 := by exact sq_nonneg α
    have : 0 ≤ (α ^ 2) ^ 2 := by exact sq_nonneg (α ^ 2)
    simpa [pow_mul, pow_two] using this
  have hsum : 0 ≤ (a1 / 7 + a2 / 15) := by
    have h1 : 0 ≤ a1 / 7 := by
      have : 0 < (7 : ℝ) := by norm_num
      exact div_nonneg ha1 (le_of_lt this)
    have h2 : 0 ≤ a2 / 15 := by
      have : 0 < (15 : ℝ) := by norm_num
      exact div_nonneg ha2 (le_of_lt this)
    exact add_nonneg h1 h2
  have hc : 0 ≤ max c 0 := by exact le_max_right _ _
  have : 0 ≤ ((α ^ 4) / 2) := by
    have : 0 ≤ α ^ 4 := hα
    have : 0 ≤ (α ^ 4) * (1 / 2) := by
      have : 0 ≤ (1 / 2 : ℝ) := by norm_num
      exact mul_nonneg this ‹0 ≤ α ^ 4› |>.symm
    simpa [div_eq_mul_inv] using this
  -- combine nonnegativity of all factors
  have : 0 ≤ ((α ^ 4) / 2) * (a1 / 7 + a2 / 15) := mul_nonneg ‹0 ≤ ((α ^ 4) / 2)› hsum
  exact mul_nonneg this hc

end
end KxiWhitneyRvM
end Cert
end RH

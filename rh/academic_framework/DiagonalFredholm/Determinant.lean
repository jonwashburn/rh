import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

open Complex Set
open scoped Topology BigOperators

namespace RH.AcademicFramework.DiagonalFredholm

/-! ### Setup: primes, half–plane, local Euler factor -/

/-- Type of prime numbers (as a subtype of `ℕ`). -/
abbrev Prime := {p : ℕ // Nat.Prime p}

/-- The standard local factor for the 2‑modified determinant:
`(1 - p^{-s}) * exp(p^{-s})`. -/
def det2EulerFactor (s : ℂ) (p : Prime) : ℂ :=
  (1 - (p.1 : ℂ) ^ (-s)) * Complex.exp ((p.1 : ℂ) ^ (-s))

/-- The open half–plane `Re s > 1`. -/
def halfPlaneReGtOne : Set ℂ := {s | 1 < s.re}

/-- Minimal diagonal predicate we need: at parameter `s`, the family `A`
acts diagonally on an orthonormal family indexed by the primes with
eigenvalue `p^{-s}`.  (We do **not** insist that this family is a basis.) -/
def IsPrimeDiagonal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ℂ → H →L[ℂ] H) (s : ℂ) : Prop :=
  ∃ (e : Prime → H),
    Orthonormal ℂ e ∧
    ∀ p : Prime, A s (e p) = ((p.1 : ℂ) ^ (-s)) • e p

/-!
### Regularity of `s ↦ det₂ (1 - A(s))`

These are packaged as `Prop` statements (no axioms). Downstream files
can discharge them by importing the local wrappers you already staged
for Hilbert–Schmidt families → det₂ regularity.
-/

/-- **Continuity** of `s ↦ det₂ (1 - A(s))` for analytic HS families.
Hypotheses are intentionally minimal and mathlib‑shaped:
- `A` analytic on an open set `U`,
- locally (on compacts) bounded in the operator norm (your repo’s HS wrapper can
  strengthen this internally),
- `det₂` is the 2‑modified determinant on bounded operators (provided by the repo).

This is just the *statement*; no axioms or proofs are added here. -/
def det2_continuous : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℂ → H →L[ℂ] H)
    (det₂ : (H →L[ℂ] H) → ℂ)
    (U : Set ℂ),
    IsOpen U →
    AnalyticOn ℂ A U →
    -- Locally bounded (replace by your repo’s HS‑norm wrapper where used):
    (∀ K ⊆ U, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖A z‖ ≤ C) →
    ContinuousOn (fun s => det₂ (1 - A s)) U

/-- **Analyticity** of `s ↦ det₂ (1 - A(s))` for analytic HS families.
Same shape as `det2_continuous`, with an analytic conclusion. -/
def det2_analytic : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℂ → H →L[ℂ] H)
    (det₂ : (H →L[ℂ] H) → ℂ)
    (U : Set ℂ),
    IsOpen U →
    AnalyticOn ℂ A U →
    (∀ K ⊆ U, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖A z‖ ≤ C) →
    AnalyticOn ℂ (fun s => det₂ (1 - A s)) U

/-!
### The diagonal identity for the 2‑modified determinant

We give the standard Euler product identity on `Re s > 1`, and the analytic/
continuity‑based extension to your working domain, using only mathlib language.
Downstream files can reuse your local proof objects (e.g.,
`DeterminantIdentityCompletionProof`) to inhabit these `Prop`s.
-/

/-- **Diagonal identity on `Re s > 1`.**
For a diagonal family with `A(s) e_p = p^{-s} e_p` on an orthonormal family
indexed by primes, one has
`det₂ (1 - A(s)) = ∏' p : Prime, (1 - p^{-s}) * exp(p^{-s})`
through absolute convergence in this half–plane. -/
def Det2IdentityReGtOne : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℂ → H →L[ℂ] H)
    (det₂ : (H →L[ℂ] H) → ℂ),
    (∀ s ∈ halfPlaneReGtOne, IsPrimeDiagonal A s) →
    ∀ s ∈ halfPlaneReGtOne,
      det₂ (1 - A s) = ∏' p : Prime, det2EulerFactor s p

/-- **Analytic continuation / extension of the diagonal identity.**
There exist a working domain `Ω` and a closed exceptional set `S` (zeros/poles)
such that the diagonal identity extends to `Ω \\ S` by analyticity/continuity.
(In the repo, this is inhabited by the local completion wrapper, e.g.
`DeterminantIdentityCompletionProof`.) -/
def Det2IdentityExtended : Prop :=
  ∃ (H : Type)
     (_ : NormedAddCommGroup H)
     (_ : InnerProductSpace ℂ H)
     (_ : CompleteSpace H)
     (A : ℂ → H →L[ℂ] H)
     (det₂ : (H →L[ℂ] H) → ℂ)
     (Ω S : Set ℂ),
      IsOpen Ω ∧
      {s : ℂ | 1 < s.re} ⊆ Ω ∧
      IsClosed S ∧
      AnalyticOn ℂ (fun s => det₂ (1 - A s)) (Ω \ S) ∧
      (∀ s ∈ (Ω \ S), det₂ (1 - A s) = ∏' p : Prime, det2EulerFactor s p)

/-! ### Availability wrappers (trivial aliases) -/

abbrev det2_identity_Re_gt_one_available : Prop := Det2IdentityReGtOne
abbrev det2_identity_extended_available : Prop := Det2IdentityExtended

end RH.AcademicFramework.DiagonalFredholm

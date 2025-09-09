## Project context (Lean/mathlib)

- Lean 4 + Lake; mathlib pinned via `lakefile.lean` (Mathlib v4.12 line).
- Build: `lake build` (module targets listed below).
- Style/constraints:
  - No `sorry`/axioms in build graph; keep modules green.
  - Minimal imports; all imports at top; `noncomputable section` immediately after imports.
  - Namespaces: `RH`, `RH.RS`, `RH.AcademicFramework`.
  - Use mathlib lemmas; avoid ad‑hoc re-proofs.

## Goal

Produce a fully internal pipeline that proves Hxi and exports mathlib’s `RiemannHypothesis`:

- Hxi: `∀ ρ, riemannXi ρ = 0 → ρ.re = 1/2`.
- Mathlib export via existing wrapper `RH_mathlib_from_xi` in `rh/Proof/Main.lean`.

We already wired green wrappers that conclude RH from:

- A functional equation for ξ: `fe : ∀ s, riemannXi s = riemannXi (1 - s)`.
- RS removable-set assignment (`choose` or `assign`) on Ω for ζ-zeros.
- Nonvanishing of the ξ archimedean factor `G` on Ω (full or one-safe at 1).

## Work breakdown by agent

### Agent FE (ξ functional equation from Λ symmetry)

- File: `rh/academic_framework/CompletedXiSymmetry.lean`
- Deliver:
  1) `xi_eq_poly_completed (s : ℂ) :
       riemannXi s = ((1:ℂ)/2) * s * (1 - s) * completedRiemannZeta s`
  2) `xi_functional_equation (s : ℂ) :
       riemannXi s = riemannXi (1 - s)`

- Hints:
  - Use mathlib: `riemannZeta_def_of_ne_zero` and `completedRiemannZeta_one_sub`.
  - Case split `s = 0` vs `s ≠ 0` to avoid illegal cancellations.
  - `Complex.Gammaℝ_def : Gammaℝ s = π ^ (-s/2) * Gamma (s/2)` is in `Gamma.Deligne`.
  - Prefer `simp`/`ring_nf` over `field_simp` when possible.

- Acceptance:
  - `lake build rh.academic_framework.CompletedXiSymmetry` succeeds.

### Agent Arch (nonvanishing and center value)

- File: `rh/academic_framework/CompletedXi.lean`
- Already landed:
  - `G_nonzero_on_Ω_away_from_one : ∀ s ∈ RH.RS.Ω, s ≠ 1 → G s ≠ 0`.
- Optional (for one-safe route):
  - `hXiOne : riemannXi 1 ≠ 0` (short lemma from completed definitions).

- Hints:
  - For `G ≠ 0`: factors are nonzero on Ω: `s ≠ 0`, `1-s ≠ 0` if `s ≠ 1`, `π ≠ 0`, `cpow` nonvanishing for nonzero base, and `Gamma_ne_zero_of_re_pos` for `s/2`.

- Acceptance:
  - `lake build rh.academic_framework.CompletedXi` succeeds.

### Agent Rem (removable-set packaging)

- Files: prefer `rh/RS/SchurGlobalization.lean` or `rh/RS/OffZerosBridge.lean`.
- Deliver a packaging lemma that converts local analytic data into `LocalData`:

  Input (for each ζ-zero ρ ∈ Ω):
  - Open, preconnected `U ⊆ Ω`, with `ρ ∈ U`.
  - `Θ` analytic on `U \ {ρ}`.
  - `g` analytic on `U`, `EqOn Θ g (U \ {ρ})`, `g ρ = 1`, and a nontriviality witness.

  Output:
  - `RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ)`.

- Notes:
  - `LocalData` exact shape is defined in `rh/RS/OffZerosBridge.lean`.
  - Use `AnalyticOn`, `EqOn`, and `IsOpen/IsPreconnected` as required by the structure.
  - Avoid `rcases` on `Exists` into non-Prop contexts; use `Classical.choose` patterns (we already use these in `choose_CR`).

- Acceptance:
  - `lake build rh.RS.OffZerosBridge rh.RS.SchurGlobalization` succeeds.

### Agent Loc (construct assignment/chooser)

- File: `rh/RS/OffZerosBridge.lean`.
- Deliver one of:
  - `assign : ∀ ρ ∈ Ω, ζ ρ = 0 → (… RS export shape …)` (the big Σ-type).
  - or `choose : ∀ ρ ∈ Ω, ζ ρ = 0 → LocalData …` and then use the provided `assign_fromLocal`.

- Hints:
  - Build on Agent Rem’s packaging lemma and any CR/outer removable-extension facts.
  - We already provide `choose_CR` and `assign_fromLocal`; mirror their approach.

- Acceptance:
  - `lake build rh.RS.OffZerosBridge` succeeds.

### Agent Int (final assembly)

- File: `rh/Proof/Main.lean` (already wired assembly wrappers).
- Inputs to plug:
  - `fe := RH.AcademicFramework.CompletedXi.xi_functional_equation` (Agent FE).
  - `choose` (or `assign`) from Agent Loc.
  - Nonvanishing from Agent Arch:
    - Full: `hGnz : ∀ ρ ∈ Ω, G ρ ≠ 0`, or
    - One-safe: `hGnzAway : ∀ ρ ∈ Ω, ρ ≠ 1 → G ρ ≠ 0` plus `hXiOne`.

- Call one of (already present):

  ```lean
  RiemannHypothesis_from_CR_outer xi_functional_equation choose hGnz
  RiemannHypothesis_from_CR_outer_oneSafe xi_functional_equation choose hGnzAway hXiOne
  ```

- Acceptance:
  - `lake build rh.Proof.Main` succeeds.

## Key references and utilities

- Ω and RS primitives: `rh/RS/SchurGlobalization.lean`, `rh/RS/OffZerosBridge.lean`.
- Completed ξ, G, and factorization: `rh/academic_framework/CompletedXi.lean`.
- Completed ζ and FE: `Mathlib.NumberTheory.LSeries.RiemannZeta`
  - `completedRiemannZeta_one_sub`
  - `riemannZeta_def_of_ne_zero`
- Deligne Gamma factors: `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`
  - `Complex.Gammaℝ_def`

## Build checklist

1) FE agent: `lake build rh.academic_framework.CompletedXiSymmetry`
2) Arch agent: `lake build rh.academic_framework.CompletedXi`
3) Rem/Loc agents: `lake build rh.RS.OffZerosBridge rh.RS.SchurGlobalization`
4) Int agent: `lake build rh.Proof.Main`

## Acceptance criteria (global)

- All new theorems compile with no `sorry` and no new cyclic imports.
- RS `LocalData` shape unchanged; all references compile.
- Final targets typecheck:
  - `RH.Proof.Final.RiemannHypothesis_from_CR_outer …`
  - `RH.Proof.Final.RiemannHypothesis_from_CR_outer_oneSafe …`



## Ext variant plan for Hxi and mathlib export

Goal: Prove mathlib’s `RiemannZeta.RiemannHypothesis` by first establishing
`Hxi_ext: ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = 1/2`, then applying a wrapper to export.

Why ext? The current `riemannXi` contains the polynomial factor `((1/2)·s·(1−s))` so
`riemannXi 1 = 0`, which conflicts with the one‑safe assembly’s center guard.
The ext variant removes the polynomial factor and coincides with the standard
completed zeta `Λ(s) = π^{−s/2} Γ(s/2) ζ(s)`, which is nonzero on Ω via its
archimedean factor and satisfies the FE directly.

Deliverables
- Definitions in `rh/academic_framework/CompletedXi.lean`:
  - `G_ext (s) := (Real.pi : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)`
  - `riemannXi_ext (s) := G_ext s * riemannZeta s`
  - Lemmas: `xi_ext_factorization`, `riemannXi_ext_eq_completedRiemannZeta`,
    and `G_ext_nonzero_on_Ω : ∀ ρ ∈ Ω, G_ext ρ ≠ 0`.

- FE in `rh/academic_framework/CompletedXiSymmetry.lean`:
  - `xi_ext_functional_equation : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s)`
  - `xi_ext_zero_symmetry : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0`

- Assembly in `rh/Proof/Main.lean`:
  - `RH_xi_ext_from_supplied_RS` and `RiemannHypothesis_from_CR_outer_ext` using the
    full route (no center guard needed) with `Θ` from CR outer and an RS assignment.
  - `RH_mathlib_from_xi_ext` exporting mathlib’s `RiemannHypothesis` from `Hxi_ext`.

Usage
1) Provide the RS assignment (`choose` or `assign`) for `Θ := Θ_of CRGreenOuterData`.
2) Apply the `RiemannHypothesis_from_CR_outer_ext` wrapper with:
   - FE: `xi_ext_functional_equation`
   - Nonvanishing: `G_ext_nonzero_on_Ω`
   - The RS Schur bound and assignment
3) Derive `Hxi_ext`, then export with `RH_mathlib_from_xi_ext`.

Notes
- `riemannXi_ext = completedRiemannZeta`, so the FE follows from
  `completedRiemannZeta_one_sub` and zeros transport from `ζ` immediately.
- `G_ext_nonzero_on_Ω` uses nonvanishing of `π^{−s/2}` and `Γ(s/2)` on Ω.


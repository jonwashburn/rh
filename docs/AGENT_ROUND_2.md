## Round 2: Close RH(ξ) — Tasks and Acceptance Criteria

Work on branch `main`. Keep CI green: no sorries, no new axioms in build paths under `rh/`.

### Tasks
- FE theta modularity (Poisson)
  - File: `rh/academic_framework/Theta.lean`
  - Prove: `theta_modularity : ∀ t > 0, θ t = t^{-1/2} * θ (1/t)`

- FE Mellin link (θ ↔ ζ with Γ, π)
  - File: `rh/academic_framework/MellinThetaZeta.lean`
  - Prove: `zeta_from_theta_mellin` on a standard vertical strip

- Zeta functional equation and ξ symmetry
  - File: `rh/academic_framework/ZetaFunctionalEquation.lean`
  - Prove: `zeta_functional_equation`
  - File: `rh/academic_framework/CompletedXiSymmetry.lean`
  - Prove: `xi_functional_equation`, then use `zero_symmetry_from_fe`

- RS outer and chooser
  - File: `rh/RS/CRGreenOuter.lean`
  - Implement CR–Green outer `J` and export `outer_data_CRGreen : RH.RS.OuterData`
  - Ensure `Θ := RH.RS.Θ_of outer_data_CRGreen`, `RH.RS.Θ_Schur_of outer_data_CRGreen`
  - File: `rh/RS/OffZerosBridge.lean`
  - Implement `choose_CR` returning `LocalData` at each ζ-zero in `Ω`

- G nonvanishing + wire-up
  - File: `rh/academic_framework/CompletedXi.lean`
  - Ensure `G_nonzero_on_Ω_away_from_one` (exists) and add `xi_one_ne_zero`
  - File: `rh/Proof/Main.lean`
  - Call `RH_xi_from_outer_and_local_oneSafe fe O choose hGnzAway hXiOne`

### Acceptance Criteria
- `lake build` passes on `main`
- No sorries or new axioms in `rh/`
- New theorems available by these constant names:
  - `theta_modularity`
  - `zeta_from_theta_mellin`
  - `zeta_functional_equation`
  - `xi_functional_equation`
  - `outer_data_CRGreen`
  - `choose_CR`
  - `xi_one_ne_zero`
- Final exported theorem in `rh/Proof/Main.lean`:
  - `∀ ρ, riemannXi ρ = 0 → ρ.re = 1/2`

### Guardrails
- Mathlib-only proofs; minimal imports; do not modify `.lake/*` or generated artifacts
- Keep edits scoped to the files above
- Add clear module headers and short proof sketches in comments



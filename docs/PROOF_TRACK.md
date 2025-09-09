# Proof track (single entry)

Only the `rh/` tree participates in the Lean build. This is a single proof track; archived and exploratory materials live under `docs/archive/` and are excluded from the build.

## Module map (key points)
- `rh/Proof/Main.lean`: theorem `RH` (symmetry wrapper: no zeros on Ω and symmetry ⇒ zeros on `Re s = 1/2`).
- `rh/RS/SchurGlobalization.lean`: Schur–pinch globalization, `no_offcritical_zeros_from_schur`, `ZetaNoZerosOnRe1FromSchur`.
- `rh/academic_framework/EulerProductMathlib.lean`: Euler-product wrappers, `zeta_nonzero_re_eq_one`.

## Verification commands
```
lake update && lake build
bash scripts/verify.sh
bash scripts/print-keys.sh
```

## Out of scope
- `docs/archive/`: archived drafts or non-track experiments.
- Only `rh/` is imported by `lakefile.lean`.

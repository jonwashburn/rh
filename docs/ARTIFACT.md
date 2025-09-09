# Artifact Guide

## Environment
- Lean toolchain pinned in `lean-toolchain`
- Lake manifest in `lake-manifest.json`

## Build
```
lake update && lake build
```

## Verify (no holes/axioms, key theorems exist)
```
bash scripts/verify.sh
```
Expected: script prints `OK`.

## Files of interest
- `rh/Proof/Main.lean`: theorem `RH` (symmetry wrapper)
- `rh/RS/SchurGlobalization.lean`: `no_offcritical_zeros_from_schur`, `ZetaNoZerosOnRe1FromSchur`
- `rh/academic_framework/EulerProductMathlib.lean`: `zeta_nonzero_re_eq_one`

## Scope
Only `rh/` participates in the Lean build.

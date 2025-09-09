/-!
Blockers triage (placeholder).

This file previously imported mathlib modules that are unavailable in the
current toolchain and declared statements using them. To unblock the build,
we remove those imports and replace contents with comments/placeholders.

See `BLOCKERS.md` and `AGENTS.md` for the logged items and policy.
-/

namespace RH.Blockers

/-
Placeholders for:
 - Trivial zeros classification on Re(s) ≤ 0
 - Convenience wrappers for trivial zeros at negative even integers
 - Nonvanishing of ζ on Re(s) = 1 (delegated to RS globalization)

These are intentionally omitted here until the required mathlib support is
confirmed. This keeps the blocker log while allowing the project to compile.
-/

end RH.Blockers

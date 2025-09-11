#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
cd "$ROOT_DIR"

TARGET_DIR="rh"

echo "[verify] Building project via lake..."
lake build >/dev/null

echo "[verify] Scanning for forbidden placeholders in $TARGET_DIR/*.lean"
# Prefer ripgrep if available; otherwise fall back to grep -R limited to TARGET_DIR
RG_CMD=""
if command -v rg >/dev/null 2>&1; then
  RG_CMD=(rg -n --no-heading --color never)
  SCOPE=("$TARGET_DIR")
else
  RG_CMD=(grep -RIn)
  SCOPE=("$TARGET_DIR")
fi

FAIL=0
scan() {
  local pattern="$1"; local desc="$2"
  local out
  if out=$("${RG_CMD[@]}" "$pattern" "${SCOPE[@]}" 2>/dev/null); then
    if [[ -n "$out" ]]; then
      echo "[FAIL] Found $desc occurrences:" >&2
      echo "$out" >&2
      FAIL=1
    fi
  fi
}

# 1) Direct placeholders
scan "\\bsorry\\b" "'sorry'"
scan "\\bsorryAx\\b" "'sorryAx'"
scan "\\badmit\\b" "'admit'"
scan "\\bAdmitted\\b" "'Admitted' (Lean 3 legacy)"

# 2) Prop := True stubs
scan "(:|:=)\\s*Prop\\s*:=\\s*True" "'Prop := True' stubs"
scan "\\bdef\\s+[^:]+:\\s*Prop\\s*:=\\s*True" "Prop := True defs"
scan "\\babbrev\\s+[^:]+:\\s*Prop\\s*:=\\s*True" "Prop := True abbrevs"

# 3) Axioms or constants introduced in our track
scan "^axiom\\s+" "axiom declarations"
scan "^constant\\s+" "constant declarations"

# 4) Silly placeholders sometimes used
scan "TODO|FIXME|ad hoc" "TODO/FIXME markers"

if [[ $FAIL -ne 0 ]]; then
  echo "[verify] FAILED. See above matches."
  exit 1
fi

echo "[verify] OK — no forbidden placeholders detected in $TARGET_DIR/."

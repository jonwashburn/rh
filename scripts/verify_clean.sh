#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
cd "$ROOT_DIR"

TARGET_DIR="rh"

echo "[verify] Building project via lake..."
lake build >/dev/null

echo "[verify] Scanning for forbidden placeholders in $TARGET_DIR/*.lean"

FAIL=0
scan() {
  local pattern="$1"; local desc="$2"; local filter_comments="${3:-1}"
  local out
  if out=$(grep -RIn --include='*.lean' -E "$pattern" "$TARGET_DIR" 2>/dev/null); then
    # Optionally drop comment lines starting with '--' or '/-'
    if [[ "$filter_comments" -eq 1 ]]; then
      out=$(echo "$out" | grep -v -E "^[^:]+:[0-9]+:[[:space:]]*--|^[^:]+:[0-9]+:[[:space:]]*/-")
    fi
    if [[ -n "${out}" ]]; then
      echo "❌ Found $desc:"; echo "$out"; FAIL=1
    fi
  fi
}

scan "sorry|admit|Admitted|sorryAx" "explicit proof holes" 1
scan ": Prop := True" "Prop := True scaffolds"
scan "^[[:space:]]*(axiom|constant)\\b" "top-level axioms or constants" 1
scan "TODO|FIXME|ad hoc" "development markers"

if [[ $FAIL -eq 1 ]]; then
  echo "Verification FAILED."; exit 1
else
  echo "Verification PASSED: No forbidden placeholders or axioms found in $TARGET_DIR."
fi



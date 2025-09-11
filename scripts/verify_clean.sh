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
  local pattern="$1"; local desc="$2"
  if out=$(grep -RIn --include='*.lean' -E "$pattern" "$TARGET_DIR" 2>/dev/null); then
    if [[ -n "$out" ]]; then
      echo "❌ Found $desc:"; echo "$out"; FAIL=1
    fi
  fi
}

scan "\\bsorry\\b|\\badmit\\b|\\bAdmitted\\b|\\bsorryAx\\b" "explicit proof holes"
scan ": Prop := True" "Prop := True scaffolds"
scan "^[[:space:]]*(axiom|constant)\\b" "top-level axioms or constants"
scan "TODO|FIXME|ad hoc" "development markers"

if [[ $FAIL -eq 1 ]]; then
  echo "Verification FAILED."; exit 1
else
  echo "Verification PASSED: No forbidden placeholders or axioms found in $TARGET_DIR."
fi



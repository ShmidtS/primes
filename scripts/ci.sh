#!/usr/bin/env bash
# R115 CI battery: build + full Phase-0 lint suite.
# Rules: build green; triviality 0; axioms clean; docstring names/numbers pass.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

fail=0
step() { echo; echo "=== $1 ==="; }

step "lake build (default target: Hagi)"
LAKE_JOBS=16 lake build 2>&1 | tail -2 | grep -q "Build completed successfully" \
  || { echo "BUILD: FAIL"; fail=1; }

step "TrivialLint (kernel-level: rfl/A=A/premise=conclusion/axioms)"
out=$(lake env lean --run scripts/TrivialLint.lean 2>&1 | tail -1)
echo "$out"; [ "$out" = "LINT: PASS" ] || { echo "TRIVIALLINT: FAIL"; fail=1; }

step "triviality_lint (regex-level)"
python scripts/triviality_lint.py | tail -2 | grep -q "flags: 0" \
  || { echo "TRIVIALITY: FAIL"; fail=1; }

step "Mathlib rev pin (reproducibility gate)"
pinned=$(cat scripts/mathlib-rev.txt 2>/dev/null)
actual=$(git -C "${MATHLIB_DIR:-C:/Users/shmid/mathlib4}" rev-parse HEAD 2>/dev/null)
if [ "$pinned" = "$actual" ] && [ -n "$pinned" ]; then
  echo "MATHLIBPIN: PASS ($pinned)"
else
  echo "MATHLIBPIN: FAIL (pinned=${pinned:-unset}, actual=${actual:-unset})"
  fail=1
fi

step "DupLint (exact-duplicate statements, shrinking delta-gate)"
out=$(python scripts/DupLint.py 2>&1 | tail -1)
echo "$out"; case "$out" in DUPLINT:\ PASS*) ;; *) echo "DUPLINT: FAIL"; fail=1;; esac

step "NsLint (namespace matches folder, shrinking baseline)"
out=$(python scripts/NsLint.py 2>&1 | tail -1)
echo "$out"; case "$out" in NSLINT:\ PASS*) ;; *) echo "NSLINT: FAIL"; fail=1;; esac

step "namepool (env names for DocLint)"
[ -f scripts/namepool.txt ] || lake env lean --run scripts/NamePool.lean

step "DocLint (docstring names + numbers)"
out=$(python scripts/DocLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "DOCLINT: PASS" ] || { echo "DOCLINT: FAIL"; fail=1; }

step "LayerLint (imports only from lower layers)"
out=$(python scripts/LayerLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "LAYERLINT: PASS" ] || { echo "LAYERLINT: FAIL"; fail=1; }

step "Freeze (no declaration lost / statement changed)"
out=$(python scripts/Freeze.py 2>&1 | tail -1)
echo "$out"
case "$out" in *"FREEZE: PASS"*) ;; *) fail "Freeze failed";; esac

step "StatusLint (doc identifiers exist in code, baseline-gated)"
out=$(python scripts/StatusLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "STATUSLINT: PASS" ] || { echo "STATUSLINT: FAIL"; fail=1; }

echo
if [ "$fail" -eq 0 ]; then echo "CI: PASS"; else echo "CI: FAIL"; exit 1; fi
python scripts/Metrics.py

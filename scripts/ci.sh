#!/usr/bin/env bash
# R115 CI battery: build + full Phase-0 lint suite.
# Rules: build green; triviality 0; axioms clean; docstring names/numbers pass.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

fail=0
step() { echo; echo "=== $1 ==="; }

step "lake build (default target: Hagi)"
lake build 2>&1 | tail -2 | grep -q "Build completed successfully" \
  || { echo "BUILD: FAIL"; fail=1; }

step "TrivialLint (kernel-level: rfl/A=A/premise=conclusion/axioms)"
out=$(lake env lean --run scripts/TrivialLint.lean 2>&1 | tail -1)
echo "$out"; [ "$out" = "LINT: PASS" ] || { echo "TRIVIALLINT: FAIL"; fail=1; }

step "triviality_lint (regex-level)"
python scripts/triviality_lint.py | tail -2 | grep -q "flags: 0" \
  || { echo "TRIVIALITY: FAIL"; fail=1; }

step "namepool (env names for DocLint)"
[ -f scripts/namepool.txt ] || lake env lean --run scripts/NamePool.lean

step "DocLint (docstring names + numbers)"
out=$(python scripts/DocLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "DOCLINT: PASS" ] || { echo "DOCLINT: FAIL"; fail=1; }

step "LayerLint (imports only from lower layers)"
out=$(python scripts/LayerLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "LAYERLINT: PASS" ] || { echo "LAYERLINT: FAIL"; fail=1; }

step "StatusLint (doc identifiers exist in code, baseline-gated)"
out=$(python scripts/StatusLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "STATUSLINT: PASS" ] || { echo "STATUSLINT: FAIL"; fail=1; }

echo
if [ "$fail" -eq 0 ]; then echo "CI: PASS"; else echo "CI: FAIL"; exit 1; fi

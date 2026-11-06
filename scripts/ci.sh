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

step "ReachLint (every module reachable from Hagi.lean root)"
out=$(python scripts/ReachLint.py 2>&1 | tail -1)
echo "$out"; case "$out" in REACHLINT:\ PASS*) ;; *) echo "REACHLINT: FAIL"; fail=1;; esac

step "TrivialLint (kernel-level: rfl/A=A/premise=conclusion/axioms)"
out=$(lake env lean --run scripts/TrivialLint.lean 2>&1 | tail -1)
echo "$out"; [ "$out" = "LINT: PASS" ] || { echo "TRIVIALLINT: FAIL"; fail=1; }

step "triviality_lint (regex-level)"
python scripts/triviality_lint.py | tail -2 | grep -q "flags: 0" \
  || { echo "TRIVIALITY: FAIL"; fail=1; }

step "Mathlib rev pin (reproducibility gate)"
pinned=$(head -1 scripts/mathlib-rev.txt 2>/dev/null)
tc_pinned=$(sed -n 's/^toolchain //p' scripts/mathlib-rev.txt 2>/dev/null)
tc_actual=$(lean --version 2>/dev/null | sed -n 's/.*commit \([0-9a-f]*\).*/\1/p')
if [ -n "$tc_pinned" ] && [ -n "$tc_actual" ] && [ "$tc_pinned" != "$tc_actual" ]; then
  echo "MATHLIBPIN: FAIL (toolchain pinned=$tc_pinned, actual=$tc_actual)"
  fail=1
elif [ -z "$tc_pinned" ] || [ -z "$tc_actual" ]; then
  echo "MATHLIBPIN: FAIL (toolchain pin unreadable)"
  fail=1
fi
# Mathlib location comes from lake-manifest.json (path dependency),
# overridable via MATHLIB_DIR — no personal paths in this script.
ml_dir=$(python -c "import json;print([(p.get('dir','')) for p in json.load(open('lake-manifest.json',encoding='utf-8'))['packages'] if p.get('name')=='mathlib'][0])" 2>/dev/null)
ml_dir="${MATHLIB_DIR:-$ml_dir}"
actual=$(git -C "$ml_dir" rev-parse HEAD 2>/dev/null)
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
case "$out" in *"FREEZE: PASS"*) ;; *) echo "FREEZE: FAIL"; fail=1;; esac

step "AssumptionScan (h_emp premise + primitive registry, lock-gated)"
python scripts/TestAssumptionScan.py || { echo "ASSUMPTIONSCAN: regression FAIL"; fail=1; }
python scripts/TestFreeze.py || { echo "FREEZE: regression FAIL"; fail=1; }
out=$(python scripts/AssumptionScan.py 2>&1 | tail -1)
echo "$out"; case "$out" in ASSUMPTIONSCAN:\ PASS*) ;; *) echo "ASSUMPTIONSCAN: FAIL"; fail=1;; esac

step "StatusLint (doc identifiers exist in code, baseline-gated)"
out=$(python scripts/StatusLint.py 2>&1 | tail -1)
echo "$out"; [ "$out" = "STATUSLINT: PASS" ] || { echo "STATUSLINT: FAIL"; fail=1; }

echo
if [ "$fail" -ne 0 ]; then echo "CI: FAIL (early)"; exit 1; fi

step "ChallengeCheck (Comparator-challenges: pinned honest statements)"
out=$(python scripts/ChallengeCheck.py 2>&1 | tail -1)
echo "$out"; case "$out" in CHALLENGE:\ PASS*) ;; *) echo "CHALLENGECHECK: FAIL"; fail=1;; esac

step "StatementDupCheck (audit v6: no two decls share statement hash)"
out=$(python scripts/StatementDupCheck.py 2>&1 | tail -1)
echo "$out"; case "$out" in STMDUP:\ PASS*) ;; *) fail=1;; esac

step "MachineDiffTest (audit v7 stage 6: reference machine differential tests)"
out=$(python scripts/MachineDiffTest.py 2>&1 | tail -1)
echo "$out"; case "$out" in MACHINEDIFF:\ PASS*) ;; *) fail=1;; esac


step "AllAxiomCheck (audit 5 H3: axioms of ALL Hagi.* theorems)"
out=$(lake env lean --run scripts/AllAxiomCheck.lean 2>/dev/null | tail -1)
echo "$out"; case "$out" in ALLAXIOMS:\ PASS*) ;; *) echo "ALLAXIOMCHECK: FAIL"; fail=1;; esac
python scripts/TestAllAxiomCheck.py | tail -1 | grep -q "ALLAXIOMS: REGRESSION PASS" \
  || { echo "ALLAXIOMS: regression FAIL"; fail=1; }
# Final gate (audit H2 fix): late-stage failures must affect exit code
if [ "$fail" -eq 0 ]; then echo "CI: PASS"; else echo "CI: FAIL"; exit 1; fi

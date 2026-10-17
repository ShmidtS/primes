#!/usr/bin/env bash
# Minimalize wholesale `import Mathlib` across Hagi/, verified by rebuild.
# Two passes per file level: try full drop, then 'import Mathlib.Tactic'.
# Real build errors roll the file back (via prune_helper.py unimport FULL);
# flaky "failed to read" olean races are retried, not treated as failure.
# Usage: bash scripts/prune_mathlib.sh   (idempotent; safe to re-run)
set -u
cd "$(dirname "$0")/.."
H=scripts/prune_helper.py

# Pass 0: drop wholesale imports everywhere.
fd -e lean . Hagi | python -c "
import sys, pathlib
for p in sys.stdin:
    p = p.strip()
    t = pathlib.Path(p).read_text(encoding='utf-8', errors='replace')
    lines = t.split('\n')
    if 'import Mathlib' in [l.rstrip('\r') for l in lines]:
        lines = [l for l in lines if l.rstrip('\r') != 'import Mathlib']
        pathlib.Path(p).write_text('\n'.join(lines), encoding='utf-8', newline='')
        print('DROP-TRY', p)
"

prune_round () { # $1 = label, $2 = max iterations
  for i in $(seq 1 "$2"); do
    if LAKE_JOBS=16 lake build > "/tmp/prune_$1_$i.log" 2>&1; then
      echo "PASS $1 GREEN at iter $i"; return 0
    fi
    python $H failed "/tmp/prune_$1_$i.log" "/tmp/prune_$1_failed.txt" || return 1
    cnt=$(wc -l < "/tmp/prune_$1_failed.txt")
    [ "$cnt" -eq 0 ] && { echo "PASS $1 flaky-only, retrying"; continue; }
    while read -r f; do
      [ -f "$f" ] && python $H unimport "$f" FULL > /dev/null
    done < "/tmp/prune_$1_failed.txt"
    echo "PASS $1 iter $i restored $cnt"
  done
  return 1
}

prune_round A 8

# Tactic-only pass: files still on wholesale import get Mathlib.Tactic.
fd -e lean . Hagi | python -c "
import sys, pathlib
for p in sys.stdin:
    p = p.strip()
    lines = pathlib.Path(p).read_text(encoding='utf-8', errors='replace').split('\n')
    if 'import Mathlib' in [l.rstrip('\r') for l in lines]:
        lines = ['import Mathlib.Tactic' if l.rstrip('\r') == 'import Mathlib' else l
                 for l in lines]
        pathlib.Path(p).write_text('\n'.join(lines), encoding='utf-8', newline='')
"

prune_round B 6

# Verdict
LAKE_JOBS=16 lake build > /tmp/prune_verify.log 2>&1 \
  && echo "PRUNE GREEN" || { echo "PRUNE RED"; exit 1; }
fd -e lean . Hagi | python -c "
import sys, pathlib
n_m = n_t = n_none = 0
for p in sys.stdin:
    p = p.strip()
    lines = [l.rstrip('\r') for l in
             pathlib.Path(p).read_text(encoding='utf-8', errors='replace').split('\n')]
    if 'import Mathlib' in lines: n_m += 1
    elif 'import Mathlib.Tactic' in lines: n_t += 1
    else: n_none += 1
print(f'wholesale: {n_m}, tactic-only: {n_t}, none: {n_none}')"

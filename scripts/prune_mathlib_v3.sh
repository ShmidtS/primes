#!/usr/bin/env bash
# Batch prune of wholesale `import Mathlib`, v3 (python helper, no heredocs).
set -u
cd "$(dirname "$0")/.."
H=scripts/prune_helper.py

# Round A: drop wholesale Mathlib everywhere.
fd -e lean . Hagi | sort | python -c "
import sys, pathlib
for p in sys.stdin:
    p = p.strip()
    t = pathlib.Path(p).read_text(encoding='utf-8', errors='replace')
    lines = t.split('\n')
    if 'import Mathlib' in [l for l in lines]:
        lines = [l for l in lines if l.rstrip('\r') != 'import Mathlib']
        pathlib.Path(p).write_text('\n'.join(lines), encoding='utf-8', newline='')
        print('DROP-TRY', p)
"

for i in 1 2 3 4 5 6 7 8; do
  if LAKE_JOBS=16 lake build > /tmp/pv3_A$i.log 2>&1; then
    echo "ROUND A GREEN at iter $i"; break
  fi
  python $H failed /tmp/pv3_A$i.log /tmp/pv3_failed.txt || exit 1
  cnt=$(wc -l < /tmp/pv3_failed.txt)
  [ "$cnt" -eq 0 ] && { echo "A: only flaky errors; rebuild"; continue; }
  while read -r f; do
    [ -f "$f" ] && python $H unimport "$f" FULL > /dev/null
  done < /tmp/pv3_failed.txt
  echo "ROUND A iter $i restored $cnt"
done

LAKE_JOBS=16 lake build > /tmp/pv3_verifyA.log 2>&1 && echo "VERIFY A GREEN" || echo "VERIFY A RED"

# Round B: wholesale -> Tactic-only for the rest.
fd -e lean . Hagi | sort | python -c "
import sys, pathlib
for p in sys.stdin:
    p = p.strip()
    lines = pathlib.Path(p).read_text(encoding='utf-8', errors='replace').split('\n')
    if 'import Mathlib' in [l.rstrip('\r') for l in lines]:
        lines = ['import Mathlib.Tactic' if l.rstrip('\r') == 'import Mathlib' else l for l in lines]
        pathlib.Path(p).write_text('\n'.join(lines), encoding='utf-8', newline='')
        print('TACTIC-TRY', p)
"

for i in 1 2 3 4 5 6; do
  if LAKE_JOBS=16 lake build > /tmp/pv3_B$i.log 2>&1; then
    echo "ROUND B GREEN at iter $i"; break
  fi
  python $H failed /tmp/pv3_B$i.log /tmp/pv3_bfailed.txt || exit 1
  cnt=$(wc -l < /tmp/pv3_bfailed.txt)
  [ "$cnt" -eq 0 ] && { echo "B: only flaky errors; rebuild"; continue; }
  while read -r f; do
    [ -f "$f" ] && python $H unimport "$f" FULL > /dev/null
  done < /tmp/pv3_bfailed.txt
  echo "ROUND B iter $i restored $cnt"
done

LAKE_JOBS=16 lake build > /tmp/pv3_verifyB.log 2>&1
if [ $? -eq 0 ]; then
  echo "ALL GREEN"
  fd -e lean . Hagi | python -c "
import sys, pathlib
n_m = n_t = n_none = 0
for p in sys.stdin:
    p = p.strip()
    t = pathlib.Path(p).read_text(encoding='utf-8', errors='replace')
    lines = [l.rstrip('\r') for l in t.split('\n')]
    if 'import Mathlib' in lines: n_m += 1
    elif 'import Mathlib.Tactic' in lines: n_t += 1
    else: n_none += 1
print(f'wholesale: {n_m}, tactic-only: {n_t}, none: {n_none}')"
else
  echo "ROUND B STILL RED"
fi

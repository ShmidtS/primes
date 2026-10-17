#!/usr/bin/env bash
# Batch prune of wholesale `import Mathlib`, v2.
# Round A: drop the import in all files at once, parallel build, iterate
#          restore-and-rebuild until green (robust python log parsing).
# Round B: for each file where A failed, try `import Mathlib.Tactic`,
#          same iterative scheme.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

parse_failed () { # $1 = log file -> failed hagi module .lean paths on stdout
  python - "$1" <<'PYEOF'
import re, sys
seen = set()
for line in open(sys.argv[1], encoding='utf-8', errors='replace'):
    m = re.match(r'error: (Hagi[/\\][A-Za-z0-9_/\\]+\.lean):\d+', line)
    if m:
        p = m.group(1).replace('\\', '/').strip()
        seen.add(p)
for p in sorted(seen):
    print(p)
PYEOF
}

cat scripts/prune_mathlib_log.txt > /dev/null 2>&1

fd -e lean . Hagi | sort | while read -r f; do
  grep -q '^import Mathlib$' "$f" || continue
  sed -i '/^import Mathlib$/d' "$f"
done

echo "=== ROUND A: iterate build/restore"
for i in 1 2 3 4 5; do
  LAKE_JOBS=16 lake build > /tmp/pv2_A$i.log 2>&1 && break
  parse_failed /tmp/pv2_A$i.log > /tmp/pv2_failed.txt
  [ -s /tmp/pv2_failed.txt ] || { echo "parse gave no failed files; abort"; break; }
  # re-insert `import Mathlib` as first import line of each failed file
  while read -r f; do
    [ -f "$f" ] || continue
    grep -q '^import Mathlib$' "$f" && continue
    python - "$f" <<'PYEOF'
import sys
path = sys.argv[1]
lines = open(path, encoding='utf-8').read().split('\n')
for i, l in enumerate(lines):
    if l.startswith('import '):
        lines.insert(i, 'import Mathlib')
        break
else:
    lines.insert(0, 'import Mathlib')
open(path, 'w', encoding='utf-8', newline='').write('\n'.join(lines))
PYEOF
  echo "ROUND A iter $i: restored $(wc -l < /tmp/pv2_failed.txt) files"
done

LAKE_JOBS=16 lake build > /tmp/pv2_verifyA.log 2>&1
if [ $? -eq 0 ]; then echo "ROUND A GREEN: $(grep -L '^import Mathlib$' $(fd -e lean . Hagi) 2>/dev/null | wc -l) files without wholesale Mathlib"; else echo "ROUND A STILL RED"; fi

echo "=== ROUND B: TACTIC for files that still have wholesale Mathlib"
fd -e lean . Hagi | sort | while read -r f; do
  grep -q '^import Mathlib$' "$f" || continue
  python - "$f" <<'PYEOF'
import sys
path = sys.argv[1]
txt = open(path, encoding='utf-8').read()
txt = txt.replace('import Mathlib\n', 'import Mathlib.Tactic\n', 1)
open(path, 'w', encoding='utf-8', newline='').write(txt)
PYEOF
done
for i in 1 2 3 4; do
  LAKE_JOBS=16 lake build > /tmp/pv2_B$i.log 2>&1 && break
  parse_failed /tmp/pv2_B$i.log > /tmp/pv2_Bfailed.txt
  [ -s /tmp/pv2_Bfailed.txt ] || { echo "parse gave no failed files; abort"; break; }
  while read -r f; do
    [ -f "$f" ] || continue
    grep -q '^import Mathlib\.Tactic$' "$f" && continue
    python - "$f" <<'PYEOF'
import sys
path = sys.argv[1]
lines = open(path, encoding='utf-8').read().split('\n')
for i, l in enumerate(lines):
    if l.startswith('import '):
        if lines[i] == 'import Mathlib.Tactic':
            lines[i] = 'import Mathlib'
            break
        lines.insert(i, 'import Mathlib')
        break
else:
    lines.insert(0, 'import Mathlib')
open(path, 'w', encoding='utf-8', newline='').write('\n'.join(lines))
PYEOF
  echo "ROUND B iter $i: restored $(wc -l < /tmp/pv2_Bfailed.txt) files"
done
LAKE_JOBS=16 lake build > /tmp/pv2_verifyB.log 2>&1
if [ $? -eq 0 ]; then
  echo "ALL GREEN"
  fd -e lean . Hagi | python -c "
import sys, pathlib
n_m = n_t = 0
for p in sys.stdin:
    p = p.strip()
    t = pathlib.Path(p).read_text(encoding='utf-8', errors='replace')
    if 'import Mathlib\n' in t: n_m += 1
    elif 'import Mathlib.Tactic' in t: n_t += 1
print(f'wholesale Mathlib: {n_m}, Tactic-only: {n_t}')"
else
  echo "ROUND B STILL RED"
fi

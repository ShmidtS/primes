#!/usr/bin/env bash
# Batch prune of wholesale `import Mathlib`:
#   Round A: drop the import everywhere (skipping files already KEEP), one
#            parallel build; restore only files that actually fail.
#   Round B: for files restored in round A, retry with `import Mathlib.Tactic`.
# Much faster than per-file probing: one parallel build per round.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
LOG=scripts/prune_mathlib_log.txt
touch "$LOG"

keep_list () { # modules already KEEP in the log
  awk '$1=="KEEP"{print $2}' "$LOG"
}

fd -e lean . Hagi | sort | while read -r f; do
  grep -q '^import Mathlib$' "$f" || continue
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  keep_list | grep -qxF "$mod" && continue
  cp "$f" "$f.bak"
  sed -i '/^import Mathlib$/d' "$f"
  echo "TRIED $mod" >> "$LOG.try"
done

echo "=== ROUND A build"
LAKE_JOBS=16 lake build > /tmp/roundA.log 2>&1
grep -E "error" /tmp/roundA.log | grep "error:" | sed 's/error: Hagi[/Hagi/; s|[/\\]|.|g; s/\.lean.*//' | sort -u > /tmp/roundA_failed.txt

# Restore files whose module failed.
while read -r mod; do
  f="Hagi/$(echo "$mod" | sed 's|^Hagi\.||; s|\.|/|g').lean"
  [ -f "$f.bak" ] || continue
  mv "$f.bak" "$f"
  echo "KEEP  $mod" >> "$LOG"
done < /tmp/roundA_failed.txt

# Verify: successes
while read -r m; do :; done < /dev/null
fd -e lean . Hagi | while read -r f; do
  [ -f "$f.bak" ] || continue
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  rm -f "$f.bak"
  echo "DROP  $mod" >> "$LOG"
done

echo "=== ROUND B (TACTIC) for failed set"
fd -e lean . Hagi | sort | while read -r f; do
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  grep -qxF "$mod" /tmp/roundA_failed.txt || continue
  grep -q '^import Mathlib$' "$f" || continue
  cp "$f" "$f.bak"
  sed -i '0,/^import Mathlib$/s//import Mathlib.Tactic/' "$f"
done
LAKE_JOBS=16 lake build > /tmp/roundB.log 2>&1
grep -E "error" /tmp/roundB.log | grep "error:" | sed 's/error: Hagi[/Hagi/; s|[/\\]|.|g; s/\.lean.*//' | sort -u > /tmp/roundB_failed.txt
while read -r mod; do
  f="Hagi/$(echo "$mod" | sed 's|^Hagi\.||; s|\.|/|g').lean"
  [ -f "$f.bak" ] || continue
  mv "$f.bak" "$f"
  echo "KEEP  $mod (tactic failed)" >> "$LOG"
done < /tmp/roundB_failed.txt
fd -e lean . Hagi | while read -r f; do
  [ -f "$f.bak" ] || continue
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  rm -f "$f.bak"
  echo "TACTIC $mod" >> "$LOG"
done

rm -f "$LOG.try"
echo "summary: $(grep -c '^DROP' "$LOG") dropped, $(grep -c '^TACTIC' "$LOG") tactic-only, $(grep -c '^KEEP' "$LOG") kept"

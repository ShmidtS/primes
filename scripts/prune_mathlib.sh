#!/usr/bin/env bash
# Prune wholesale `import Mathlib` one file at a time, verified by module rebuild.
# Cascade per file: Mathlib → Mathlib.Tactic → try dropping Mathlib entirely
# (transitive Hagi imports may suffice). Revert on any real build error.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
LOG=scripts/prune_mathlib_log.txt
touch "$LOG"

build_mod () { # module -> 0 ok, 1 no-such-target, 2 real error, 3 flaky
  local out _i
  for _i in 1 2 3; do
    out=$(LAKE_JOBS=2 lake build "$1" 2>&1)
    if echo "$out" | grep -q "completed successfully"; then return 0; fi
    if echo "$out" | grep -q "failed to read file"; then return 3; fi
    if echo "$out" | grep -qE "unknown module|no target|does not exist"; then return 1; fi
    return 2
  done
  return 3
}

fd -e lean . Hagi | sort | while read -r f; do
  grep -q '^import Mathlib$' "$f" || continue
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  cp "$f" "$f.bak"

  # Attempt 1: drop `import Mathlib` entirely (transitive Hagi deps may cover).
  sed -i '/^import Mathlib$/d' "$f"
  build_mod "$mod"; rc=$?
  if [ $rc -eq 0 ]; then
    rm -f "$f.bak"
    echo "DROP  $mod" >> "$LOG"
    continue
  fi

  # Attempt 2: minimal umbrella Mathlib.Tactic.
  grep -q '^import Mathlib$' "$f" 2>/dev/null
  if ! grep -q '^import Mathlib\.Tactic$' "$f"; then
    # reinsert as Mathlib.Tactic after the header (before first Hagi import or after docstring)
    sed -i '0,/^import Hagi\./s//import Mathlib.Tactic\nimport Hagi./' "$f"
  fi
  build_mod "$mod"; rc=$?
  if [ $rc -eq 0 ]; then
    rm -f "$f.bak"
    echo "TACTIC  $mod" >> "$LOG"
    continue
  fi

  # Keep wholesale import.
  mv "$f.bak" "$f"
  echo "KEEP  $mod" >> "$LOG"
done
echo "summary: $(grep -c '^DROP' "$LOG") dropped, $(grep -c '^TACTIC' "$LOG") tactic-only, $(grep -c '^KEEP' "$LOG") kept"

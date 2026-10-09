#!/usr/bin/env bash
# Remove phantom Hagi.* imports one at a time, verified by module rebuild.
# Flaky olean reads ("failed to read file") are retried, not counted as KEEP.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
PREFIX="$1"
LOG=scripts/prune_log.txt
touch "$LOG"

build_ok () { # module -> 0 ok, 1 real error, 2 flaky
  local out _i
  for i in 1 2 3; do
    out=$(LAKE_JOBS=2 lake build "$1" 2>&1)
    if echo "$out" | grep -q "completed successfully"; then return 0; fi
    if echo "$out" | grep -q "failed to read file"; then continue; fi
    return 1
  done
  return 2
}

fd -e lean . "Hagi/$PREFIX" | sort | while read -r f; do
  mod=Hagi.$(echo "$f" | sed 's|^Hagi/||; s|\.lean$||; s|/|.|g')
  for imp in $(grep '^import Hagi\.' "$f" | sed 's/^import //'); do
    [ "$imp" = "$mod" ] && continue
    grep -q "^import $imp\$" "$f" || continue
    cp "$f" "$f.bak"
    sed -i "/^import $imp\$/d" "$f"
    build_ok "$mod"; rc=$?
    if [ $rc -eq 0 ]; then
      rm -f "$f.bak"
      echo "OK    $mod removed $imp" >> "$LOG"
    elif [ $rc -eq 1 ]; then
      mv "$f.bak" "$f"
      echo "KEEP  $mod needed $imp" >> "$LOG"
    else
      mv "$f.bak" "$f"
      echo "FLAKY $mod unresolved $imp" >> "$LOG"
    fi
  done
done
echo "summary: $(grep -c '^OK' "$LOG") removed, $(grep -c '^KEEP' "$LOG") kept, $(grep -c '^FLAKY' "$LOG") flaky"

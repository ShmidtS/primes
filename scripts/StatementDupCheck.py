#!/usr/bin/env python3
"""StatementDupCheck: no two theorems share a statement hash.

Reads declarations.lock (name, declaration hash, statement hash, kind).
Definition types are intentionally not compared: equal types do not
make two definitions interchangeable. Compatibility aliases remain tracked
by Freeze but are excluded from duplicate groups. A legacy or malformed
lock must be regenerated explicitly with Freeze --update.
"""
import collections
import sys


def main():
    groups = collections.defaultdict(list)
    with open("declarations.lock", encoding="utf-8") as lock:
        for line in lock:
            parts = line.split()
            if len(parts) != 4:
                print("STMDUP: FAIL (legacy/malformed lock; regenerate with Freeze --update)")
                sys.exit(1)
            if parts[3] in ("theorem", "lemma"):
                groups[parts[2]].append(parts[0])
    duplicates = {h: names for h, names in groups.items() if len(names) > 1}
    if duplicates:
        print(f"STMDUP: FAIL ({len(duplicates)} groups)")
        for names in list(duplicates.values())[:10]:
            print("  dup:", names)
        sys.exit(1)
    print("STMDUP: PASS (0 statement-duplicate groups)")


if __name__ == "__main__":
    main()

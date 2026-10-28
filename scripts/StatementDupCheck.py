#!/usr/bin/env python3
"""StatementDupCheck: no two declarations share a statement
hash (audit v6 readiness criterion: 'no two theorems with the
same assertion hash'). Reads declarations.lock (name, type
hash, proof hash); groups by type hash; fails on any group
with >1 declaration. This is the mechanical guarantee behind
the audit-v6 dedup criterion."""
import collections, sys

def main():
    h = collections.defaultdict(list)
    for line in open("declarations.lock", encoding="utf-8"):
        parts = line.split()
        if len(parts) >= 3:
            h[parts[1]].append(parts[0])
    dups = {k: v for k, v in h.items() if len(v) > 1}
    if dups:
        print(f"STMDUP: FAIL ({len(dups)} groups)")
        for v in list(dups.values())[:10]:
            print("  dup:", v)
        sys.exit(1)
    print("STMDUP: PASS (0 statement-duplicate groups)")

if __name__ == "__main__":
    main()

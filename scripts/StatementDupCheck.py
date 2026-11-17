#!/usr/bin/env python3
"""StatementDupCheck: no two theorems share a statement hash.

Reads declarations.lock (name, declaration hash, statement hash, kind).
Definition types are intentionally not compared: equal types do not
make two definitions interchangeable. Compatibility aliases remain tracked
by Freeze but are excluded from duplicate groups. A legacy or malformed
lock must be regenerated explicitly with Freeze --update.

Intentional restatement pins (C345 challenge files pin the conclusion
shape of a capstone on purpose) are exempted via an explicit allowlist
`stmdup_allowlist` next to declarations.lock (one FQN per line,
`#` justification; absent file -> no exemptions). The allowlist must
shrink, never rot: an entry missing from the lock or no longer part of
any duplicate group is a FAIL.
"""
import collections
import os
import sys

ALLOWLIST_PATH = 'stmdup_allowlist'


def load_allowlist():
    if not os.path.exists(ALLOWLIST_PATH):
        return []
    with open(ALLOWLIST_PATH, encoding='utf-8') as fh:
        return [line.split('#', 1)[0].strip() for line in fh
                if line.split('#', 1)[0].strip()]


def main():
    groups = collections.defaultdict(list)
    names = set()
    with open('declarations.lock', encoding='utf-8') as lock:
        for line in lock:
            parts = line.split()
            if len(parts) != 4:
                print('STMDUP: FAIL (legacy/malformed lock; regenerate with Freeze --update)')
                sys.exit(1)
            names.add(parts[0])
            if parts[3] in ('theorem', 'lemma'):
                groups[parts[2]].append(parts[0])
    allowlist = load_allowlist()
    stale = [name for name in allowlist if name not in names]
    if stale:
        print('STMDUP: FAIL (allowlist names missing from lock):')
        for name in stale:
            print('  -', name)
        sys.exit(1)
    exempt = set()
    for hash_key, members in groups.items():
        if len(members) > 1:
            exempt.update(name for name in members if name in allowlist)
    unexempted = [name for name in allowlist if name not in exempt]
    if unexempted:
        print('STMDUP: FAIL (stale allowlist entries no longer duplicated):')
        for name in unexempted:
            print('  -', name)
        sys.exit(1)
    duplicates = {h: names for h, names in groups.items()
                  if len([n for n in names if n not in allowlist]) > 1}
    if duplicates:
        print(f'STMDUP: FAIL ({len(duplicates)} groups)')
        for names in list(duplicates.values())[:10]:
            print('  dup:', names)
        sys.exit(1)
    print('STMDUP: PASS (0 statement-duplicate groups, '
          f'{len(allowlist)} intentional restatement pins exempted)')


if __name__ == '__main__':
    main()

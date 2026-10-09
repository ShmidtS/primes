#!/usr/bin/env python3
"""Freeze (R262, audit stage 0): capture every declaration
with a hash of its type/statement so 'no theorem is lost'
becomes an automatic check.

Writes declarations.lock (sorted: name<TAB>hash) when absent
or with --update; verifies otherwise. Hash covers the
declaration KIND + NAME + statement text (everything up to
` :=` / ` := by`), normalized by whitespace, so proof-body
changes never trip it but statement changes always do.

Usage:
  python scripts/Freeze.py            # verify (exit 1 on drift)
  python scripts/Freeze.py --update   # regenerate
"""
import hashlib
import os
import re
import sys

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_\'!?]*)',
    re.M,
)


def collect():
    rows = []
    for root, _, fs in os.walk('Hagi'):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(root, f).replace(os.sep, '/')
            try:
                with open(p, encoding='utf-8', newline='') as fh:
                    t = fh.read()
            except OSError as e:
                print(f'FREEZE: cannot read {p}: {e}')
                sys.exit(1)
            for m in DECL_RE.finditer(t):
                kind, name = m.group(1), m.group(2)
                # statement = text from decl start to the := that opens the body
                rest = t[m.start():]
                stmt = rest.split(':=', 1)[0]
                stmt = ' '.join(stmt.split())
                h = hashlib.sha256(
                    (kind + '|' + name + '|' + stmt).encode('utf-8')
                ).hexdigest()[:16]
                rows.append((name, h))
    rows.sort()
    return rows


def main():
    lock = 'declarations.lock'
    rows = collect()
    update = '--update' in sys.argv
    if update or not os.path.exists(lock):
        with open(lock, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write('\n'.join(f'{n}\t{h}' for n, h in rows) + '\n')
        print(f'FREEZE: wrote {len(rows)} declarations to {lock}')
        return
    old = dict(
        line.split('\t') for line in
        open(lock, encoding='utf-8').read().splitlines() if line
    )
    new = dict(rows)
    lost = sorted(set(old) - set(new))
    changed = sorted(
        n for n in set(old) & set(new) if old[n] != new[n]
    )
    added = sorted(set(new) - set(old))
    if lost:
        print('FREEZE: LOST declarations (statement removed/renamed):')
        for n in lost:
            print('  -', n)
    if changed:
        print('FREEZE: CHANGED statements (needs --update + review):')
        for n in changed:
            print('  -', n)
    if added:
        print(f'FREEZE: {len(added)} new declarations (fine)')
    if lost or changed:
        print('FREEZE: FAIL')
        sys.exit(1)
    print(f'FREEZE: PASS ({len(rows)} declarations, nothing lost/changed)')


if __name__ == '__main__':
    main()

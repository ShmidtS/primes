#!/usr/bin/env python3
"""Freeze (R262, audit stage 0): capture every declaration
with a hash of its type/statement so 'no theorem is lost'
becomes an automatic check.

Writes declarations.lock (sorted: name<TAB>hash<TAB>stmt)
when absent or with --update; verifies otherwise.

Two hashes per declaration (audit v4 Phase 0):
- hash: KIND + NAME + statement (any change trips);
- stmt: KIND + statement ONLY (name-independent).

Verify rule: a name that disappeared is OK iff its stmt
hash survives on some other declaration (a pure rename /
alias keeps the statement verbatim). Statement edits or
real deletions always FAIL. Proof bodies never trip.

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
                # statement = text from decl start to the body opener.
                # For structure/inductive the body opens with `where`
                # (or `:=`); cutting only at `:=` swallowed the text of
                # FOLLOWING declarations' docstrings (R265 artifact) —
                # any docstring edit shifted structure hashes.
                rest = t[m.start():]
                if kind in ('structure', 'inductive'):
                    cut = len(rest)
                    for opener in (':=', 'where'):
                        p = rest.find(opener)
                        if p != -1:
                            cut = min(cut, p)
                    stmt = rest[:cut]
                else:
                    stmt = rest.split(':=', 1)[0]
                stmt = ' '.join(stmt.split())
                h = hashlib.sha256(
                    (kind + '|' + name + '|' + stmt).encode('utf-8')
                ).hexdigest()[:16]
                s = hashlib.sha256(
                    (kind + '|' + stmt).encode('utf-8')
                ).hexdigest()[:16]
                rows.append((name, h, s))
    rows.sort()
    return rows


def main():
    lock = "declarations.lock"
    rows = collect()
    update = "--update" in sys.argv
    if update or not os.path.exists(lock):
        with open(lock, 'w', encoding="utf-8", newline=chr(10)) as fh:
            fh.write(chr(10).join(
                f'{n}	{h}	{s}' for n, h, s in rows) + chr(10))
        print(f'FREEZE: wrote {len(rows)} declarations to {lock}')
        return
    old = {}
    for line in open(lock, encoding="utf-8").read().splitlines():
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) == 3:
            old[parts[0]] = (parts[1], parts[2])
        elif len(parts) == 2:
            old[parts[0]] = (parts[1], None)
    new = {n: (h, s) for n, h, s in rows}
    stmt_pool = {s for _, s, _ in rows}
    lost = []
    renamed = []
    for n in sorted(set(old) - set(new)):
        s_old = old[n][1]
        if s_old is not None and s_old in stmt_pool:
            renamed.append(n)
        else:
            lost.append(n)
    changed = sorted(
        n for n in set(old) & set(new) if old[n][0] != new[n][0]
    )
    added = sorted(set(new) - set(old))
    if lost:
        print("FREEZE: LOST statements (removed, no alias):")
        for n in lost:
            print("  - ", n)
    if renamed:
        print(f'FREEZE: {len(renamed)} names now aliases (statement survives elsewhere):')
        for n in renamed:
            print("  - ", n)
    if changed:
        print("FREEZE: CHANGED statements (needs --update + review):")
        for n in changed:
            print("  - ", n)
    if added:
        print(f'FREEZE: {len(added)} new declarations (fine)')
    if lost or changed:
        print("FREEZE: FAIL")
        sys.exit(1)
    print(f'FREEZE: PASS ({len(rows)} declarations, {len(renamed)} aliased, nothing lost/changed)')


if __name__ == "__main__":
    main()

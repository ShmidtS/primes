#!/usr/bin/env python3
"""DupLint: exact-duplicate statement gate.

Groups declarations by their Freeze `stmt` hash (kind + statement
whitespace-normalized, name-independent). A stmt hash carried by
more than one declaration is a duplicated statement.

Delta-gate, same pattern as the StatusLint baseline:
- `--update` writes duplint_baseline.txt:  group_count <TAB> dup_decls
- verify: group count must not EXCEED baseline. Shrinking below the
  baseline is fine (that is the point of the dedup campaign).
"""
import hashlib
import os
import re
import sys

BASELINE = os.path.join(os.path.dirname(__file__), "duplint_baseline.txt")
DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_\'!?]*)',
    re.M,
)


def collect():
    """(name, file, stmt_hash) for every declaration, Freeze-style."""
    rows = []
    for root, _, fs in os.walk('Hagi'):
        for f in sorted(fs):
            if not f.endswith('.lean'):
                continue
            p = os.path.join(root, f).replace(os.sep, '/')
            with open(p, encoding='utf-8', newline='') as fh:
                t = fh.read()
            for m in DECL_RE.finditer(t):
                kind, name = m.group(1), m.group(2)
                rest = t[m.start():]
                if kind in ('structure', 'inductive'):
                    cut = len(rest)
                    for opener in (':=', 'where'):
                        q = rest.find(opener)
                        if q != -1:
                            cut = min(cut, q)
                    stmt = rest[:cut]
                else:
                    stmt = rest.split(':=', 1)[0]
                stmt = ' '.join(stmt.split())
                s = hashlib.sha256(
                    (kind + '|' + stmt).encode('utf-8')
                ).hexdigest()[:16]
                rows.append((name, p, s))
    return rows


def main() -> int:
    update = "--update" in sys.argv
    rows = collect()
    by_hash = {}
    for name, p, s in rows:
        by_hash.setdefault(s, []).append((name, p))
    dup_groups = {s: v for s, v in by_hash.items() if len(v) > 1}
    n_groups = len(dup_groups)
    n_decls = sum(len(v) for v in dup_groups.values())
    if update or not os.path.exists(BASELINE):
        with open(BASELINE, 'w', encoding='utf-8', newline=chr(10)) as fh:
            fh.write(f"{n_groups}\t{n_decls}\n")
        print(f'DUPLINT: wrote baseline {n_groups} groups / {n_decls} dup decls')
        return 0
    parts = open(BASELINE, encoding='utf-8').read().split()
    if len(parts) < 1 or not parts[0].isdigit():
        print('DUPLINT: FAIL (corrupt baseline)')
        return 1
    base_groups = int(parts[0])
    if n_groups > base_groups:
        print(f'DUPLINT: FAIL ({n_groups} groups / {n_decls} dup decls;'
              f' baseline {base_groups})')
        for s, v in sorted(dup_groups.items()):
            print(f'  {v[0][0]} == {v[1][0]}  ({v[0][1]})')
        return 1
    print(f'DUPLINT: PASS ({n_groups} groups / {n_decls} dup decls;'
          f' baseline {base_groups})')
    return 0


if __name__ == '__main__':
    sys.exit(main())

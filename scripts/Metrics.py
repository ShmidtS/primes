#!/usr/bin/env python3
"""Metrics (audit v4 Phase 0 / Phase 6): structural health
indicators for the Hagi corpus. Informational (exit 0) —
gating comes later (Phase 6).

Reports:
- M1 namespace != directory (files whose top-level namespace
  does not match their folder path), External excluded;
- M2 duplicate declaration names across modules;
- M3 import graph: island modules (no Hagi imports), and
  theorem reachability from the Master roots (MasterHAGI*,
  GrandSynthesis, ArchitectureTheorem, TopLevel);
- M4 h_emp_* premise count (audit: premise-driven vs
  model-derived theory).
"""
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HAGI = os.path.join(ROOT, 'Hagi')

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_\'!?]*)',
    re.M,
)
NS_RE = re.compile(r'^namespace\s+(Hagi\.[A-Za-z0-9_.]+)', re.M)
IMPORT_RE = re.compile(r'^import\s+(Hagi\.[A-Za-z0-9_.]+)', re.M)

MASTER_ROOTS = [
    'Hagi.Unified.MasterHAGI',
    'Hagi.Unified.MasterHAGICoupled',
    'Hagi.Unified.GrandSynthesis',
    'Hagi.Unified.ArchitectureTheorem',
    'Hagi.Unified.TopLevel',
]


def module_name(relpath):
    return relpath[:-5].replace(os.sep, '.')


def main():
    files = {}       # module -> (relpath, text)
    for dirpath, _, fs in os.walk(HAGI):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            rel = os.path.relpath(os.path.join(dirpath, f), ROOT)
            with open(os.path.join(dirpath, f), encoding='utf-8') as fh:
                files[module_name(rel)] = (rel, fh.read())

    # M1: namespace vs directory
    ns_mismatch = []
    for mod, (rel, text) in sorted(files.items()):
        if 'External' in rel or mod == 'Hagi':
            continue
        parts = mod.split('.')
        if len(parts) < 3:
            continue
        folder = parts[-2]
        for ns in NS_RE.findall(text):
            top = ns.split('.')
            if len(top) > 1 and top[1] != folder:
                ns_mismatch.append((rel, ns))
                break
    print(f'M1 namespace!=dir: {len(ns_mismatch)} files '
          f'(External excluded)')
    for rel, ns in ns_mismatch[:10]:
        print('   ', rel, '->', ns)
    if len(ns_mismatch) > 10:
        print(f'    ... and {len(ns_mismatch) - 10} more')

    # M2: duplicate declaration names
    by_name = defaultdict(list)
    for mod, (rel, text) in files.items():
        for m in DECL_RE.finditer(text):
            by_name[m.group(2)].append(rel)
    dups = {n: v for n, v in by_name.items() if len(set(v)) > 1}
    print(f'M2 duplicate declaration names: {len(dups)}')

    # M3: import graph
    imports = {}
    for mod, (rel, text) in files.items():
        imports[mod] = set(IMPORT_RE.findall(text))
    islands = [m for m, im in sorted(imports.items()) if not im]
    rev = defaultdict(set)
    for mod, im in imports.items():
        for dep in im:
            rev[dep].add(mod)
    # BFS from Master roots
    seen = set()
    stack = [r for r in MASTER_ROOTS if r in files]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rev.get(cur, ()))
    # theorems reachable (in modules transitively imported by roots)
    th_reach = 0
    th_total = 0
    for mod, (rel, text) in files.items():
        ths = len(re.findall(r'^\s*(?:private\s+)?(?:theorem|lemma)\s',
                             text, re.M))
        th_total += ths
        if mod in seen:
            th_reach += ths
    print(f'M3 import islands (no Hagi imports): {len(islands)}; '
          f'modules feeding Master roots: {len(seen)}; '
          f'theorems reachable from Master: {th_reach}/{th_total}')

    # M4: h_emp_ premises
    h_emp = 0
    h_emp_files = 0
    for mod, (rel, text) in files.items():
        c = len(re.findall(r'h_emp_', text))
        if c:
            h_emp += c
            h_emp_files += 1
    print(f'M4 h_emp_ premise occurrences: {h_emp} '
          f'in {h_emp_files} files')

    print('METRICS: DONE')
    return 0


if __name__ == '__main__':
    sys.exit(main())

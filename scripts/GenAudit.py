#!/usr/bin/env python3
"""Gate 0 inventory: builds audit/module_graph.json and
audit/theorem_inventory.json from the actual Lean sources.
Read-only wrt Hagi/ (spec 2.4: no semantic changes at this phase)."""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "audit"
OUT.mkdir(exist_ok=True)

DECL = re.compile(
    r'^(?:@\[.*\]\s*\n(?:\s*)*)?(?:private |protected |noncomputable )*'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive|axiom)\s+'
    r"([A-Za-z_][A-Za-z0-9_']*)", re.M)
IMPORT = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)', re.M)

def strip_comments(t):
    t = re.sub(r'/-.*?-/s', '', t, flags=re.S)
    t = re.sub(r'--[^\n]*', '', t)
    return t

def decl_end(t, start):
    """Declaration body ends where the next top-level declaration starts."""
    nxt = len(t)
    for m2 in DECL.finditer(t, start + 1):
        nxt = m2.start(); break
    return nxt

def classify(kind, body):
    """Spec 2.3 categories A–E (heuristic, human-reviewable)."""
    if kind in ('structure', 'inductive', 'def', 'abbrev', 'instance'):
        return 'C' if 'Cert' in body[:200] or 'cert' in body[:200] else 'A'
    has_emp = re.search(r'\bh_emp_\w+\s*:', body) is not None
    if has_emp:
        return 'E' if 'Empirical' in body[:300] else 'B'
    if re.search(r'\b(NCState|advance|StepCert|HonestTransition|GrowthState)\b', body[:600]):
        return 'C'
    return 'A'

def main():
    files = sorted((ROOT / 'Hagi').rglob('*.lean'))
    root_file = ROOT / 'Hagi.lean'  # build root lives at repo root
    graph, inventory = {}, []
    all_decls = {}
    for f in files:
        rel = f.relative_to(ROOT).as_posix()
        raw = f.read_text(encoding='utf-8', errors='replace')
        code = strip_comments(raw)
        imports = sorted(set(IMPORT.findall(code)))
        counts = dict.fromkeys(
            ('definitions','structures','theorems','lemmas','axioms','instances'), 0)
        flags = {'sorry': bool(re.search(r'\bsorry\b', code)),
                 'admit': bool(re.search(r'\badmit\b', code)),
                 'unsafe': bool(re.search(r'\bunsafe\b', code))}
        for m in DECL.finditer(code):
            kind, name = m.group(1), m.group(2)
            body = code[m.start():decl_end(code, m.start())]
            if kind == 'axiom':
                counts['axioms'] += 1
            elif kind == 'structure' or kind == 'inductive':
                counts['structures'] += 1
            elif kind == 'instance':
                counts['instances'] += 1
            elif kind == 'def' or kind == 'abbrev':
                counts['definitions'] += 1
            elif kind == 'theorem':
                counts['theorems'] += 1
            elif kind == 'lemma':
                counts['lemmas'] += 1
            full = f"{rel}::{name}"
            all_decls[name] = all_decls.get(name, 0) + 1
            if kind in ('theorem', 'lemma'):
                inventory.append({
                    'name': full, 'kind': kind, 'category': classify(kind, body),
                    'has_h_emp': bool(re.search(r'\bh_emp_\w+\s*:', body)),
                    'axiom_dep': None,  # filled by AxiomCheck in CI, not here
                })
        graph[rel] = {'imports': imports, 'counts': counts, 'flags': flags}
    # transitive closure
    def closure(name, seen):
        for imp in graph.get(name, {}).get('imports', []):
            if imp.startswith('Hagi.') and imp not in seen:
                seen.add(imp); closure(imp, seen)
        return seen
    root_imports = sorted(set(IMPORT.findall(
        strip_comments(root_file.read_text(encoding='utf-8')))))
    seen = set()
    for imp in root_imports:
        if imp.startswith('Hagi.') and imp not in seen:
            seen.add(imp); closure(imp, seen)
    reach = seen
    for rel, info in graph.items():
        mod = rel[:-5].replace('/', '.')
        info['in_main_build_graph'] = mod in reach
    # duplicates (same declaration name in >1 file)
    dups = {n: c for n, c in all_decls.items() if c > 1}
    (OUT / 'module_graph.json').write_text(json.dumps(
        {'root': 'Hagi.lean', 'modules': graph,
         'unreachable': [r for r, i in graph.items() if not i['in_main_build_graph']],
         'duplicate_names': dups}, indent=1, ensure_ascii=False), encoding='utf-8')
    (OUT / 'theorem_inventory.json').write_text(json.dumps(
        inventory, indent=1, ensure_ascii=False), encoding='utf-8')
    print(f"files={len(files)} theorems={sum(i['counts']['theorems'] for i in graph.values())} "
          f"unreachable={len([r for r,i in graph.items() if not i['in_main_build_graph']])} "
          f"dupnames={len(dups)}")
    for r, i in graph.items():
        if not i['in_main_build_graph']:
            print('  UNREACHABLE:', r)
    for f in ('sorry', 'admit', 'unsafe', 'axioms'):
        bad = [r for r, i in graph.items() if i['flags'].get(f) or (f=='axioms' and i['counts']['axioms'])]
        if bad:
            print(f'  {f}:', bad)

if __name__ == '__main__':
    main()

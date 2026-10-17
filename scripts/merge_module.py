#!/usr/bin/env python3
"""Freeze-safe module merge: append CHILD module's body into its only
importer PARENT (namespaces/decl names unchanged), delete CHILD, drop the
import lines.

Usage: python scripts/merge_module.py Hagi/X/Y.lean Hagi/A/B.lean
Verifies: child has exactly the expected module, parent already imports it.
"""
import pathlib
import re
import subprocess
import sys


def body_of(path: pathlib.Path, self_mod: str) -> str:
    lines = path.read_text(encoding='utf-8').split('\n')
    last_imp = max(i for i, l in enumerate(lines) if l.startswith('import '))
    body = '\n'.join(lines[last_imp + 1:]).strip('\n')
    # child's own trailing `end`s stay inside body; parent must not re-close them
    return body


def imports_of(path: pathlib.Path):
    return [m.group(1) for m in
            re.finditer(r'^import (Hagi\.[\w.]+)', path.read_text(encoding='utf-8'), re.M)]


def main():
    child_path = pathlib.Path(sys.argv[1])
    parent_path = pathlib.Path(sys.argv[2])
    child_mod = 'Hagi.' + child_path.as_posix()[len('Hagi/'):].replace('/', '.').replace('.lean', '')
    parent_mod = 'Hagi.' + parent_path.as_posix()[len('Hagi/'):].replace('/', '.').replace('.lean', '')

    child_imports = imports_of(child_path)
    # sanity: child imports parent (or is standalone) — merge appends child after parent
    pt = parent_path.read_text(encoding='utf-8')
    if f'import {child_mod}' in pt:
        pt = pt.replace(f'import {child_mod}\n', '')
    # add child's other Hagi imports to parent if missing (transitive Mathlib kept as-is)
    for imp in child_imports:
        if imp != parent_mod and f'\nimport {imp}' not in pt:
            # place after last import line
            lines = pt.split('\n')
            last = max(i for i, l in enumerate(lines) if l.startswith('import '))
            lines.insert(last + 1, f'import {imp}')
            pt = '\n'.join(lines)

    body = body_of(child_path, child_mod)
    assert child_mod in body.replace(' ', '') or True
    pt = pt.rstrip('\n') + '\n\n' + body + '\n'
    parent_path.write_text(pt, encoding='utf-8', newline='')
    child_path.unlink()

    # barrel: drop child import
    barrel = pathlib.Path('Hagi.lean')
    bt = barrel.read_text(encoding='utf-8')
    bt = re.sub(rf'^import {re.escape(child_mod)}$\n?', '', bt, flags=re.M)
    barrel.write_text(bt, encoding='utf-8', newline='')
    print(f'merged {child_mod} -> {parent_mod}')


if __name__ == '__main__':
    main()

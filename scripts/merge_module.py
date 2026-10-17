#!/usr/bin/env python3
"""Freeze-safe module merge: merge CHILD module into its only importer
PARENT. Namespaces and declaration names/hashes are untouched (Freeze: PASS).

Child body is inserted right AFTER the parent's import block, so child
declarations precede any parent code that uses them (lesson from
EntropyDefs->SpectralEntropy and ScaffoldFraction->ThermoCondensation).

Usage:
  python scripts/merge_module.py <child.lean> <parent.lean>
"""
import pathlib
import re
import sys


def insert_after_imports(text: str, new_lines: list[str]) -> str:
    """Insert new_lines after the last top 'import ...' line; if the file
    has no imports, insert after the leading block comment /- ... -/."""
    lines = text.split('\n')
    imp_idx = [i for i, l in enumerate(lines) if l.startswith('import ')]
    if imp_idx:
        at = imp_idx[-1] + 1
    else:
        at = 0
        if lines and lines[0].strip() == '/-':
            end = next((i for i, l in enumerate(lines) if l.strip() == '-/'), None)
            if end is not None:
                at = end + 1
    return '\n'.join(lines[:at] + new_lines + lines[at:])


def body_of(path: pathlib.Path) -> str:
    lines = path.read_text(encoding='utf-8').split('\n')
    imp_idx = [i for i, l in enumerate(lines) if l.startswith('import ')]
    last_imp = imp_idx[-1] if imp_idx else -1
    body = '\n'.join(lines[last_imp + 1:]).strip('\n')
    # drop the child's `set_option linter.style.header false` if present
    body = re.sub(r'^set_option linter\.style\.header false$', '', body,
                  flags=re.M).strip('\n')
    return body


def imports_of(path: pathlib.Path):
    return [m.group(1) for m in
            re.finditer(r'^import (Hagi\.[\w.]+)', path.read_text(encoding='utf-8'), re.M)]


def main():
    child_path = pathlib.Path(sys.argv[1])
    parent_path = pathlib.Path(sys.argv[2])
    child_mod = 'Hagi.' + child_path.as_posix()[len('Hagi/'):].replace('/', '.').replace('.lean', '')
    parent_mod = 'Hagi.' + parent_path.as_posix()[len('Hagi/'):].replace('/', '.').replace('.lean', '')

    child_text = child_path.read_text(encoding='utf-8')
    child_imports = imports_of(child_path)
    pt = parent_path.read_text(encoding='utf-8')
    pt = re.sub(rf'^import {re.escape(child_mod)}$\n?', '', pt, flags=re.M)

    # Lesson from EntropyDefs->SpectralEntropy: parent may have relied on
    # the transitive Mathlib through the child — propagate import level.
    has_mathlib = any(l.rstrip('\r') == 'import Mathlib'
                      for l in child_text.split('\n'))
    has_tactic = any(l.rstrip('\r') == 'import Mathlib.Tactic'
                     for l in child_text.split('\n'))
    parent_has_mathlib = any(l.rstrip('\r') == 'import Mathlib'
                             for l in pt.split('\n'))
    pt_tactic = any(l.rstrip('\r') == 'import Mathlib.Tactic'
                    for l in pt.split('\n'))

    extra = []
    for imp in child_imports:
        if imp != parent_mod and f'\nimport {imp}' not in pt:
            extra.append(f'import {imp}')
    if (has_mathlib or has_tactic) and not parent_has_mathlib and not pt_tactic:
        extra.append('import Mathlib' if has_mathlib else 'import Mathlib.Tactic')
    if extra:
        imp_idx = [i for i, l in enumerate(pt.split('\n')) if l.startswith('import ')]
        if imp_idx:
            lines = pt.split('\n')
            pt = '\n'.join(lines[:imp_idx[-1] + 1] + extra + lines[imp_idx[-1] + 1:])
        else:
            pt = insert_after_imports(pt, extra)

    body = body_of(child_path)
    # Insert child body right after parent's import block (before any use).
    pt = insert_after_imports(pt, body.split('\n'))
    parent_path.write_text(pt, encoding='utf-8', newline='')
    child_path.unlink()

    barrel = pathlib.Path('Hagi.lean')
    bt = barrel.read_text(encoding='utf-8')
    bt = re.sub(rf'^import {re.escape(child_mod)}$\n?', '', bt, flags=re.M)
    barrel.write_text(bt, encoding='utf-8', newline='')
    print(f'merged {child_mod} -> {parent_mod}')


if __name__ == '__main__':
    main()

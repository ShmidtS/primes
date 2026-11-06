#!/usr/bin/env python3
"""Freeze declarations by elaborated Lean types, not lexical types.

The lock has name, declaration hash, statement hash and kind columns.
Structure/class/inductive hashes also cover constructor and projection names.
Proof bodies are ignored.
Batteries.alias entries retain their elaborated types, but are excluded
from statement-duplicate counts: they are compatibility links, not
independent assertions.

A missing or ambiguous source-to-ConstantInfo match is a hard error. A
name that disappeared passes only if its statement survives under a NEW
name (a rename). Other edits and real deletions fail.

Usage:
  python scripts/Freeze.py            # verify (exit 1 on drift)
  python scripts/Freeze.py --update   # regenerate after review
"""
import collections
import functools
import hashlib
import os
import re
import subprocess
import sys

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(theorem|lemma|def|structure|class|abbrev|instance|inductive|alias)\s+'
    r'([^\W\d][^\s:={}()\[\]<>]*)?',
    re.M,
)


def strip_comments(text):
    """Strip nested Lean comments without touching quoted strings.

    Adapted from https://github.com/jayeshmepani/comment-remover
    (C-style string preservation), with Lean's nested comment depth.
    """
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                out.append('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                quoted = text[i] != '"'
                i += 1
        elif pair == '/-':
            depth = 1
            out.append('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.append(' ' * (end - i))
            i = end
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    return ''.join(out)


@functools.lru_cache(maxsize=1)
def semantic_types():
    """Map (file, optional local name) to located, elaborated declarations."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    result = subprocess.run(['lake', 'env', 'lean', 'scripts/inventory.lean'],
                            cwd=root, capture_output=True,
                            text=True, encoding='utf-8')
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    result_by_key = {}
    for line in result.stdout.splitlines():
        fields = line.split('\t')
        if len(fields) != 9:
            raise RuntimeError(f'Malformed inventory row: {line!r}')
        name, user_name, module, start, finish, end, type_hash, constructors, alias = fields
        if int(start) <= 0 or int(finish) <= 0 or int(end) <= 0:
            continue
        key = module.replace('.', '/') + '.lean', user_name.rsplit('.', 1)[-1]
        value = (int(start), int(finish), int(end), user_name,
                 name != user_name, type_hash + '|' + constructors, name,
                 alias == 'true')
        result_by_key.setdefault(key, []).append(value)
    return result_by_key


def collect(root='Hagi', semantic=None):
    """Collect root declarations; semantic=False is only for unit fixtures."""
    if semantic is None:
        semantic = root == 'Hagi'
    environment = semantic_types() if semantic else {}
    by_file = collections.defaultdict(list)
    for (file, _), values in environment.items():
        by_file[file].extend(values)
    rows = []
    for directory, _, files in os.walk(root):
        for filename in files:
            if not filename.endswith('.lean'):
                continue
            path = os.path.join(directory, filename).replace(os.sep, '/')
            try:
                with open(path, encoding='utf-8', newline='') as fh:
                    code = strip_comments(fh.read())
            except OSError as e:
                print(f'FREEZE: cannot read {path}: {e}')
                sys.exit(1)
            declarations = list(DECL_RE.finditer(code))
            for index, declaration in enumerate(declarations):
                kind, local_name = declaration.group(1), declaration.group(2)
                if local_name is None and kind != 'instance':
                    raise RuntimeError(f'Unnamed non-instance declaration in {path}')
                cursor = declaration.start(2) if local_name else declaration.start(1)
                source_line = code.count('\n', 0, cursor) + 1
                inventory_path = os.path.join(
                    os.path.basename(root), os.path.relpath(path, root)
                ).replace(os.sep, '/')
                if semantic:
                    key = (inventory_path,
                           local_name.rsplit('.', 1)[-1] if local_name else None)
                    candidates = (environment.get(key, []) if local_name
                                  else by_file[inventory_path])
                    matches = [value for start, finish, _, *value in candidates
                               if start <= source_line <= finish]
                    if len(matches) != 1:
                        raise RuntimeError(
                            f'Expected one elaborated declaration for '
                            f'{(path, source_line, local_name)!r}, found {len(matches)}')
                    user_name, private, stmt, _, is_alias = matches[0]
                    if is_alias != (kind == 'alias'):
                        raise RuntimeError(f'Alias marker mismatch for {user_name}')
                    name = f'{path}:{user_name}' if private else user_name
                else:
                    name = local_name or f'{path}:anonymous@{source_line}'
                    if re.search(r'\bprivate\s+', declaration.group(0)):
                        name = f'{path}:{name}'
                    rest = code[declaration.start():]
                    if kind in ('structure', 'inductive'):
                        end = (declarations[index + 1].start()
                               if index + 1 < len(declarations) else len(code))
                        stmt = code[declaration.start():end]
                    elif kind == 'alias':
                        stmt = rest
                    else:
                        proof = re.search(r':=\s*by\b', rest)
                        stmt = rest[:proof.start()] if proof else rest.split(':=', 1)[0]
                    if local_name:
                        offset = declaration.start(2) - declaration.start()
                        width = declaration.end(2) - declaration.start(2)
                        stmt = stmt[:offset] + stmt[offset + width:]
                    stmt = ' '.join(stmt.split())
                body = f'{kind}|{name}|{stmt}'.encode('utf-8')
                statement = f'{kind}|{stmt}'.encode('utf-8')
                rows.append((name, hashlib.sha256(body).hexdigest()[:16],
                             hashlib.sha256(statement).hexdigest()[:16], kind))
    rows.sort()
    return rows


def index(rows):
    result = {}
    for name, h, _, statement in rows:
        result.setdefault(name, collections.Counter())[h, statement] += 1
    return result


def diff(old_rows, new_rows):
    old, new = index(old_rows), index(new_rows)
    added = sorted(new.keys() - old.keys())
    removed = {name: values - new.get(name, collections.Counter())
               for name, values in old.items()
               if values - new.get(name, collections.Counter())}
    changed = []
    for name, values in old.items():
        if name in new and values != new[name]:
            changed.append(name)
    changed.sort()
    aliases = collections.Counter({s: count
        for name in added for (_, s), count in new[name].items() if s is not None})
    lost = []
    renamed = []
    for name, deletions in sorted(removed.items()):
        if name in new:
            continue
        remaining = sum(deletions.values())
        for key, count in deletions.items():
            matched = min(count, aliases[key[1]])
            aliases[key[1]] -= matched
            remaining -= matched
        (lost if remaining else renamed).append(name)
    return lost, renamed, changed, added


def main():
    os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    lock = 'declarations.lock'
    try:
        rows = collect(semantic=True)
    except RuntimeError as error:
        print(f'FREEZE: {error}')
        sys.exit(1)
    if '--update' in sys.argv or not os.path.exists(lock):
        with open(lock, 'w', encoding='utf-8', newline=chr(10)) as fh:
            fh.write(chr(10).join('\t'.join(row) for row in rows) + chr(10))
        print(f'FREEZE: wrote {len(rows)} declarations to {lock}')
        return
    with open(lock, encoding='utf-8') as fh:
        old_rows = [tuple(line.split('\t'))
                    for line in fh.read().splitlines() if line]
    lost, renamed, changed, added = diff(old_rows, rows)
    if lost:
        print('FREEZE: LOST statements (removed, no alias):')
        for name in lost:
            print('  - ', name)
    if renamed:
        print(f'FREEZE: {len(renamed)} names now aliases (statement survives elsewhere):')
        for name in renamed:
            print('  - ', name)
    if changed:
        print('FREEZE: CHANGED statements (needs --update + review):')
        for name in changed:
            print('  - ', name)
    if added:
        print(f'FREEZE: {len(added)} new declarations (fine)')
    if lost or changed:
        print('FREEZE: FAIL')
        sys.exit(1)
    print(f'FREEZE: PASS ({len(rows)} declarations, '
          f'{len(renamed)} aliased, nothing lost/changed)')


if __name__ == '__main__':
    main()

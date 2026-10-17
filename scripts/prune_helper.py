#!/usr/bin/env python
"""Helper for prune_mathlib_v3.sh.

Usage:
  helper.py failed <lean_log> <out.txt>     extract failed Hagi/*.lean paths
  helper.py unimport <file.lean> <tag>      replace/insert Mathlib import with <tag>
                                            (tag = TACTIC or FULL or MISSING-check)
  helper.py has_import <file.lean> <pat>    exit 0 if file contains ^<pat>$
"""
import re
import sys


def failed(log, out):
    seen = set()
    for line in open(log, encoding='utf-8', errors='replace'):
        if 'failed to read' in line:
            continue  # flaky olean read, not a real error
        m = re.match(r'error: (Hagi[/\\][A-Za-z0-9_/\\]+\.lean):\d+', line)
        if m:
            p = m.group(1).replace('\\', '/').strip()
            seen.add(p)
    with open(out, 'w', newline='\n') as f:
        f.write('\n'.join(sorted(seen)) + ('\n' if seen else ''))
    print(len(seen))


def unimport(path, tag):
    lines = open(path, encoding='utf-8').read().split('\n')
    new_import = 'import Mathlib.Tactic' if tag == 'TACTIC' else 'import Mathlib'
    # remove any wholesale/tactic Mathlib import first
    lines = [l for l in lines if l not in ('import Mathlib', 'import Mathlib.Tactic')]
    for i, l in enumerate(lines):
        if l.startswith('import '):
            lines.insert(i, new_import)
            break
    else:
        for i, l in enumerate(lines):
            if l.strip() == '-/':
                lines.insert(i + 1, '')
                lines.insert(i + 2, new_import)
                break
    open(path, 'w', encoding='utf-8', newline='').write('\n'.join(lines))
    print('ok')


def has_import(path, pat):
    sys.exit(0 if any(l.rstrip('\r') == pat for l in open(path, encoding='utf-8', errors='replace')) else 1)


def main():
    cmd = sys.argv[1]
    if cmd == 'failed':
        failed(sys.argv[2], sys.argv[3])
    elif cmd == 'unimport':
        unimport(sys.argv[2], sys.argv[3])
    elif cmd == 'has_import':
        has_import(sys.argv[2], sys.argv[3])
    else:
        sys.exit('unknown cmd')


if __name__ == '__main__':
    main()

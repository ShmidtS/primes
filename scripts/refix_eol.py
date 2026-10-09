#!/usr/bin/env python3
"""Restore original line endings for churned files and re-apply import
deletions preserving per-line endings."""
import re
import subprocess
import sys

churned = [ln.split()[0] for ln in sys.stdin if ln.strip()]
try:
    with open("scripts/prune_log.txt", encoding="utf-8") as fh:
        log = fh.readlines()
except FileNotFoundError:
    sys.exit("prune_log.txt not found")

removed = {}  # file -> set of imports removed
for ln in log:
    m = re.match(r"OK\s+([\w.]+) removed (Hagi\.[\w.]+)", ln.strip())
    if m:
        mod, imp = m.groups()
        f = "Hagi/" + mod[len("Hagi.") :].replace(".", "/") + ".lean"
        removed.setdefault(f, set()).add(imp)

for f in churned:
    if f not in removed:
        # churn without recorded removal (safety) -> just restore
        subprocess.run(["git", "checkout", "--", f], check=True)
        print("restored (no import removals recorded):", f)
        continue
    orig = subprocess.run(
        ["git", "show", "HEAD:" + f], capture_output=True, check=True
    ).stdout
    lines = orig.splitlines(keepends=True)
    out = []
    for raw_line in lines:
        body = raw_line.rstrip(b"\r\n")
        m = re.match(rb"import (Hagi\.[\w.]+)\s*$", body)
        if m and m.group(1).decode() in removed[f]:
            continue
        out.append(raw_line)
    try:
        with open(f, "wb") as fh:
            fh.writelines(out)
    except OSError as exc:
        sys.exit(f"cannot write {f}: {exc}")
    print("re-applied", len(removed[f]), "import removals:", f)

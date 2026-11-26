#!/usr/bin/env python3
"""StatusLint: every backticked identifier claimed in
STATUS.md / README.md / ALGORITHMS.md must exist in the Lean
code, or be listed in RUNTIME_NAMES (runtime repo), or match
a non-identifier pattern (paths, commands, single letters).
"""
import re
import sys
from pathlib import Path

from _shared import lean_files, read_baseline

ROOT = Path(__file__).resolve().parent.parent
HAGI = ROOT / "Hagi"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?"
    r"(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|structure|abbrev|instance|inductive|class|alias)"
    r"\s+([A-Za-z_][A-Za-z0-9_'′?]*)", re.M)


def lean_names() -> set:
    names = set()
    for d in (HAGI, ROOT / "Primes"):
        for f in lean_files(d):
            txt = f.read_text(encoding="utf-8")
            names |= set(DECL_RE.findall(txt))
    return names


RUNTIME_NAMES = {
    "kill_vs_crash", "resume_safety", "safeRestore",
    "not_latest_is_best_allowed", "increment_envelope",
    "sum_w_pair_mid", "AssumptionScan", "AssumptionScan.py",
    "assumptions.lock",
    "certified_transfer_gate", "nl_budget",  # bench_bridge.py
    "steps_drop_vs_bound",
    "adaptive_span", "_cov_step_starts",
    "hier_span",
    "certified_warmup_sim_run", "finite_displacement_ce_upper",
    "tangent_range_sq",
    "cost_regime_w",
    "growth_gate_measure",
}

# Baseline of KNOWN doc/code mismatches (2026-10-05 snapshot,
# must SHRINK: fix the doc or add the name, then remove here).
BASELINE_FILE = Path(__file__).resolve().parent / "statuslint_baseline.txt"

SKIP_WORDS = {
    "hagi", "mathlib", "lake", "bash", "git", "python", "rg",
    "fd", "true", "false", "sorry", "info", "warning", "error",
    "propext", "classical", "quot", "one", "two",
}

IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_'′?]*)`")

# doc links / headings must reference REAL repo files.
# Markdown link targets [`name`](Hagi/Foo/Bar.lean) and `## Hagi/…​.lean`
# headings; anchors and queries stripped before the disk check.
PATH_RE = re.compile(r"(?:\]\(|^##\s+)(Hagi/[A-Za-z0-9_/]+\.lean)(?:[)#]|$)",
                     re.M)


def is_skip(ident: str) -> bool:
    low = ident.lower()
    if low in SKIP_WORDS:
        return True
    # a backticked name that is an actual Hagi/Primes module
    if any((ident + ".lean") == f.name
           for d in (HAGI, ROOT / "Primes") for f in lean_files(d)):
        return True
    # hypothesis-pattern fragments and suffix references
    if ident.startswith("_") or ident.startswith("h_emp_")             or ident.startswith("h_model_") or ident == "h_emp_":
        return True
    # paths / numbers / non-identifier heads
    if any(ch in ident for ch in "./\\:") or ident[0].isdigit():
        return True
    # single letters and 2-letter math locals
    return len(ident) <= 2


def check(fname: str, names: set, baseline: set) -> list:
    txt = (ROOT / fname).read_text(encoding="utf-8")
    missing = []
    for m in PATH_RE.finditer(txt):
        path = m.group(1)
        if not (ROOT / path).is_file():
            missing.append((fname, path))
    if missing:
        return missing
    for m in IDENT.finditer(txt):
        ident = m.group(1)
        if ident in names or ident in RUNTIME_NAMES:
            continue
        if ident in baseline:
            continue
        if is_skip(ident):
            continue
        missing.append((fname, ident))
    return missing


def load_baseline() -> set:
    if BASELINE_FILE.exists():
        return read_baseline(BASELINE_FILE)
    return set()


def main() -> int:
    names = lean_names()
    baseline = load_baseline()
    if not names:
        print("STATUSLINT: FAIL (could not collect Lean names)")
        return 1
    missing = []
    for f in ("STATUS.md", "README.md", "ALGORITHMS.md"):
        missing += check(f, names, baseline)
    if missing:
        print("STATUSLINT: FAIL")
        for f, i in sorted(set(missing)):
            if i.startswith("Hagi/") and i.endswith(".lean"):
                print(f"  {f}: path `{i}` does not exist on disk")
            else:
                print(f"  {f}: `{i}` not found in Hagi/ or RUNTIME_NAMES")
        return 1
    print("STATUSLINT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())

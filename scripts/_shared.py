#!/usr/bin/env python3
"""Shared primitives for scripts/ linters and tools (v5 W5).

Deliberately NOT a lint-lib: only stable, duplication-free
constants/regex/filesystem/comment-stripping primitives live
here. Linter logic stays in its own script (plan v5 W5).
"""
import re
from pathlib import Path

# Module-name tokens shared by every import/namespace regex (LayerLint,
# ClosureReport, ReachLint, Metrics x2). The surrounding regexes differ in
# anchors and capture groups on purpose and stay in their own scripts.
MODULE_SUFFIX = r"[A-Za-z0-9_.]+"
HAGI_MODULE = r"Hagi\." + MODULE_SUFFIX

# Byte-identical declaration regex shared by DupLint and Metrics.
# Variants in Freeze/StatusLint/DocLint/AssumptionScan differ in
# modifier sets and capture groups on purpose — do not unify.
DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(theorem|lemma|def|structure|abbrev|instance|inductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_\'!?]*)',
    re.M,
)

# C217/C239/C240 quarantine: dirs outside the namespace/reach rules.
# Single source for NsLint and ReachLint (comment drift between the
# two copies was measured before extraction).
LEGACY_PREFIX = "Hagi/Legacy/"
BENCH_PREFIX = "Hagi/Benchmarks/"
RESEARCH_PREFIX = "Hagi/Research/"


def lean_files(base: Path) -> list:
    """Sorted list of *.lean files under base (deterministic order)."""
    return sorted(base.rglob("*.lean"))


def read_baseline(path) -> set:
    """Stripped, non-empty lines of a baseline file (StatusLint, NsLint)."""
    with open(path, encoding="utf-8") as fh:
        return {line.strip() for line in fh if line.strip()}


def strip_comments(text):
    """Strip nested Lean comments without touching quoted strings.

    Adapted from https://github.com/jayeshmepani/comment-remover
    (C-style string preservation), with Lean's nested comment depth.
    Canonical home moved here from Freeze.py (v5 W5); Freeze
    re-exports it for existing `from Freeze import strip_comments`
    consumers.
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

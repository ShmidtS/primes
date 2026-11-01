#!/usr/bin/env python3
"""AlphaDup — α-signature duplicate detector (audit M0).

Normalizes bound-variable names in theorem signatures
(renames binders positionally), strips attributes and
whitespace, and groups declarations whose normalized
statement types match. Report-only; exit code always 0.

This is a heuristic (matches the external audit's method);
true equivalence needs Lean-level checking.
"""
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.join(os.path.dirname(__file__), "..", "Hagi")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)",
    re.M,
)

ID = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")


def normalize(stmt: str) -> str:
    # positional renaming of identifiers that are not known globals:
    # cheap heuristic — rename ALL identifiers consistently by order of
    # first occurrence, EXCEPT keywords and numeric structure.
    KEYWORDS = {
        "theorem", "lemma", "∀", "∃", "→", "↔", "∧", "∨", "¬", "≤", "<",
        "≥", ">", "=", "≠", "+", "-", "*", "/", "∑", "ℝ", "ℕ", "Prop",
        "Type", "Set", "fun", "have", "by", "at", "in", "let", "match",
        "with", "and", "or", "if", "then", "else", "Int", "Nat", "Real",
        "0", "1", "2",
    }
    mapping = {}
    def repl(m):
        w = m.group(0)
        if w in KEYWORDS:
            return w
        if w not in mapping:
            mapping[w] = f"x{len(mapping)}"
        return mapping[w]
    return " ".join(ID.sub(repl, stmt).split())


def main() -> None:
    rows = []
    for dirpath, _, files in os.walk(ROOT):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, ROOT).replace(os.sep, "/")
            txt = open(p, encoding="utf-8", errors="replace").read()
            for m in DECL.finditer(txt):
                name, kind = m.group(1), "theorem"
                rest = txt[m.start():]
                stmt = rest.split(":=", 1)[0]
                # cut inside attribute `since :=`
                stmt = re.sub(r"\(since := [^)]*\)", "", stmt)
                rows.append((name, rel, normalize(stmt)))

    groups = defaultdict(list)
    for name, rel, sig in rows:
        groups[sig].append((name, rel))

    dups = {s: v for s, v in groups.items() if len(v) > 1}
    n_extra = sum(len(v) - 1 for v in dups.values())
    cross = sum(1 for v in dups.values()
                if len({r for _, r in v}) > 1)
    print(f"declarations scanned: {len(rows)}")
    print(f"alpha-duplicate groups: {len(dups)}")
    print(f"redundant copies: {n_extra}")
    print(f"cross-file groups: {cross}")
    print()
    for s, v in sorted(dups.items(), key=lambda kv: -len(kv[1])):
        print(f"group ({len(v)}):")
        for name, rel in v:
            print(f"  {name}  [{rel}]")


if __name__ == "__main__":
    main()

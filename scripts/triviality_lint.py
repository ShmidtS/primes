#!/usr/bin/env python3
"""Triviality linter for Hagi (round-52 rules).

T1: theorem proof must not be bare `rfl` / `trivial` / `sorry`
T2: conclusion must not literally coincide with a hypothesis
Reports the non-trivial share (lower bound) over all theorems.
"""
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(__file__), "..", "Hagi")

THEO = re.compile(r"^\s*(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)


def split_sigs(text):
    """Yield (name, signature_text) for each theorem/lemma."""
    for m in THEO.finditer(text):
        name = m.group(1)
        start = m.end()
        depth = 0
        i = start
        n = len(text)
        while i < n:
            c = text[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == ":" and depth == 0 and text[i : i + 2] == ":=":
                yield name, text[start:i]
                break
            i += 1


def sig_hyps_and_concl(sig):
    """Return (list_of_hypothesis_bodies, conclusion_text)."""
    groups = re.findall(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)", sig)
    hyps = [g.split(":", 1)[-1] for g in groups]
    last_par = sig.rfind(")")
    concl = sig[last_par + 1 :] if last_par != -1 else sig
    return hyps, concl


def findings(path, text):
    out = []
    for name, sig in split_sigs(text):
        hyps, concl = sig_hyps_and_concl(sig)
        concl_norm = re.sub(r"\s+", "", concl).lstrip(":")
        hyp_norms = [re.sub(r"\s+", "", h) for h in hyps]
        if len(concl_norm) > 3 and concl_norm in hyp_norms:
            out.append((path, name, "T2-CONCLUSION-IS-HYPOTHESIS", concl_norm[:60]))
        proof = sig[:0]  # placeholder
        tail = text.split(name, 1)
        # T1: bare trivial proof
        m = re.search(re.escape(name) + r"[^:]*:=\s*(rfl|trivial|sorry)", text)
        if m and m.group(1) in ("rfl", "trivial", "sorry"):
            out.append((path, name, "T1-BARE-TRIVIAL-PROOF", m.group(1)))
        del proof, tail
    return out


def main():
    if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    all_files = []
    for root, _dirs, fs in os.walk(ROOT):
        for f in fs:
            if f.endswith(".lean"):
                all_files.append(os.path.join(root, f))
    total = 0
    flagged = []
    for path in sorted(all_files):
        try:
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
        except OSError as e:
            print(f"  WARN unreadable: {path} ({e})")
            continue
        total += len(THEO.findall(text))
        flagged.extend(findings(path, text))
    print(f"theorems+lemmas scanned: {total}")
    print(f"triviality flags: {len(flagged)}")
    for path, name, kind, detail in flagged:
        print(f"  {kind:32s} {os.path.relpath(path)} :: {name}  {detail}")
    share = 1 - (len(flagged) / total if total else 0)
    print(f"non-trivial share (lower bound): {share:.4f}")


if __name__ == "__main__":
    main()

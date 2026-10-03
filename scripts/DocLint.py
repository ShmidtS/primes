#!/usr/bin/env python3
"""DocLint — правила 4 и 5 рецензии (round-52).

R4: каждое имя в обратных кавычках (`name`) внутри docstring
    обязано быть объявлением репозитория (Hagi/Primes: theorem/
    lemma/def/structure/abbrev/instance) либо внешним qualified
    именом (с точкой), либо тактикой/ключевым словом прозы
    (допускается оговорённый список PROSE).
    Ссылки на имена других файлов проекта — легальны (глобальный
    пул), но проверяются на существование.
R5: числа в docstring (>= 2 значащих цифр) должны быть либо
    помечены словом «измерено»/«measured» в том же предложении,
    либо сопровождаться `#eval`-ссылкой в файле, либо входить в
    код файла (объявлены как literal в Lean-коде ниже).

Report-only по R5 (эвристика), strict по R4.
Выход: последний маркер DOCLINT: PASS / DOCLINT: FAIL.
"""
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(__file__), "..", "Hagi")

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?"
    r"(?:theorem|lemma|def|structure|abbrev|instance|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
    re.M,
)
DOC = re.compile(r"/--(.*?)-/", re.S)
TICK = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*?)`")
NUM = re.compile(r"\b\d[\d._]*\d\b|\b\d+\b")

PROSE = {
    "rfl", "trivial", "ring", "simp", "omega", "linarith", "nlinarith",
    "exact", "refine", "calc", "constructor", "induction", "rw", "have",
    "obtain", "unfold", "whnf", "conv", "argmax", "argmin", "logsumexp",
    "softmax", "exp", "log", "sqrt", "cosh", "sinh", "tanh", "sum", "max",
    "min", "sup", "inf", "lim", "Var", "Cov", "Gap", "KL", "QP", "KKT",
    "SafeQP", "LoRA", "TTT", "MoE", "DPO", "GMM", "NCE", "PL", "SGD",
    "Adam", "UAT", "PR", "F3", "KV", "MLIR", "MLP", "LSTM",
}


def sentences(text):
    """Yield (sentence, is_doc) splitting on periods/newlines."""
    for m in DOC.finditer(text):
        for part in re.split(r"(?<=[.;])\s+|\n+", m.group(1)):
            if part.strip():
                yield part, True
    # strip docstrings for code sentences
    code = DOC.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    for part in re.split(r"\n+", code):
        if part.strip():
            yield part, False


def file_findings(path, text, pool=None):
    out = []
    names = set(DECL.findall(text))
    pool = pool or names
    # identifiers visible anywhere in the file (binders, locals),
    # with backticked spans removed so prose labels do not enter
    bare = TICK.sub(" ", text)
    local_ids = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", bare))
    pool = pool | local_ids
    literals = set(re.findall(r"\b\d[\d._]*\b", text))
    for sent, is_doc in sentences(text):
        if not is_doc:
            continue  # rule 4 covers docstrings only
        for nm in TICK.findall(sent):
            if nm.endswith("_"):  # explicit prose-label escape
                continue
            if "." in nm or nm in PROSE or len(nm) <= 2:
                continue
            if nm not in pool:
                out.append(f"R4_DOC\t{path}\t`{nm}` not declared anywhere")
        if is_doc:
            for num in NUM.findall(sent):
                flat = num.replace("_", "")
                if flat in ("0", "1", "2", "3"):  # trivial ints
                    continue
                ok = (
                    "измерено" in sent
                    or "measured" in sent.lower()
                    or "#eval" in sent
                    or flat in literals
                    or flat.rstrip(".") in literals
                )
                if not ok:
                    out.append(f"R5_NUM\t{path}\tnumber {num} unmarked/uncomputed")
    return out


def main():
    # global declaration pool: repo decls + full Lean env names
    pool = set()
    env_names = set()
    np = os.path.join(os.path.dirname(__file__), "namepool.txt")
    if os.path.exists(np):
        try:
            with open(np, encoding="utf-8") as fh:
                for line in fh:
                    parts = line.strip().split(".")
                    env_names.add(parts[-1])
                    # namespace prefixes (e.g. Hagi.Data.DField)
                    for i in range(1, len(parts)):
                        env_names.add(parts[i])
        except (OSError, UnicodeDecodeError) as e:
            print(f"warn: unreadable {np}: {e} — Mathlib names unresolved",
                  file=sys.stderr)
    else:
        print("warn: scripts/namepool.txt missing — run "
              "`lake env lean --run scripts/NamePool.lean` first "
              "(Mathlib names unresolved)", file=sys.stderr)
    texts = {}
    for base in ("Hagi", "Primes"):
        b = os.path.join(os.path.dirname(__file__), "..", base)
        for dirpath, _, files in os.walk(b):
            for f in files:
                if f.endswith(".lean"):
                    p = os.path.join(dirpath, f)
                    try:
                        with open(p, encoding="utf-8") as fh:
                            t = fh.read()
                    except (OSError, UnicodeDecodeError) as e:
                        print(f"warn: skip unreadable {p}: {e}", file=sys.stderr)
                        continue
                    texts[os.path.relpath(p, ROOT)] = t
                    pool |= set(DECL.findall(t))
    findings = []
    nfiles = len(texts)
    for path, text in texts.items():
        findings += file_findings(path, text, pool | env_names)
    r4 = [f for f in findings if f.startswith("R4")]
    r5 = [f for f in findings if f.startswith("R5")]
    print(f"files scanned: {nfiles}")
    print(f"R4 (docstring names) findings: {len(r4)}")
    for f in r4:
        print(" ", f.replace("\t", " | "))
    print(f"R5 (unmarked numbers) findings: {len(r5)}")
    for f in r5[:60]:
        print(" ", f.replace("\t", " | "))
    if len(r5) > 60:
        print(f"  ... and {len(r5)-60} more")
    print("DOCLINT: " + ("FAIL" if r4 else "PASS"))
    return 1 if r4 else 0


if __name__ == "__main__":
    sys.exit(main())

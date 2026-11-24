"""Doc anchors: every `Hagi/…/File.lean:N` in the docs (plus the short `File.lean:N`
and `(:N)` forms that inherit the last full path on the same doc line) is bound
in scripts/docanchors.lock to the Lean declaration it points at.  The lock is
keyed by the anchor itself, so neither editing the docs nor a Lean docstring
pass can move an anchor silently: line numbers that no longer land on the same
declaration fail the gate until they are re-mapped BY NAME.

  python scripts/DocAnchorCheck.py                          # check -> DOCANCHORS: PASS/FAIL
  python scripts/DocAnchorCheck.py --reanchor BASE [--base2 B2] [--write]
                                                            # old line numbers at git BASE
                                                            # -> work tree, by declaration name
  python scripts/DocAnchorCheck.py --update                 # rewrite the lock (after an
                                                            # audited --reanchor --write)

Re-anchoring never uses a line offset.  The declaration (or namespace / section
line) found at the old line is looked up again in the work tree.  A line that
pointed at a docstring opener or at the declaration keyword keeps that role; any
other line of the same declaration keeps its line when its text is unique in the
chunk (`text`), else falls back to the docstring opener / keyword
(`coarsened` in the report)."""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "docanchors.lock"
FIXED_DOCS = ["STATUS.md", "ALGORITHMS.md", "README.md", "RELATED.md",
              ".omc/analysis/era-index.md"]

MOD = (r"(?:private |protected |noncomputable |unsafe |meta |partial |@\[[^\]]*\]\s*|"
       r"extern\s+\S+\s+)*")
DECL = re.compile(r"^" + MOD +
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example)\s+"
                  r"([A-Za-z_][A-Za-z0-9_'?]*)")
HEADER = re.compile(r"^(?:namespace|section|end|open|import|set_option|noncomputable section)\b")
FULL = re.compile(r"(?<![A-Za-z0-9_/.-])(Hagi/[A-Za-z0-9_/]+\.lean):(\d+)(?:-(\d+))?")
SHORT = re.compile(r"(?<![A-Za-z0-9_/.-])([A-Z][A-Za-z0-9]*\.lean):(\d+)(?:-(\d+))?")
CONT = re.compile(r"(?:(?<![\w.:])(:\d{1,4})(?:-(\d+))?(?![\d.])|\(:(\d{1,4})(?:-(\d+))?\))")
STATUS = "DOCANCHORS: "
SECTION = "§"


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout


def read(commit, f):
    if commit is None:
        return ROOT.joinpath(f).read_text(encoding="utf-8").split("\n")
    return git("show", f"{commit}:{f}").split("\n")


def docs():
    return FIXED_DOCS + [p.relative_to(ROOT).as_posix()
                         for p in sorted((ROOT / "docs").glob("*.md"))]


class Chunk:
    """One top-level item: optional docstring + declaration (with its proof)."""
    __slots__ = ("start", "end", "doc", "decl", "name")

    def __init__(s, start):
        s.start, s.end, s.doc, s.decl, s.name = start, start, None, None, None


def chunks(lines):
    """Top-level chunks.  A new chunk starts at a docstring opener, a declaration
    keyword or a structural line (namespace / section / import ...); any other
    column-0 line continues the current chunk; a blank line closes it.  A
    docstring chunk is then merged with the declaration chunk that follows it
    without a blank line, so a chunk = docstring + declaration (+ proof)."""
    out, cur, depth = [], None, 0

    def flush():
        nonlocal cur
        if cur is not None:
            out.append(cur)
        cur = None

    for i, l in enumerate(lines, 1):
        s = l.strip()
        closing = depth > 0 and s.startswith("-/")
        top = bool(s) and not l[0].isspace() and (depth == 0 or closing) \
            and not s.startswith("--")
        s2 = s[2:].strip() if closing else s
        waiting = cur is not None and cur.doc is not None and cur.name is None
        m = DECL.match(s2) if top and not s2.startswith("variable") else None
        if top and s.startswith("/-") and not waiting:
            flush()
            cur = Chunk(i)
            if s.startswith("/--"):
                cur.doc = i
            else:
                cur.name = SECTION + s              # module / section header
        elif top and (m or HEADER.match(s2)):
            if waiting and m:
                cur.name, cur.decl = m.group(1), i
            else:
                flush()
                cur = Chunk(i)
                if m:
                    cur.name, cur.decl = m.group(1), i
                else:
                    cur.name = SECTION + s
        if cur is not None:
            cur.end = i
        if not s and depth == 0:
            flush()
        if ("/-" in l or "-/" in l) and not s.startswith("--"):
            depth = max(0, depth + l.count("/-") - l.count("-/"))
    flush()
    merged = []
    for c in out:
        p = merged[-1] if merged else None
        if p is not None and p.doc is not None and p.name is None and c.name \
                and not c.name.startswith(SECTION) and c.doc is None and c.start == p.end + 1:
            p.name, p.decl, p.end = c.name, c.decl, c.end
        else:
            merged.append(c)
    return merged


def index(lines):
    """(chunks, name -> chunks in order, line -> chunk)."""
    cs, byname, at = chunks(lines), {}, {}
    for c in cs:
        if c.name:
            byname.setdefault(c.name, []).append(c)
        for k in range(c.start, c.end + 1):
            at[k] = c
    return cs, byname, at


PROBLEM = []
FILES = []                                  # Hagi modules (set in main)


def scan(doc, lines, base):
    """Anchor occurrences: (doc line, start, end, file, n, n2), left to right.
    A `(:N)` / `:N` continuation inherits the file of the anchor right before it
    (separated only by `, ` / `;` / `(` / ` – `); `:a–:b` is one range."""
    res = []
    for ln, line in enumerate(lines, 1):
        raw = []
        for m in FULL.finditer(line):
            raw.append((m.start(), m.end(), m.group(1), int(m.group(2)), m.group(3)))
        for m in SHORT.finditer(line):
            if any(s <= m.start() < e for s, e, *_ in raw):
                continue
            c = base.get(m.group(1), [])
            if len(c) != 1:
                PROBLEM.append(f"{doc}:{ln}: short form `{m.group(0)}` -> {c or 'no such file'}")
                continue
            raw.append((m.start(), m.end(), c[0], int(m.group(2)), m.group(3)))
        for m in CONT.finditer(line):
            prev = max((r for r in raw if r[1] <= m.start()), key=lambda r: r[1], default=None)
            if prev is None:
                continue
            gap = line[prev[1]:m.start()]
            if not re.fullmatch(r"[\s,;()–-]*", gap):
                continue
            g = m.group(1) or m.group(3)
            n, n2 = int(g.lstrip(":")), m.group(2) or m.group(4)
            if "–" in gap or "-" in gap.strip():
                raw.remove(prev)
                raw.append((prev[0], m.end(), prev[2], prev[3], n2 or str(n)))
                continue
            raw.append((m.start(), m.end(), prev[2], n, n2))
        for s, e, f, n, n2 in sorted(raw):
            res.append((ln, s, e, f, n, n2))
    return res


def aim(lines, n):
    """What line N points at in `lines`: (name, role, text, next-name) or None.
    role: doc = docstring opener, decl = declaration keyword, end = last line
    of the declaration, inner = any other line of the chunk.  A line between
    chunks belongs to the NEXT chunk, so a blank line or a since-deleted header
    lands on what follows it."""
    cs, _, at = index(lines)
    c = at.get(n)
    if c is None:
        c = next((x for x in cs if x.start > n), None)
        role = "inner"
    else:
        role = "doc" if c.doc == n else "decl" if c.decl == n else "inner"
    if role == "inner" and c.end == n:
        role = "end"                      # last line of the declaration
    if c is None or not c.name:
        return None
    nxt = next((x.name for x in cs if x.start > c.start and x.name
                and not x.name.startswith(SECTION)), None)
    return c.name, role, lines[n - 1].strip(), nxt


def landing(lines, tgt, f):
    """Where the same target lands now: (file, line, how).
    A name that left this module is looked up in the other Hagi modules (a
    split); a since-deleted section header lands on the first declaration it
    introduced."""
    name, role, text, nxt = tgt
    _, byname, _ = index(lines)
    c = (byname.get(name) or [None])[0]
    if c is None and not name.startswith(SECTION):
        for g in FILES:
            if g == f:
                continue
            if index(read(None, g))[1].get(name):
                return landing(read(None, g), tgt, g)[0:2] + ("moved",)
        return f, None, "NAME-LOST"
    if c is None and nxt:
        c = (byname.get(nxt) or [None])[0]
        if c is None:
            return f, None, "NAME-LOST"
        return f, c.doc or c.decl, "header->decl"
    if c is None:
        return f, None, "NAME-LOST"
    if role == "doc" and c.doc:
        return f, c.doc, "doc"
    if role == "end":
        return f, c.end, "end"
    if role == "decl" and c.decl:
        return f, c.decl, "decl"
    if role == "inner":
        hits = [i for i in range(c.start, c.end + 1) if text and lines[i - 1].strip() == text]
        if len(hits) == 1:
            return f, hits[0], "text"
    return f, c.doc or c.decl or c.start, "coarsened"


def main():
    global FILES
    ap = argparse.ArgumentParser()
    ap.add_argument("--reanchor", metavar="BASE")
    ap.add_argument("--base2", help="fallback baseline for files absent in BASE")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--update", action="store_true")
    a = ap.parse_args()
    FILES = [f for f in git("ls-files", "Hagi").split("\n") if f.endswith(".lean")]
    base = {}
    for f in FILES:
        base.setdefault(f.split("/")[-1], []).append(f)
    cache = {}

    def old(f):
        for c in (a.reanchor, a.base2):
            if not c:
                continue
            k = (c, f)
            if k not in cache:
                cache[k] = read(c, f) if subprocess.run(
                    ["git", "cat-file", "-e", f"{c}:{f}"], cwd=ROOT,
                    capture_output=True).returncode == 0 else None
            if cache[k] is not None:
                return cache[k]
        return None

    if a.reanchor:
        occ_n = moved = coarsened = 0
        for d in docs():
            raw = ROOT.joinpath(d).read_bytes().decode("utf-8")
            eol = "\r\n" if "\r\n" in raw else "\n"
            lines = raw.replace("\r\n", "\n").split("\n")
            occ = scan(d, lines, base)
            occ_n += len(occ)
            edits = {}
            for ln, s, e, f, n, n2 in occ:
                o = old(f)
                t = aim(o, n) if o and 0 < n <= len(o) else None
                if t is None:
                    PROBLEM.append(f"UNMAPPED {d}:{ln} {f}:{n} (baseline lines: {len(o) if o else 'absent'})")
                    continue
                g, m, how = landing(read(None, f), t, f)
                if m is None:
                    PROBLEM.append(f"LOST {d}:{ln} {f}:{n} [{t[0]}]")
                    continue
                coarsened += how == "coarsened"
                end = m + (int(n2) - n) if n2 else None
                if m != n or g != f:
                    moved += 1
                    edits.setdefault(ln, []).append((s, e, f, g, n, n2, m, end))
                print(f"{how:12} {d}:{ln} {f}:{n}{('-' + n2) if n2 else ''} -> "
                      f"{g.split('/')[-1]}:{m}{('-' + str(end)) if end else ''} [{t[0]}]")
            if a.write:
                for ln, es in edits.items():
                    l = lines[ln - 1]
                    for s, e, f, g, n, n2, m, end in sorted(es, key=lambda x: -x[0]):
                        tok = l[s:e]
                        tok = re.sub(rf"(?<!\d){n}(?!\d)", str(m), tok, count=1)
                        if n2:
                            tok = re.sub(rf"(?<!\d){n2}(?!\d)", str(end), tok, count=1)
                        if g != f:
                            tok = tok.replace(f.split("/")[-1], g.split("/")[-1])
                        l = l[:s] + tok + l[e:]
                    lines[ln - 1] = l
                if edits:
                    ROOT.joinpath(d).write_bytes(eol.join(lines).encode("utf-8"))
        print(f"reanchor: {occ_n} occurrences, moved {moved}, coarsened {coarsened}, "
              f"problems {len(PROBLEM)}")
        for p in PROBLEM:
            print(p)
        return 0

    lock, occ_n = {}, 0
    for d in docs():
        for ln, s, e, f, n, n2 in scan(d, read(None, d), base):
            occ_n += 1
            t = aim(read(None, f), n)
            lock[f"{f}:{n}"] = f"{t[0]}|{t[1]}" if t else "NONE"
    if a.update:
        LOCK.write_text("".join(f"{k}\t{v}\n" for k, v in sorted(lock.items())),
                        encoding="utf-8")
        print(f"DOCANCHORS: lock written, {len(lock)} anchors / {occ_n} occurrences")
        return 0
    want = dict(l.split("\t") for l in LOCK.read_text(encoding="utf-8").split("\n") if l)
    stale = sorted(k for k, v in lock.items() if want.get(k) != v)
    gone = sorted(k for k in want if k not in lock)
    for k in (stale + gone)[:200]:
        print(f"  stale {k}: was {want.get(k)}, now {lock.get(k)}")
    for p in PROBLEM:
        print("  ", p)
    ok = not stale and not gone and not PROBLEM
    print(f"{STATUS}{'PASS' if ok else 'FAIL'} ({len(lock)} anchors, {len(stale)} stale, "
          f"{len(gone)} gone, {len(PROBLEM)} unresolved)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.exit(main())

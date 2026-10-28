#!/usr/bin/env python3
"""ChallengeCheck (audit v6, step 2): Comparator-challenges.

For each challenge in Challenge/challenges.json:
  1. the named theorem exists and its axioms are a subset of
     the allowed list (propext, Classical.choice, Quot.sound);
  2. every pinned type (canonical #check string, whitespace-
     normalized) still matches — a silent change of the premise
     contract or the statement fails the gate.

The challenge statement itself is pinned by the build: the
conclusion is spelled out in the challenge file and proven by
delegation, so any change of meaning breaks compilation.

Output: "CHALLENGE: PASS n/n" or "CHALLENGE: FAIL" + reasons.
"""
import json, re, subprocess, sys, tempfile, os

sys.stdout.reconfigure(encoding="utf-8")

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.environ.get("LEAN_BIN", "lake")

def normalize(s: str) -> str:
    return re.sub(r"\s+", " ", s.strip())

def lean_probe(imports, cmds):
    src = "\n".join(f"import {i}" for i in imports) + "\n" + "\n".join(cmds) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=ROOT) as f:
        f.write(src)
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=1800,
                           encoding="utf-8", errors="replace")
        return r.stdout + r.stderr
    finally:
        os.unlink(path)

def main():
    with open(os.path.join(ROOT, "Challenge", "challenges.json"), encoding="utf-8") as f:
        data = json.load(f)
    ok = True
    n = 0
    for ch in data["challenges"]:
        n += 1
        thm = ch["theorem"]
        mod = ch["module"]
        allowed = set(ch["allowed_axioms"])
        out = lean_probe([mod], [f"#print axioms {thm}"])
        m = re.search(r"depends on axioms: \[(.*?)\]", out)
        if not m:
            print(f"CHALLENGE FAIL {ch['name']}: cannot resolve {thm}\n{out[:500]}")
            ok = False
            continue
        axioms = set(a.strip() for a in m.group(1).split(",") if a.strip())
        extra = axioms - allowed
        if extra:
            print(f"CHALLENGE FAIL {ch['name']}: extra axioms {sorted(extra)}")
            ok = False
        for dep, pinned in ch.get("pinned_types", {}).items():
            out = lean_probe([mod], [f"#check @{dep}"])
            # capture everything after '@dep :'
            m2 = re.search(re.escape(f"@{dep}") + r"\s*:\s*(.*)", out, re.S)
            if not m2:
                print(f"CHALLENGE FAIL {ch['name']}: cannot #check {dep}\n{out[:500]}")
                ok = False
                continue
            actual = normalize(m2.group(1))
            if actual != normalize(pinned):
                print(f"CHALLENGE FAIL {ch['name']}: pinned type of {dep} changed")
                print(f"  pinned: {normalize(pinned)}")
                print(f"  actual: {actual}")
                ok = False
    print(f"CHALLENGE: {'PASS' if ok else 'FAIL'} {n if ok else 0}/{n}")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()

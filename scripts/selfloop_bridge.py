"""Selfloop telemetry bridge: REAL self-development-loop telemetry
(HAGI_v2 experiments/selfloop_result.json) fed to the Lean certificate checker
Hagi.Runtime.CertChecker as an exact-Fraction CertStepData trajectory.
Run `python scripts/selfloop_bridge.py [INPUT]`: prints the JSON trajectory + holds.
`--emit-lean PATH` writes a Lean witness (#eval checkTrajectory + norm_num theorem)
that must pass; `--corrupt PATH` a negative control the checker must reject.
"""

# Mapping (semantics: C:\\HAGI_v2 THEORY_ALIGNMENT.md §1, read-only):
# T   = len(rounds) of the parsed json (the LIVE file has 4
#       rounds — 3 COMMIT + 1 LEVER_CHANGE; the 149/150 figure
#       in the docs belongs to a different 150-round run);
# obj = T − #COMMITs before round r  — the processor's
#       `unsolved_objective` telescope counter;
# drop = 1 EXACTLY per COMMIT round (THEORY_ALIGNMENT §1:
#       "unsolved_objective − 1.0 за коммит, без clamp") — a
#       COMMIT solves one generation; no fractional drop is
#       invented;
# obj' = obj − 1 (the telescope stays additive);
# budget/budget' = (rounds remaining incl./excl. this) / T;
# risk/risk' = wasted_candidates pre/post ÷ base_budget —
#       waste-fraction telemetry read from the gate record
#       (string "a -> b"), the ONLY risk-like per-round field
#       actually present.

# HONESTY PINS (fail-closed, never fabricate):
#  - a round missing any required field (gate.action,
#    gate.wasted_candidates, base_budget) aborts the bridge;
#  - a LEVER_CHANGE / HOLD round has NO certified drop => it is
#    NOT a step (the cert-tern HOLD rule: excluded from the
#    trajectory, logged in `holds` telemetry -- checkStep demands
#    0 < drop);
#  - exact_accuracy / experts are present but NOT used as
#    objective readouts (they are gate preconditions, not
#    telescope levels);
#  - interpretation contract = Hagi.Runtime.CertChecker
#    `Describes`/`mkCertStep`: the rational readouts cast to the
#    real levels of the certified AdditiveLedger telescope.


import argparse
import json
import sys
from fractions import Fraction as F

DEFAULT_INPUT = r"C:\HAGI_v2\experiments\selfloop_result.json"


def parse_wasted(s):
    """Parse the gate's wasted_candidates string "a -> b"."""
    try:
        a, b = s.split("->")
        return F(int(a.strip())), F(int(b.strip()))
    except Exception:
        sys.exit(f"ABORT: unparsable wasted_candidates: {s!r}")


def build_trace(doc):
    """json → (start, steps, holds, meta). Fail-closed on any
    missing field; COMMIT ⇒ step (drop = 1), anything else ⇒
    hold (excluded from the trajectory)."""
    rounds = doc.get("rounds")
    if not rounds:
        sys.exit("ABORT: no rounds in telemetry")
    base_budget = doc.get("base_budget")
    if not isinstance(base_budget, int) or base_budget <= 0:
        sys.exit(f"ABORT: missing/invalid base_budget: {base_budget!r}")
    T = F(len(rounds))
    start = T
    steps, holds = [], []
    commits = 0
    for rec in rounds:
        r = rec.get("round")
        gate = rec.get("gate") or {}
        action = gate.get("action")
        wc = gate.get("wasted_candidates")
        if r is None or action is None or not isinstance(wc, str):
            sys.exit(f"ABORT: round record missing required "
                     f"fields (round/action/wasted_candidates): "
                     f"{rec!r}")
        wa, wb = parse_wasted(wc)
        budget = F(T - r + 1) / T
        budget2 = F(T - r) / T
        if action == "COMMIT":
            obj = start - commits
            obj2 = obj - 1              # telescope: −1.0 per COMMIT
            d = {"round": r, "action": action,
                 "obj": obj, "obj'": obj2, "drop": obj - obj2,
                 "budget": budget, "budget'": budget2,
                 "risk": wa / base_budget, "risk'": wb / base_budget}
            # inline mirror of Hagi.Runtime.checkStep
            if not (0 < d["drop"] and d["drop"] <= d["obj"] - d["obj'"]
                    and 0 <= d["budget'"] and 0 <= d["risk'"]):
                sys.exit(f"ABORT: COMMIT round {r} failed the "
                         f"certified check mirror: {d}")
            steps.append(d)
            commits += 1
        else:
            holds.append({"round": r, "action": action,
                          "reason": gate.get("reason", ""),
                          "wasted_candidates": wc,
                          "note": "no certified drop (rollback): "
                                  "HOLD/LEVER_CHANGE, excluded "
                                  "from the trajectory (checkStep "
                                  "demands 0 < drop)"})
    if not steps:
        sys.exit("ABORT: no COMMIT rounds — empty trajectory")
    meta = {"T": len(rounds), "commits": commits,
            "base_budget": base_budget,
            "converged": doc.get("converged")}
    return start, steps, holds, meta


def rat(q):
    """Fraction -> exact Lean rational literal."""
    return (f"({q.numerator}/{q.denominator} : ℚ)"
            if q.denominator != 1 else f"({q.numerator} : ℚ)")


FIELDS = ["obj", "obj'", "drop", "budget", "budget'", "risk", "risk'"]


def lean_step(d):
    return "  ⟨" + ", ".join(rat(d[f]) for f in FIELDS) + "⟩"


def emit_lean(path, start, traj, name_suffix="", ok=True):
    """Witness: literal trajectory from the REAL telemetry +
    #eval + norm_num theorem (same pattern as bench_bridge.py)."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def selfloopStart{name_suffix} : ℚ := {rat(start)}\n\n"
                f"def selfloopTrajectory{name_suffix} : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "\n]\n\n"
                f"#eval checkTrajectory selfloopStart{name_suffix} "
                f"selfloopTrajectory{name_suffix}\n\n")
        thm = "valid" if ok else "invalid"
        val = "true" if ok else "false"
        f.write(f"theorem selfloop_traj_{thm}{name_suffix} :\n"
                f"    checkTrajectory selfloopStart{name_suffix} "
                f"selfloopTrajectory{name_suffix} = {val} := by\n"
                "  simp only [checkTrajectory, checkStep, "
                f"selfloopStart{name_suffix}, "
                f"selfloopTrajectory{name_suffix}, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default=DEFAULT_INPUT,
                    help="path to selfloop_result.json "
                         "(HAGI_v2 stays read-only)")
    ap.add_argument("--emit-lean", metavar="PATH")
    ap.add_argument("--corrupt", metavar="PATH")
    args = ap.parse_args()

    with open(args.input, encoding="utf-8") as f:
        doc = json.load(f)
    start, steps, holds, meta = build_trace(doc)
    print(json.dumps({
        "mode": "selfloop",
        "input": args.input,
        "meta": {k: str(v) for k, v in meta.items()},
        "start": str(start),
        "steps": len(steps), "holds": len(holds),
        "trajectory": [{k: str(v) for k, v in d.items()}
                       for d in steps],
        "holds_telemetry": holds,
    }, indent=1, ensure_ascii=False))

    if args.emit_lean:
        emit_lean(args.emit_lean, start, steps)
    if args.corrupt:
        bad = [dict(d) for d in steps]
        bad[-1]["drop"] = bad[-1]["drop"] + F(1)
        emit_lean(args.corrupt, start, bad, name_suffix="Bad",
                  ok=False)


if __name__ == "__main__":
    main()

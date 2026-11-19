#!/usr/bin/env python3
"""Bench bridge (C434, stage 9): a REAL minimal gradient-descent trainer
feeding the executable Lean certificate checker (Hagi.Runtime.CertChecker).

Pure stdlib: arithmetic is exact via fractions.Fraction — no floats, no
numpy. After each GD step the trainer serializes a CertStepData record
(obj, obj', drop, budget, budget', risk, risk') as exact rationals.

Modes:
  default            run T GD steps, print the JSON trajectory
  --emit-lean PATH   additionally write a Lean witness file with the
                     literal `benchTrajectory : List CertStepData`,
                     #eval checkTrajectory and a `decide` theorem
  --corrupt PATH     negative control: same trajectory but one drop
                     inflated so the checker MUST reject it (false)
  --mode cert-ce     C442: certified cross-entropy training loop — a
                     softmax-CE-style linear classifier trained by GD
                     with exact rational arithmetic, per-step checker
                     admission (abort on a non-certified step) and
                     holdout risk telemetry (C435 tie). See below.
"""

import argparse
import json
import sys
from fractions import Fraction as F

# Rational dataset: linear regression, model y ~ w*x, scalar w.
XS = [F(1), F(2), F(3)]
YS = [F(2), F(4), F(7)]
N = F(len(XS))
ETA = F(1, 10)  # learning rate (exact)


def loss(w):
    return sum(((w * x - y) ** 2 for x, y in zip(XS, YS)), F(0)) / N


def grad(w):
    return F(2) * sum(((w * x - y) * x for x, y in zip(XS, YS)), F(0)) / N


def train(steps):
    """Run `steps` GD iterations; return (start_obj, [step dicts])."""
    w = F(0)
    traj = []
    for t in range(steps):
        obj, budget, risk = loss(w), F(steps - t, steps), abs(w)
        w = w - ETA * grad(w)  # GD step, exact
        obj2, budget2, risk2 = loss(w), F(steps - t - 1, steps), abs(w)
        traj.append({
            "obj": obj, "obj'": obj2,
            "drop": obj - obj2,  # actual descent, not a slack claim
            "budget": budget, "budget'": budget2,
            "risk": risk, "risk'": risk2,
        })
    return traj[0]["obj"], traj


# ----------------------------------------------------------------
# C442: certified CE training loop (--mode cert-ce)
#
# PIN (honest approximation choice): softmax = exp is irrational on
# ℚ, so the classifier head uses the RATIONAL-SOFTMAX surrogate
# p_c = z_c² / Σ_j z_j²  with per-point loss 1 − p_true — an exact
# rational [0,1]-valued CE/0-1-style surrogate (no floats, no logs).
# Model: scalar feature x, K classes, logits z_c = w_c·x.
#
# PIN (learning rate): η = 1/L with L = ‖X‖²_F, the Frobenius
# estimate of the linear block's smoothness (design matrix n×K,
# entry x_i per class column — the BlockSmooth C426 pattern).
# Descent is NOT tuned to fit: every step must pass the exact
# checkStep admission (drop > 0, drop ≤ obj − obj', budget' ≥ 0,
# risk' ≥ 0) computed in-line BEFORE the step is accepted; any
# failure aborts the trainer with a nonzero exit — the trainer only
# ever emits certified steps.
#
# PIN (holdout tie, C435): the risk field of each step is the
# holdout loss on ONE held-out point, i.e. holdoutMean on a k=1
# sample of the finite population; it is honest telemetry (may go
# UP — the C435 selection-bias lesson), the checker only requires
# risk' ≥ 0.
#
# PIN (trajectory length): exact rational GD on this surrogate has
# exploding denominators (degree-4 dynamics); the default is T=2
# steps, which already yields a nontrivial telescope and stays
# within norm_num's reach for the machine-checked witness.

CE_K = 3                                  # classes
CE_XTR = [F(1), F(2)]                     # train features
CE_YTR = [0, 1]                           # train labels
CE_XHO, CE_YHO = F(1), 2                  # holdout point
CE_W0 = [F(1), F(0), F(1)]                # initial weights


def ce_point_loss(w, x, y):
    """1 − p_true with p the rational-softmax over squared scores."""
    S = sum((w[c] * x) ** 2 for c in range(CE_K))
    return F(1) - (w[y] * x) ** 2 / S


def ce_train_loss(w):
    n = F(len(CE_XTR))
    return sum((ce_point_loss(w, x, y)
                for x, y in zip(CE_XTR, CE_YTR)), F(0)) / n


def ce_holdout_risk(w):
    return ce_point_loss(w, CE_XHO, CE_YHO)


def ce_grad(w):
    """Exact rational gradient of the train CE surrogate."""
    g = [F(0)] * CE_K
    n = F(len(CE_XTR))
    for x, y in zip(CE_XTR, CE_YTR):
        S = sum((w[c] * x) ** 2 for c in range(CE_K))
        a = (w[y] * x) ** 2
        for c in range(CE_K):
            dS = 2 * x * x * w[c]
            da = (2 * w[y] * x * x) if c == y else F(0)
            g[c] += (a * dS) / (S * S) - da / S
    return [t / n for t in g]


def ce_L():
    """Frobenius smoothness estimate ‖X‖²_F of the n×K design."""
    return sum((x * x for x in CE_XTR for _ in range(CE_K)), F(0))


def check_step(d):
    """In-line mirror of Hagi.Runtime.checkStep (exact admission)."""
    return (0 < d["drop"] and d["drop"] <= d["obj"] - d["obj'"]
            and 0 <= d["budget'"] and 0 <= d["risk'"])


def train_ce(steps):
    """Certified CE training: T GD steps with η = 1/L, each step
    admitted only if it passes the exact checkStep. Returns
    (start_obj, steps, [w-tuple per state], eta, L)."""
    L = ce_L()
    eta = F(1) / L
    w = list(CE_W0)
    states = [tuple(w)]
    traj = []
    for t in range(steps):
        obj, risk = ce_train_loss(w), ce_holdout_risk(w)
        budget = F(steps - t, steps)
        g = ce_grad(w)
        w = [w[c] - eta * g[c] for c in range(CE_K)]
        obj2, risk2 = ce_train_loss(w), ce_holdout_risk(w)
        budget2 = F(steps - t - 1, steps)
        d = {
            "obj": obj, "obj'": obj2,
            "drop": obj - obj2,
            "budget": budget, "budget'": budget2,
            "risk": risk, "risk'": risk2,
        }
        if not check_step(d):
            sys.exit(f"ABORT: step {t} failed certified admission: {d}")
        traj.append(d)
        states.append(tuple(w))
    return traj[0]["obj"], traj, states, eta, L


def rat(q):
    """Fraction -> exact Lean rational literal."""
    return f"({q.numerator}/{q.denominator} : ℚ)" if q.denominator != 1 \
        else f"({q.numerator} : ℚ)"


# NB: witness proof is `simp only + norm_num`, NOT `decide`: probe
# (.tmp/C434/probe*.lean) shows ℚ Decidable instances are not
# kernel-reducible in this toolchain (even a single tiny comparison),
# so decide fails structurally, not by size. norm_num yields a
# kernel-machine-checked term (allowed-axiom basis unchanged).

FIELDS = ["obj", "obj'", "drop", "budget", "budget'", "risk", "risk'"]


def lean_step(d):
    return "  ⟨" + ", ".join(rat(d[f]) for f in FIELDS) + "⟩"


def _proof(name_suffix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    head = (f"theorem bench_traj_{thm} :\n"
            f"    checkTrajectory benchStart{name_suffix} "
            f"benchTrajectory{name_suffix} = {val} := by\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStart{name_suffix}, benchTrajectory{name_suffix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    if ok:
        return head
    return (f"set_option linter.unusedSimpArgs false in\n" + head)


def emit_lean(path, start, traj, name_suffix="", ok=True):
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStart{name_suffix} : \u211a := {rat(start)}\n\n"
                f"def benchTrajectory{name_suffix} : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "]\n\n"
                f"#eval checkTrajectory benchStart{name_suffix} "
                f"benchTrajectory{name_suffix}\n\n"
                + _proof(name_suffix, ok))
    print(f"written: {path}", file=sys.stderr)


def emit_bad(path, start, traj):
    """Negative control: inflate the last drop beyond actual descent."""
    bad = [dict(d) for d in traj]
    last = bad[-1]
    last["drop"] = last["drop"] + F(1)  # drop > obj - obj' -> must fail
    emit_lean(path, start, bad, name_suffix="_bad", ok=False)


def _proof_ce(name_suffix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    proof_name = f"cert_ce_traj_{thm}"
    head = (f"theorem {proof_name} :\n"
            f"    checkTrajectory benchStart{name_suffix} "
            f"benchTrajectory{name_suffix} = {val} := by\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStart{name_suffix}, benchTrajectory{name_suffix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    if ok:
        return head
    return ("set_option linter.unusedSimpArgs false in\n" + head)


def emit_lean_ce(path, start, traj, name_suffix="", ok=True):
    """C442 witness for the certified CE trajectory (same literal /
    #eval / norm_num pattern as the default mode)."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStart{name_suffix} : \u211a := {rat(start)}\n\n"
                f"def benchTrajectory{name_suffix} : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "]\n\n"
                f"#eval checkTrajectory benchStart{name_suffix} "
                f"benchTrajectory{name_suffix}\n\n"
                + _proof_ce(name_suffix, ok))
    print(f"written: {path}", file=sys.stderr)


def emit_bad_ce(path, start, traj):
    """C442 negative control: inflate the last declared drop beyond
    the actual descent (the checker must reject the trajectory)."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    emit_lean_ce(path, start, bad, name_suffix="_bad", ok=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["quad", "cert-ce"],
                    default="quad",
                    help="quad: C434 quadratic GD (default); "
                         "cert-ce: C442 certified CE loop")
    ap.add_argument("--steps", type=int, default=None)
    ap.add_argument("--emit-lean", metavar="PATH")
    ap.add_argument("--corrupt", metavar="PATH")
    args = ap.parse_args()

    if args.mode == "cert-ce":
        steps = args.steps if args.steps is not None else 2
        start, traj, states, eta, L = train_ce(steps)
        print(json.dumps({
            "mode": "cert-ce",
            "L": str(L), "eta": str(eta),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "weights": ["[" + ", ".join(map(str, w)) + "]"
                        for w in states],
        }, indent=1))
        if args.emit_lean:
            emit_lean_ce(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_ce(args.corrupt, start, traj)
        return

    steps = args.steps if args.steps is not None else 5
    start, traj = train(steps)
    print(json.dumps({"start": str(start), "trajectory":
                      [{k: str(v) for k, v in d.items()} for d in traj]},
                     indent=1))

    if args.emit_lean:
        emit_lean(args.emit_lean, start, traj)
    if args.corrupt:
        emit_bad(args.corrupt, start, traj)


if __name__ == "__main__":
    main()

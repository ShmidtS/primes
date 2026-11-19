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
  --mode cert-tern   C443: certified ternary quantization jump — the
                     C442 CE loop extended with a train→quantize→
                     finetune cycle: gradient steps, then ONE ternary
                     jump w → s*·roundTern(w/s₀) with the LS-optimal
                     scale (lsScale formula, exact Fractions),
                     accepted only by the exact certified criterion
                     drop > 0 (rejected ⇒ HOLD: weights unchanged,
                     the hold step is EXCLUDED from the trajectory —
                     checkStep demands 0 < drop — and logged in the
                     `holds` telemetry), then certified finetune GD
                     steps on the quantized weights.
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


# ----------------------------------------------------------------
# C443: certified ternary quantization jump (--mode cert-tern)
#
# PIN (setup): the C442 CE machinery (data, surrogate, eta=1/L)
# is reused unchanged; the ternary mode starts from TERN_W0 =
# [2, 1, 2] (a free design choice fixed before the run, like
# CE_W0 in C442). Ddrops are exact measured differences — nothing
# is tuned to make a step pass; every accepted step is re-proved
# by the executable checker.
#
# PIN (quantizer): pattern q = roundTern(w / s0) with s0 =
# max|w| (in-range by construction), then the LS-OPTIMAL scale
# s* = (Σ q·w)/(Σ q·q) — the exact `lsScale_optimal` formula in
# Fractions (optimal for the FIXED pattern q in weight space;
# joint (q, s) optimality is NOT claimed). w' = s*·q.
#
# PIN (acceptance): the jump is admitted ONLY by the exact
# certified criterion drop = obj − obj' > 0 — the executable form
# of the corpus inequality k·s²/8 < E with E' ≤ k·s²/8
# (quantOpt_energy_bound / quant_jump_honest premise). A rejected
# jump is a HOLD: weights unchanged, the hold step is EXCLUDED
# from the emitted trajectory (checkStep demands 0 < drop — see
# Hagi/Theory/CertTernaryJump.lean `ternary_hold_rejected`) and
# logged in the `holds` telemetry array. Distortion energy
# Σ(w−w')² vs the corpus ceiling k·s*²/8 is reported as honest
# telemetry; it is NOT an admission input.

TERN_W0 = [F(2), F(1), F(2)]      # ternary-mode initial weights


def round_tern(fr):
    """Exact round-half-away-from-zero to {-1, 0, 1} domain input."""
    n, d = fr.numerator, fr.denominator
    if n >= 0:
        return F((2 * n + d) // (2 * d))
    return -F((2 * (-n) + d) // (2 * d))


def tern_quantize(w):
    """Ternary quantization with the LS-optimal scale (exact).

    Returns (w', s, q, s0): pattern q on the {-1,0,1} grid from the
    in-range scale s0 = max|w|, LS-optimal s = Σ q·w / Σ q·q
    (lsScale formula), quantized weights w' = s·q (exact multiples
    of s)."""
    s0 = max(abs(t) for t in w) or F(1)
    q = [round_tern(t / s0) for t in w]
    qq = sum((t * t for t in q), F(0))
    if qq == 0:                       # all-zero pattern: free zero jump
        return [F(0)] * CE_K, F(0), q, s0
    s = sum((q[i] * w[i] for i in range(CE_K)), F(0)) / qq
    return [s * t for t in q], s, q, s0


def train_tern(grad_steps, ft_steps):
    """Certified train → quantize → finetune cycle.

    Phase 1: `grad_steps` certified GD steps (C442 machinery).
    Phase 2: ONE ternary jump, admitted only by the exact criterion
    drop > 0; a rejected jump is a HOLD (excluded from the emitted
    trajectory, logged in `holds`).
    Phase 3: `ft_steps` certified GD steps on the quantized weights.
    Every emitted step passes the in-line checkStep mirror; any
    failure aborts (the trainer only ever emits certified steps).
    Returns (start_obj, [raw steps], holds, states, jump_info)."""
    w = list(TERN_W0)
    states = [tuple(w)]
    raw = []   # accepted steps: dicts with phase + readouts
    holds = [] # rejected jumps: honest telemetry, NOT steps
    jump = {}

    def record(phase, obj, obj2, risk, risk2, w2, **extra):
        raw.append({"phase": phase, "obj": obj, "obj'": obj2,
                    "drop": obj - obj2, "risk": risk,
                    "risk'": risk2, **extra})
        states.append(tuple(w2))

    for t in range(grad_steps):
        obj, risk = ce_train_loss(w), ce_holdout_risk(w)
        g = ce_grad(w)
        w2 = [w[c] - (F(1) / ce_L()) * g[c] for c in range(CE_K)]
        record("grad", obj, ce_train_loss(w2), risk,
               ce_holdout_risk(w2), w2)
        w = w2

    # ternary jump
    obj, risk = ce_train_loss(w), ce_holdout_risk(w)
    wq, s, q, s0 = tern_quantize(w)
    obj2, risk2 = ce_train_loss(wq), ce_holdout_risk(wq)
    drop = obj - obj2
    dist = sum(((w[i] - wq[i]) ** 2 for i in range(CE_K)), F(0))
    ceiling = F(CE_K) * s * s / 8
    jump = {"obj": obj, "obj'": obj2, "drop": drop, "s": s,
            "pattern": [int(t) for t in q], "s0": s0,
            "distortion": dist, "ceiling_k_s2_over_8": ceiling,
            "distortion_within_ceiling": bool(dist <= ceiling)}
    if drop > 0:
        jump["accepted"] = True
        record("jump", obj, obj2, risk, risk2, wq, s=s, pattern=q)
        w = wq
    else:
        jump["accepted"] = False
        holds.append({"phase": "jump", "obj": obj, "obj'": obj2,
                      "drop": drop, "s": s, "pattern": q,
                      "reason": "drop <= 0: HOLD, weights unchanged,"
                                " step excluded (checkStep needs 0<drop)"})

    for t in range(ft_steps):
        obj, risk = ce_train_loss(w), ce_holdout_risk(w)
        g = ce_grad(w)
        w2 = [w[c] - (F(1) / ce_L()) * g[c] for c in range(CE_K)]
        record("finetune", obj, ce_train_loss(w2), risk,
               ce_holdout_risk(w2), w2)
        w = w2

    # fill budget fields over the ACCEPTED steps only, then
    # re-verify every emitted step against the checker mirror
    n = F(len(raw))
    for t, d in enumerate(raw):
        d["budget"] = (F(len(raw) - t) / n) if n else F(0)
        d["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(d):
            sys.exit(f"ABORT: ternary step {t} ({d['phase']}) "
                     f"failed certified admission: {d}")
    return raw[0]["obj"], raw, holds, states, jump


def emit_lean_tern(path, start, traj, name_suffix="", ok=True,
                   thm_prefix="tern_traj"):
    """C443 witness for the certified ternary trajectory (same
    literal / #eval / norm_num pattern as C442/C434)."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStart{name_suffix} : \u211a := {rat(start)}\n\n"
                f"def benchTrajectory{name_suffix} : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "]\n\n"
                f"#eval checkTrajectory benchStart{name_suffix} "
                f"benchTrajectory{name_suffix}\n\n")
        thm = ("valid" if ok else "invalid")
        val = ("true" if ok else "false")
        f.write(f"theorem {thm_prefix}_{thm} :\n"
                f"    checkTrajectory benchStart{name_suffix} "
                f"benchTrajectory{name_suffix} = {val} := by\n"
                "  simp only [checkTrajectory, checkStep, "
                f"benchStart{name_suffix}, benchTrajectory{name_suffix}, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_tern(path, start, traj):
    """C443 negative (a): inflated declared drop — the checker must
    reject the trajectory."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    emit_lean_tern(path, start, bad, name_suffix="_bad", ok=False)


def emit_hold_tern(path, start, traj):
    """C443 negative (b): a HOLD (rejected-jump) step CANNOT ride the
    trajectory — the checker rejects the identity record with
    drop = 0 (machine-checked reason holds are excluded from the
    List; see Hagi/Theory/CertTernaryJump.lean ternary_hold_rejected)."""
    last = traj[-1]
    hold = {"obj": last["obj'"], "obj'": last["obj'"], "drop": F(0),
            "budget": last["budget'"], "budget'": last["budget'"],
            "risk": last["risk'"], "risk'": last["risk'"]}
    emit_lean_tern(path, start, traj + [hold],
                   name_suffix="_hold", ok=False,
                   thm_prefix="tern_hold_traj")


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


# ----------------------------------------------------------------
# C444: certified block admission for LM growth (--mode grow)
#
# PIN (model): a linear model on rational data (MSE, exact
# Fractions): base model y ~ w*x (one feature). A growth
# candidate = adding a FEATURE (fiber dimension extension: the
# Python face of the Lean OrthoInjection candidate
# mkOrthoFiberBlock in Hagi/Theory/BlockAdmission.lean): the new
# column acts only in the fresh direction; u = 0 at admission
# keeps the base objective exact (cortex coordinates unchanged).
#
# PIN (admission criterion == Lean blockGainOk, ONE inequality):
# lamM*dCost + lamR*dRisk + eps_cert <= gain, all exact Fractions:
#   gain  = measured certified drop of ONE exact GD step on the
#           EXTENDED model from u = 0 (inline check_step before
#           the step may be emitted; abort otherwise);
#   dCost = measured cost increment of the candidate column
#           (feature-dimension units: one weight + one KV column
#           — the Python face of kvCostOfBlock / lmKVCost_grow);
#   dRisk = holdout risk increment (ONE held-out point, C435
#           honesty: telemetry, may rise);
#   eps_cert = explicit safety slack.
# A REJECTED candidate is a HOLD: model unchanged, the candidate
# is logged in `admissions` telemetry (NOT a CertStepData — a
# zero-gain candidate has drop = 0 and checkStep demands 0 < drop,
# exactly the Lean costly_zero_gain_block_refused /
# noBlockAdmissionWithoutMargin negatives).
#
# PIN (reject candidate, honest zero gain): the second candidate is
# a synthetic noise feature g constructed orthogonal to the CURRENT
# residual vector (g = (r2, -r1, 0) on r = (r1, r2, r3)): its exact
# gradient is identically zero, so the measured certified gain is
# exactly 0 while dCost > 0 — the MemoryCycle 'novelty without
# gain' shape; nothing is tuned to fake a rejection: the gradient
# is computed exactly.

GROW_LAMM = F(1, 4)     # cost exchange weight (explicit parameter)
GROW_LAMR = F(1, 4)     # risk exchange weight (explicit parameter)
GROW_EPS = F(1, 100)    # admission safety slack
XHO_GROW, YHO_GROW = F(4), F(9)   # holdout point (not in train)


def grow_loss(w, feats):
    """MSE of the linear model on the feature columns `feats`
    (each column: 3 train values + 1 holdout value in position 3)."""
    n = F(len(XS))
    return sum(((sum((wi * f[i] for wi, f in zip(w, feats)), F(0))
                 - YS[i]) ** 2 for i in range(len(XS))), F(0)) / n


def grow_grad(w, feats):
    """Exact rational gradient of grow_loss (train part)."""
    n = F(len(XS))
    g = [F(0)] * len(w)
    for i in range(len(XS)):
        r = sum((wi * f[i] for wi, f in zip(w, feats)), F(0)) - YS[i]
        for j, f in enumerate(feats):
            g[j] += F(2) * r * f[i]
    return [t / n for t in g]


def grow_smooth(feats):
    """Frobenius smoothness estimate ||X||^2_F (BlockSmooth/C442
    pattern): sum of squared train feature entries — sets eta = 1/L."""
    return sum((f[i] ** 2 for f in feats
                for i in range(len(XS))), F(0))


def grow_holdout_risk(w, feats):
    """Holdout risk: squared error on the held-out point
    (column position 3 — the holdout value of each feature)."""
    pred = sum((wi * f[3] for wi, f in zip(w, feats)), F(0))
    return (pred - YHO_GROW) ** 2


def admission_margin(gain, dcost, drisk):
    """lamM*dCost + lamR*dRisk + eps - gain (positive => REJECT:
    the Lean criterion blockGainOk needs the excess <= 0)."""
    return (GROW_LAMM * dcost + GROW_LAMR * drisk + GROW_EPS
            - gain)


def grow_run(base_steps=1, grown_steps=1):
    """Certified growth cycle: base certified steps, ONE growth
    candidate (feature x^2) decided by the exact admission
    criterion, certified steps on the grown model, then a costly
    zero-gain candidate REJECTED (HOLD). Every emitted step passes
    the inline check_step mirror; any failure aborts."""
    feats0 = [list(XS) + [XHO_GROW]]   # base column + holdout value
    w = [F(0)]
    raw = []
    admissions = []
    hist = [tuple(w)]

    x2 = [x * x for x in XS] + [XHO_GROW * XHO_GROW]  # feature x^2

    def do_step(phase, feats, wcur, extra=None, only_last=False):
        L = grow_smooth([feats[-1]]) if only_last \
            else grow_smooth(feats)
        eta = F(1) / L
        obj = grow_loss(wcur, feats)
        risk = grow_holdout_risk(wcur, feats)
        g = grow_grad(wcur, feats)
        if only_last:
            # candidate step: the base is FROZEN, only the new
            # block's weight moves (lm_head_safeStep_lt shape:
            # trunk fixed, head updated)
            w2 = list(wcur)
            w2[-1] = wcur[-1] - eta * g[-1]
        else:
            w2 = [wcur[j] - eta * g[j] for j in range(len(wcur))]
        obj2 = grow_loss(w2, feats)
        risk2 = grow_holdout_risk(w2, feats)
        d = {"phase": phase, "obj": obj, "obj'": obj2,
             "drop": obj - obj2, "risk": risk, "risk'": risk2}
        if extra:
            d.update(extra)
        return d, w2

    # phase 1: base certified steps
    for t in range(base_steps):
        d, w2 = do_step("base", feats0, w)
        raw.append(d)
        w = w2
        hist.append(tuple(w))

    # growth candidate 1: feature x^2 (informative)
    featsG = [feats0[0], x2]
    dcost = F(2)                       # one weight + one KV column
    d, w2 = do_step("grow-candidate", featsG, [w[0], F(0)],
                    extra={"candidate": "x^2"}, only_last=True)
    gain, drisk = d["drop"], d["risk'"] - d["risk"]
    margin = admission_margin(gain, dcost, drisk)
    admissions.append({"candidate": "x^2", "gain": gain,
                       "dCost": dcost, "dRisk": drisk,
                       "margin_excess": margin,
                       "admitted": bool(margin <= 0)})
    if margin <= 0:
        if not (0 < d["drop"] and d["drop"] <= d["obj"]
                - d["obj'"] and 0 <= d["risk'"]):
            sys.exit(f"ABORT: grow step failed certified "
                     f"admission: {d}")
        raw.append(d)
        w = w2
        hist.append(tuple(w))
        # phase 3: certified steps on the GROWN model
        for t in range(grown_steps):
            d, w2 = do_step("grown", featsG, w)
            raw.append(d)
            w = w2
            hist.append(tuple(w))
    else:
        admissions[-1]["reason"] = (
            "margin > 0: HOLD, model unchanged (Hagi.Theory."
            "BlockAdmission noBlockAdmissionWithoutMargin)")

    # growth candidate 2: noise feature orthogonal to the current
    # residual (exact zero gradient => zero certified gain)
    r = [YS[i] - sum((wi * f[i] for wi, f in zip(w, featsG)), F(0))
         for i in range(len(XS))]
    gcol = [r[1], -r[0], F(0), F(0)]   # orthogonal to r, holdout 0
    featsN = [feats0[0], x2, gcol]
    dcost2 = F(2)
    d2, _ = do_step("grow-candidate", featsN, list(w) + [F(0)],
                    extra={"candidate": "noise"}, only_last=True)
    gain2, drisk2 = d2["drop"], d2["risk'"] - d2["risk"]
    margin2 = admission_margin(gain2, dcost2, drisk2)
    admissions.append({"candidate": "noise", "gain": gain2,
                       "dCost": dcost2, "dRisk": drisk2,
                       "margin_excess": margin2,
                       "admitted": bool(margin2 <= 0),
                       "reason": "zero gradient (orthogonal to "
                                 "residual): measured gain = 0, "
                                 "cost > 0 => REJECT "
                                 "(costly_zero_gain_block_refused)"})
    # REJECT: nothing emitted, model unchanged (refuse_safe shape)

    # fill budget fields over the ACCEPTED steps, re-verify each
    n = F(len(raw))
    for t, dd in enumerate(raw):
        dd["budget"] = (F(len(raw) - t) / n) if n else F(0)
        dd["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(dd):
            sys.exit(f"ABORT: grow step {t} ({dd['phase']}) "
                     f"failed certified admission: {dd}")
    return raw[0]["obj"], raw, admissions, hist


def _proof_grow(prefix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    return (f"theorem grow_traj_{thm}{prefix} :\n"
            f"    checkTrajectory benchStartGrow{prefix} "
            f"benchTrajectoryGrow{prefix} = {val} := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStartGrow{prefix}, benchTrajectoryGrow{prefix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")


def emit_lean_grow(path, start, traj, reject=None):
    """C444 witness: literal trajectory + #eval + norm_num theorem,
    plus (if `reject` given) the machine-checked ADMISSION REFUSAL
    of the costly zero-gain candidate: the criterion inequality is
    FALSE on the exact measured literals."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartGrow : ℚ := {rat(start)}\n\n"
                "def benchTrajectoryGrow : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrow "
                "benchTrajectoryGrow\n\n")
        f.write(_proof_grow("", True))
        if reject is not None:
            f.write(
                "\n/-- Machine-checked refusal of the costly "
                "zero-gain candidate (C444 negative (c)): the "
                "admission criterion\nlamM·Δcost + lamR·Δrisk + "
                "ε_cert ≤ gain is FALSE on the exact measured "
                "literals, so\nblockAdmissionRule refuses "
                "(Hagi.Theory.BlockAdmission."
                "noBlockAdmissionWithoutMargin). -/\n"
                "theorem grow_reject_margin :\n"
                "    ¬ ((1/4 : ℚ) * "
                f"{rat(reject['dCost'])} + (1/4 : ℚ) * "
                f"{rat(reject['dRisk'])} + {rat(GROW_EPS)}"
                f"\n        ≤ {rat(reject['gain'])}) := by\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# ----------------------------------------------------------------
# C446: anytime holdout admission-stop (--mode grow-stop)
#
# PIN (gap C445): the C444 grow loop admits blocks on the train-
# side margin alone; holdout telemetry may DEGRADE with no stop --
# growth continues while generalization collapses. This mode adds
# the Ville anytime stop (Hagi/Theory/AnytimeHoldoutStop):
#
#   e-process  L_t = exp(lam * D_t),  D_t = holdout_t - holdout_0
#   (accumulated holdout degradation), supermartingale under the
#   ZERO-degradation contract (martingale holdout increments --
#   C435 holdout_unbiased premise, model fixed before the draw);
#   Ville: P[sup_t L_t >= 1/delta] <= delta  -- an ANYTIME detector:
#   the stop may fire at any adaptively chosen step.
#
# RATIONAL detector (no exp, exact Fractions): since
#   log(1/delta) <= 1/delta - 1   (log x <= x - 1)
# the threshold tau' = 1/delta - 1 is CONSERVATIVE: firing
# lam * D_t >= 1/delta - 1 implies the e-value crossed 1/delta
# (Lean: stop_implies_evalue), so the false-stop probability is
# bounded by delta (Lean: grow_stop_sound / false_stop_bound).
# The detector fires LATER than the exact e-value stop -- we pay
# sensitivity, never validity.
#
# PIN (honest overfitting scenario): normalized polynomial blocks
# (x/3)^d, d = 2..11; train points x in {1,2,3}, holdout x = 4.
# Each block's certified candidate step has positive measured
# gain (blockGainOk passes: lamM = lamR = eps = 0 pass-through
# growth gate -- the honest C445 gap: the admission gate alone does
# NOT stop overfitting), but the holdout value (4/3)^d makes the
# accumulated degradation D_t explode -- the anytime stop fires and
# every later block is REFUSED with reason STOP (admitWithStop /
# stop_blocks_admission).

GS_LAM = F(8)        # detector weight lambda (exact Fraction)
GS_DELTA = F(1, 4)   # anytime false-stop budget delta
GS_THRESH = F(1) / GS_DELTA - F(1)  # conservative rational threshold
GS_DMAX = 11         # candidate blocks (x/3)^d, d = 2..GS_DMAX


def gs_stop_fires(d_cum):
    """The executable rational stop rule (Lean holdoutStopRule):
    stopThreshold delta <= lam * D. Conservative subset of the
    e-value crossing {exp(lam*D) >= 1/delta} (Ville)."""
    return GS_THRESH <= GS_LAM * d_cum


def grow_stop_run(base_steps=2, grown_steps=4):
    """Certified growth with the anytime holdout stop: base steps,
    then normalized polynomial blocks decided by the C444 margin
    (pass-through parameters here -- the honest gap) AND the C446
    Ville stop. Once the stop fires, later blocks are logged as
    refused (reason STOP) and NOTHING is emitted for them."""
    feats = [list(XS) + [XHO_GROW]]
    w = [F(0)]
    raw = []
    admissions = []

    def do_step(phase, feats, wcur, extra=None, only_last=False):
        L = grow_smooth([feats[-1]]) if only_last \
            else grow_smooth(feats)
        eta = F(1) / L
        obj = grow_loss(wcur, feats)
        risk = grow_holdout_risk(wcur, feats)
        g = grow_grad(wcur, feats)
        if only_last:
            w2 = list(wcur)
            w2[-1] = wcur[-1] - eta * g[-1]
        else:
            w2 = [wcur[j] - eta * g[j] for j in range(len(wcur))]
        obj2 = grow_loss(w2, feats)
        risk2 = grow_holdout_risk(w2, feats)
        d = {"phase": phase, "obj": obj, "obj'": obj2,
             "drop": obj - obj2, "risk": risk, "risk'": risk2}
        if extra:
            d.update(extra)
        return d, w2

    for t in range(base_steps):
        d, w2 = do_step("base", feats, w)
        raw.append(d)
        w = w2

    h0 = grow_holdout_risk(w, feats)
    stopped = False
    stop_rec = None
    for dd in range(2, GS_DMAX + 1):
        c = [x ** dd / F(3) ** dd for x in XS] \
            + [(XHO_GROW / F(3)) ** dd]
        feats2 = feats + [c]
        d, w2 = do_step("grow-candidate", feats2, list(w) + [F(0)],
                        extra={"candidate": f"(x/3)^{dd}"},
                        only_last=True)
        gain = d["drop"]
        # C444 margin with pass-through parameters: the gate itself
        # would admit (positive certified gain) -- honest C445 gap
        rec = {"candidate": f"(x/3)^{dd}", "gain": gain,
               "holdout": grow_holdout_risk(w2, feats2),
               "D": grow_holdout_risk(w2, feats2) - h0,
               "admitted": False, "reason": ""}
        if stopped:
            rec["reason"] = ("STOP already fired: admitWithStop "
                             "blocks every later block "
                             "(stop_blocks_admission)")
            admissions.append(rec)
            continue
        if not (0 < d["drop"] and d["drop"] <= d["obj"] - d["obj'"]
                and 0 <= d["risk'"]):
            sys.exit(f"ABORT: grow-stop candidate step failed "
                     f"certified check: {d}")
        raw.append(d)
        w, feats = w2, feats2
        # grown certified steps on the extended model
        for t in range(grown_steps):
            d, w2 = do_step("grown", feats, w)
            raw.append(d)
            w = w2
        h = grow_holdout_risk(w, feats)
        d_cum = h - h0
        rec["admitted"] = True
        rec["holdout"] = h
        rec["D"] = d_cum
        rec["lamD"] = GS_LAM * d_cum
        rec["margin_excess"] = -gain
        if gs_stop_fires(d_cum):
            stopped = True
            rec["stopped"] = True
            rec["reason"] = ("STOP: lam*D >= 1/delta - 1 => e-value "
                             ">= 1/delta (stop_implies_evalue); "
                             "false-stop prob <= delta (Ville, "
                             "grow_stop_sound)")
            stop_rec = dict(rec)
        else:
            rec["stopped"] = False
        admissions.append(rec)

    if not stopped:
        sys.exit("ABORT: honest overfitting scenario did not fire "
                 "the anytime stop -- tune GS_LAM/GS_DELTA")

    n = F(len(raw))
    for t, dd in enumerate(raw):
        dd["budget"] = (F(len(raw) - t) / n) if n else F(0)
        dd["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(dd):
            sys.exit(f"ABORT: grow-stop step {t} ({dd['phase']}) "
                     f"failed certified admission: {dd}")
    return raw[0]["obj"], raw, admissions, h0, stop_rec


def _proof_grow_stop(prefix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    return (f"theorem growstop_traj_{thm}{prefix} :\n"
            f"    checkTrajectory benchStartGrowStop{prefix} "
            f"benchTrajectoryGrowStop{prefix} = {val} := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStartGrowStop{prefix}, "
            f"benchTrajectoryGrowStop{prefix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")


def emit_lean_grow_stop(path, start, traj, stop_rec, blocked):
    """C446 witness: literal trajectory + #eval + norm_num theorem,
    the machine-checked STOP (the rational rule fired on the exact
    literals) and the negative: the FIRST blocked candidate had a
    POSITIVE measured gain -- without the stop the cycle would have
    continued (no_stop_admits)."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartGrowStop : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryGrowStop : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrowStop "
                "benchTrajectoryGrowStop\n\n")
        f.write(_proof_grow_stop("", True))
        f.write(
            "\n/-- Machine-checked STOP (C446): the conservative "
            "rational rule fired --\n1/delta - 1 <= lam * D on the "
            "exact measured literals, hence the e-value\ncrossed "
            "1/delta (stop_implies_evalue) and admission is "
            "blocked for every later\nblock "
            "(Hagi.Theory.AnytimeHoldoutStop). -/\n"
            "theorem growstop_fired :\n"
            f"    {rat(GS_THRESH)} <= {rat(GS_LAM)} * "
            f"{rat(stop_rec['D'])} := by\n"
            "  norm_num\n")
        f.write(
            "\n/-- Negative (cycle would continue without the "
            "stop): the FIRST blocked\ncandidate has POSITIVE "
            "measured certified gain -- the C444 margin alone would\n"
            "admit it (no_stop_admits). The stop is the ONLY "
            "reason growth halted. -/\n"
            "theorem growstop_blocked_would_admit :\n"
            f"    0 < {rat(blocked['gain'])} := by\n"
            "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_grow_stop(path, start, traj):
    """C446 negative control: inflated declared drop -- the checker
    must reject the trajectory."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartGrowStopBad : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryGrowStopBad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in bad)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrowStopBad "
                "benchTrajectoryGrowStopBad\n\n")
        f.write(_proof_grow_stop("Bad", False))
    print(f"written: {path}", file=sys.stderr)


def emit_bad_grow(path, start, traj):
    """C444 negative: inflated declared drop — the checker must
    reject the trajectory."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartGrowBad : ℚ := {rat(start)}\n\n"
                "def benchTrajectoryGrowBad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in bad)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrowBad "
                "benchTrajectoryGrowBad\n\n")
        f.write(_proof_grow("Bad", False))
    print(f"written: {path}", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode",
                    choices=["quad", "cert-ce", "cert-tern",
                             "grow", "grow-stop"],
                    default="quad",
                    help="quad: C434 quadratic GD (default); "
                         "cert-ce: C442 certified CE loop; "
                         "cert-tern: C443 certified ternary "
                         "quantization jump cycle; "
                         "grow: C444 certified block "
                         "admission for LM growth")
    ap.add_argument("--grad-steps", type=int, default=None,
                    help="cert-tern: gradient phase steps "
                         "(default 1; grow-stop: base steps, default 2)")
    ap.add_argument("--ft-steps", type=int, default=None,
                    help="cert-tern: finetune phase steps "
                         "(default 1; grow-stop: grown steps, default 1)")
    ap.add_argument("--steps", type=int, default=None)
    ap.add_argument("--emit-lean", metavar="PATH")
    ap.add_argument("--corrupt", metavar="PATH")
    ap.add_argument("--hold-demo", metavar="PATH",
                    help="cert-tern: emit the HOLD negative witness "
                         "(a drop=0 identity step the checker "
                         "must reject)")
    args = ap.parse_args()

    if args.mode == "grow-stop":
        gs_base = args.grad_steps if args.grad_steps is not None \
            else 2
        gs_grown = args.ft_steps if args.ft_steps is not None \
            else 1
        start, traj, admissions, h0, stop_rec = grow_stop_run(
            gs_base, gs_grown)
        blocked = next((a for a in admissions
                        if stop_rec is not None and not a["admitted"]),
                       None)
        print(json.dumps({
            "mode": "grow-stop",
            "lam": str(GS_LAM), "delta": str(GS_DELTA),
            "threshold": str(GS_THRESH),
            "holdout_0": str(h0),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "stop": {k: str(v) for k, v in stop_rec.items()},
            "admissions": [{k: (str(v) if not isinstance(v, bool)
                                else v) for k, v in a.items()}
                           for a in admissions],
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
        }, indent=1))
        if args.emit_lean:
            emit_lean_grow_stop(args.emit_lean, start, traj,
                                stop_rec, blocked)
        if args.corrupt:
            emit_bad_grow_stop(args.corrupt, start, traj)
        return

    if args.mode == "grow":
        start, traj, admissions, hist = grow_run(
            args.grad_steps if args.grad_steps is not None else 1,
            args.ft_steps if args.ft_steps is not None else 1)
        rej = next((a for a in admissions if not a["admitted"]),
                   None)
        print(json.dumps({
            "mode": "grow",
            "lamM": str(GROW_LAMM), "lamR": str(GROW_LAMR),
            "eps_cert": str(GROW_EPS),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "admissions": [{k: (str(v) if not isinstance(v, bool)
                                else v) for k, v in a.items()}
                           for a in admissions],
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "weights": ["[" + ", ".join(map(str, w)) + "]"
                        for w in hist],
        }, indent=1))
        if args.emit_lean:
            emit_lean_grow(args.emit_lean, start, traj,
                           reject=rej)
        if args.corrupt:
            emit_bad_grow(args.corrupt, start, traj)
        return

    if args.mode == "cert-tern":
        start, traj, holds, states, jump = train_tern(
            args.grad_steps if args.grad_steps is not None else 1,
            args.ft_steps if args.ft_steps is not None else 1)
        print(json.dumps({
            "mode": "cert-tern",
            "eta": str(F(1) / ce_L()), "L": str(ce_L()),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "jump": {k: (str(v) if not isinstance(v, (bool, list))
                         else v) for k, v in jump.items()},
            "holds": [{k: (str(v) if not isinstance(v, (bool, list))
                           else v) for k, v in h.items()} for h in holds],
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "weights": ["[" + ", ".join(map(str, w)) + "]"
                        for w in states],
        }, indent=1))
        if args.emit_lean:
            emit_lean_tern(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_tern(args.corrupt, start, traj)
        if args.hold_demo:
            emit_hold_tern(args.hold_demo, start, traj)
        return

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

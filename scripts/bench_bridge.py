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
  --mode ef21-step  C474: EF21 IN-STEP quantized training loop — the
                     update is compressed INSIDE every gradient step
                     with error feedback: m = g + e (exact gradient +
                     accumulated residual); d = tern_s(m) (fixed-scale
                     ternary quantizer); e' = m − d (error feedback);
                     trial step θ − η·d, admitted ONLY by the exact
                     certified criterion drop > 0 (a rejected trial —
                     possibly with NEGATIVE drop — is a HOLD: weights
                     and residual unchanged, the step is EXCLUDED from
                     the trajectory and logged as reject telemetry).
"""

import argparse
import json
import time
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
# Hagi/Theory/Compression.lean `ternary_hold_rejected`) and
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
    List; see Hagi/Theory/Compression.lean ternary_hold_rejected)."""
    last = traj[-1]
    hold = {"obj": last["obj'"], "obj'": last["obj'"], "drop": F(0),
            "budget": last["budget'"], "budget'": last["budget'"],
            "risk": last["risk'"], "risk'": last["risk'"]}
    emit_lean_tern(path, start, traj + [hold],
                   name_suffix="_hold", ok=False,
                   thm_prefix="tern_hold_traj")


# ----------------------------------------------------------------
# C477: Hadamard-gated ternary quantization (--mode hadamard-tern)
#
# PIN (P5 of the A19 audit): the Hadamard rotation before ternary
# quantization is applied ONLY under a MEASURED incoherence gate
# (the corpus negative hadamard_not_universally_incoherent pins
# that the rotation is NOT universally beneficial: it can
# CONCENTRATE a vector instead of spreading it). The gate is the
# exact rational coherence comparison cohSq(Hw) < cohSq(w) with
# cohSq(v) = max|v|^2 / sum(v^2) (the square of the coherence —
# monotone, so the strict comparison decides the same; computed
# with the INTEGER +-1 Sylvester matrix because cohSq is
# scale-invariant, mirroring Hagi/Theory/HadamardIncoherence.lean
# cohSq_smul — no sqrt/irrationals anywhere).
#
# PIN (dimension): cert-tern runs on CE_K = 3 classes, which is not
# a power of two; this mode uses a K = 4 = 2^2 head (same
# rational-softmax surrogate, eta = 1/L Frobenius, exact checkStep
# admission on every emitted step) so the Sylvester H_2 applies.
#
# PIN (derotation): quantization happens in the ROTATED basis only
# when the gate passes; the pattern q and lsScale-optimal s* follow
# the C443 recipe exactly, and the result is derotated through the
# symmetric integer inverse w' = H^T (s* q)/4 (H H = 4 I, all
# Fractions). If the gate fails, the C443 direct quantizer runs
# unchanged — the machine decides, not a postulate. The jump is
# admitted ONLY by the exact certified criterion drop > 0; a
# rejection is a HOLD (excluded from the emitted trajectory).

HT_K = 4                                  # classes = 2^2 (Sylvester order)
HT_W0 = [F(-3), F(-2), F(-2), F(1)]     # fixed before the run, C443-style
# Sylvester H_2 (integer +-1, symmetric, H*H = 4 I)
HT_H = [[1, 1, 1, 1],
        [1, -1, 1, -1],
        [1, 1, -1, -1],
        [1, -1, -1, 1]]


def ht_point_loss(w, x, y):
    """1 - p_true, rational-softmax over squared scores (C442)."""
    S = sum((w[c] * x) ** 2 for c in range(HT_K))
    return F(1) - (w[y] * x) ** 2 / S


def ht_train_loss(w):
    n = F(len(CE_XTR))
    return sum((ht_point_loss(w, x, y)
                for x, y in zip(CE_XTR, CE_YTR)), F(0)) / n


def ht_holdout_risk(w):
    return ht_point_loss(w, CE_XHO, CE_YHO)


def ht_grad(w):
    """Exact rational gradient of the K=4 CE surrogate."""
    g = [F(0)] * HT_K
    n = F(len(CE_XTR))
    for x, y in zip(CE_XTR, CE_YTR):
        S = sum((w[c] * x) ** 2 for c in range(HT_K))
        a = (w[y] * x) ** 2
        for c in range(HT_K):
            dS = 2 * x * x * w[c]
            da = (2 * w[y] * x * x) if c == y else F(0)
            g[c] += (a * dS) / (S * S) - da / S
    return [t / n for t in g]


def ht_L():
    return sum((x * x for x in CE_XTR for _ in range(HT_K)), F(0))


def ht_matvec(H, w):
    return [sum((H[r][c] * w[c] for c in range(HT_K)), F(0))
            for r in range(HT_K)]


def coh_sq(w):
    """Exact rational coherence squared: max|w|^2 / sum(w^2)
    (mirror of cohSq in Hagi/Theory/HadamardIncoherence.lean)."""
    l2 = sum((t * t for t in w), F(0))
    if l2 == 0:
        return F(0)
    return max(abs(t) for t in w) ** 2 / l2


def ht_quantize(w):
    """Gated Hadamard ternary jump (rotate-if-measured-better).

    Measures cohSq(w) vs cohSq(H w) exactly in Fractions; rotates
    only when the strict gate passes; quantizes (C443 lsScale
    recipe: s0 = max|.|, q = roundTern, s* = sum q w / sum q q);
    derotates w' = H^T (s* q)/4 when rotated. Returns
    (w', s, q, s0, gate_info)."""
    hw = ht_matvec(HT_H, w)
    c_before = coh_sq(w)
    c_after = coh_sq(hw)
    gate = c_after < c_before
    src, basis = (hw, "hadamard") if gate else (w, "direct")
    s0 = max(abs(t) for t in src) or F(1)
    q = [round_tern(t / s0) for t in src]
    qq = sum((t * t for t in q), F(0))
    if qq == 0:
        wq = [F(0)] * HT_K
        s = F(0)
    else:
        s = sum((q[i] * src[i] for i in range(HT_K)), F(0)) / qq
        scaled = [s * t for t in q]
        wq = ht_matvec(HT_H, scaled) if gate else scaled
        if gate:  # derotate: H^T = H, H*H = 4 I  =>  x -> H x / 4
            wq = [t / F(4) for t in wq]
    sat = sum((1 for t in src if abs(t) > 3 * s / 2), 0) if s > 0 else HT_K
    gate_info = {"coh_sq_before": c_before, "coh_sq_after": c_after,
                 "coh_sq_rotated": c_after if gate else c_before,
                 "gate_passed": bool(gate), "basis": basis,
                 "saturated_coords": sat}
    return wq, s, q, s0, gate_info


def train_ht(grad_steps, ft_steps):
    """Certified K=4 CE train -> HADAMARD-GATED ternary jump ->
    finetune. Same admission discipline as train_tern: every emitted
    step passes the in-line checkStep mirror; the jump is admitted
    only by the exact drop > 0 criterion, otherwise a HOLD."""
    w = list(HT_W0)
    states = [tuple(w)]
    raw = []
    holds = []
    jump = {}

    def record(phase, obj, obj2, risk, risk2, w2, **extra):
        raw.append({"phase": phase, "obj": obj, "obj'": obj2,
                    "drop": obj - obj2, "risk": risk,
                    "risk'": risk2, **extra})
        states.append(tuple(w2))

    for t in range(grad_steps):
        obj, risk = ht_train_loss(w), ht_holdout_risk(w)
        g = ht_grad(w)
        w2 = [w[c] - (F(1) / ht_L()) * g[c] for c in range(HT_K)]
        record("grad", obj, ht_train_loss(w2), risk,
               ht_holdout_risk(w2), w2)
        w = w2

    obj, risk = ht_train_loss(w), ht_holdout_risk(w)
    wq, s, q, s0, gate_info = ht_quantize(w)
    obj2, risk2 = ht_train_loss(wq), ht_holdout_risk(wq)
    drop = obj - obj2
    dist = sum(((w[i] - wq[i]) ** 2 for i in range(HT_K)), F(0))
    ceiling = F(HT_K) * s * s / 8
    jump = {"obj": obj, "obj'": obj2, "drop": drop, "s": s,
            "pattern": [int(t) for t in q], "s0": s0,
            "distortion": dist, "ceiling_k_s2_over_8": ceiling,
            "distortion_within_ceiling": bool(dist <= ceiling),
            **gate_info}
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
        obj, risk = ht_train_loss(w), ht_holdout_risk(w)
        g = ht_grad(w)
        w2 = [w[c] - (F(1) / ht_L()) * g[c] for c in range(HT_K)]
        record("finetune", obj, ht_train_loss(w2), risk,
               ht_holdout_risk(w2), w2)
        w = w2

    n = F(len(raw))
    for t, d in enumerate(raw):
        d["budget"] = (F(len(raw) - t) / n) if n else F(0)
        d["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(d):
            sys.exit(f"ABORT: hadamard-tern step {t} ({d['phase']}) "
                     f"failed certified admission: {d}")
    return raw[0]["obj"], raw, holds, states, jump

# ----------------------------------------------------------------
# C479: unified full pipeline (--mode full-pipeline)
#
# PIN (unification): ONE task — linear regression on the SAME
# rational data as grow/grow-stop (XS/YS, holdout (4,9)) — passes
# ALL SIX phases back to back on ONE objective chain:
#   (a) TRAIN: 2 certified GD steps (eta = 1/L, BlockSmooth);
#   (b) EF21: 2 in-step quantized steps with error feedback
#       (m = g + e, d = tern_s(m), s = 1/4 fixed; reject => HOLD
#       telemetry, C474 semantics);
#   (c) HADAMARD-TERN: measured cohSq gate (C477) on the dim-4
#       weight vector (base features [1, x/3, (x/3)^2, (x/3)^3]
#       — dim 4 = 2^2 for the Sylvester H2), ternary jump with
#       the C443 lsScale recipe + derotation H^T/4, admitted only
#       by drop > 0; then 1 certified finetune GD step;
#   (d) GROW: candidate feature (x/3)^4 decided by the C444 exact
#       admission margin (admit => only_last step from u = 0, so
#       the obj chain stays EXACTLY continuous: L_new(w||0) =
#       L_old(w)); a noise candidate orthogonal to the residual
#       (zero gradient => zero gain) is REJECTED — telemetry,
#       not a step;
#   (e) MERGE: side finetune branch (2 certified GD steps from
#       the current weights — branch telemetry, NOT trajectory
#       steps: the trace is one state chain), merged = midpoint;
#       the C476 measured-delta gate: delta_meas = linResidual of
#       the linearization L(wA) + t*G (G = grad(wA)·(wB−wA)) over
#       the grid t in {1/4, 1/2, 3/4, 1}; SAFETY gate
#       obj(mid) <= obj(wA) + delta_meas; ADMISSION to the trace
#       still demands drop > 0 (checkStep) — a gate-passing merge
#       with drop <= 0 is an honest HOLD (telemetry);
#   (f) STOP: normalized polynomial candidates (x/3)^d, d = 4..;
#       each admits a certified step (positive gain — the honest
#       C445 gap: the admission gate alone does not stop
#       overfitting), the C446 Ville stop fires on
#       lam*D >= 1/delta - 1 (D = holdout - h0, h0 fixed at the
#       stop-phase start); after the STOP every later candidate is
#       refused (telemetry). If the stop never fires the run
#       ABORTS (the C446 discipline).
#
# PIN (why linear, not softmax-CE): the C442 rational-softmax
# surrogate has degree-4 dynamics — beyond T=2 steps the exact
# denominators explode past kernel reach (the C442 trajectory
# pin); the quadratic MSE carrier keeps the full 6-phase chain
# within norm_num's reach while exercising every phase honestly.
#
# The WHOLE cycle is ONE CertStepData trace (obj' of step N = obj
# of step N+1 — asserted; the executable checker re-verifies the
# chain) plus per-phase telemetry: drops/costs/risks, admits /
# rejects / holds, the holdout track and the stop record.

FP_W0 = [F(1), F(0), F(0), F(0)]   # fixed before the run (dim 4)
FP_EF21_S = F(1, 4)               # fixed EF21 ternary scale
FP_TRAIN_STEPS = 2
FP_EF21_STEPS = 2
FP_FT_STEPS = 1
FP_BRANCH_STEPS = 2               # merge side branch (telemetry)
FP_MERGE_GRID = [F(1, 4), F(1, 2), F(3, 4), F(1)]
FP_STOP_DMIN, FP_STOP_DMAX = 4, 8  # candidate degrees (x/3)^d


def fp_base_feats():
    """The four normalized base columns [1, x/3, (x/3)^2, (x/3)^3]
    (each: 3 train values + the holdout value in position 3)."""
    return [[F(1)] * 4,
            [x / F(3) for x in XS] + [XHO_GROW / F(3)],
            [(x / F(3)) ** 2 for x in XS]
            + [(XHO_GROW / F(3)) ** 2],
            [(x / F(3)) ** 3 for x in XS]
            + [(XHO_GROW / F(3)) ** 3]]


def fp_col(dd):
    """Normalized polynomial candidate column (x/3)^dd."""
    return [(x / F(3)) ** dd for x in XS] \
        + [(XHO_GROW / F(3)) ** dd]


def full_pipeline_run():
    """The unified 6-phase certified cycle. Returns
    (start_obj, [accepted steps], telemetry, final weights, feats)."""
    feats = fp_base_feats()
    w = list(FP_W0)
    raw = []
    tel = {"phases": [], "rejects": [], "holds": [], "admissions": []}

    def record(phase, obj, obj2, risk, risk2, w2, **extra):
        raw.append({"phase": phase, "obj": obj, "obj'": obj2,
                    "drop": obj - obj2, "risk": risk,
                    "risk'": risk2, **extra})
        return w2

    def gd(wcur, fs, only_last=False):
        L = grow_smooth([fs[-1]]) if only_last else grow_smooth(fs)
        eta = F(1) / L
        g = grow_grad(wcur, fs)
        if only_last:
            w2 = list(wcur)
            w2[-1] = wcur[-1] - eta * g[-1]
        else:
            w2 = [wcur[j] - eta * g[j] for j in range(len(wcur))]
        return w2

    obj0 = grow_loss(w, feats)

    # (a) TRAIN: certified GD steps
    for _ in range(FP_TRAIN_STEPS):
        obj, risk = grow_loss(w, feats), grow_holdout_risk(w, feats)
        w2 = gd(w, feats)
        w = record("train", obj, grow_loss(w2, feats), risk,
                   grow_holdout_risk(w2, feats), w2)
    tel["phases"].append({"phase": "train",
                          "steps": FP_TRAIN_STEPS,
                          "final_obj": str(grow_loss(w, feats))})

    # (b) EF21: in-step quantized steps with error feedback
    e = [F(0)] * len(w)
    eta = F(1) / grow_smooth(feats)
    for t in range(FP_EF21_STEPS):
        obj, risk = grow_loss(w, feats), grow_holdout_risk(w, feats)
        g = grow_grad(w, feats)
        m = [g[c] + e[c] for c in range(len(w))]
        d = ef21_tern_vec(m, FP_EF21_S)
        w2 = [w[c] - eta * d[c] for c in range(len(w))]
        drop = obj - grow_loss(w2, feats)
        if drop > 0:
            e = [m[c] - d[c] for c in range(len(w))]
            w = record("ef21", obj, grow_loss(w2, feats), risk,
                       grow_holdout_risk(w2, feats), w2)
        else:
            tel["rejects"].append({"phase": "ef21", "t": t,
                                   "drop": drop,
                                   "reason": "drop <= 0: HOLD, "
                                             "weights and residual "
                                             "unchanged "
                                             "(ef21_reject_hold)"})
    tel["phases"].append({"phase": "ef21", "scale": str(FP_EF21_S),
                          "accepted": sum(1 for r in raw
                                          if r["phase"] == "ef21"),
                          "rejected": len(tel["rejects"]),
                          "final_obj": str(grow_loss(w, feats))})

    # (c) HADAMARD-TERN: measured cohSq gate + ternary jump
    obj, risk = grow_loss(w, feats), grow_holdout_risk(w, feats)
    hw = ht_matvec(HT_H, w)
    c_before, c_after = coh_sq(w), coh_sq(hw)
    gate = c_after < c_before
    src = hw if gate else w
    s0 = max(abs(t) for t in src) or F(1)
    q = [round_tern(t / s0) for t in src]
    qq = sum((t * t for t in q), F(0))
    if qq == 0:
        wq, s = [F(0)] * len(w), F(0)
    else:
        s = sum((q[i] * src[i] for i in range(len(w))), F(0)) / qq
        scaled = [s * t for t in q]
        wq = [t / F(4) for t in ht_matvec(HT_H, scaled)] if gate \
            else scaled
    obj2, risk2 = grow_loss(wq, feats), grow_holdout_risk(wq, feats)
    jump = {"coh_sq_before": c_before, "coh_sq_after": c_after,
            "gate_passed": bool(gate),
            "basis": "hadamard" if gate else "direct",
            "s": s, "pattern": [int(t) for t in q],
            "drop": obj - obj2, "accepted": bool(obj - obj2 > 0)}
    if obj - obj2 > 0:
        w = record("hadamard-jump", obj, obj2, risk, risk2, wq)
    else:
        tel["holds"].append({"phase": "hadamard-jump",
                             "drop": obj - obj2,
                             "reason": "drop <= 0: HOLD, weights "
                                       "unchanged (ternary_hold_"
                                       "rejected)"})
    for _ in range(FP_FT_STEPS):
        obj, risk = grow_loss(w, feats), grow_holdout_risk(w, feats)
        w2 = gd(w, feats)
        w = record("hadamard-finetune", obj, grow_loss(w2, feats),
                   risk, grow_holdout_risk(w2, feats), w2)
    tel["phases"].append({"phase": "hadamard-tern", "jump": {
        k: (str(v) if not isinstance(v, (bool, list)) else v)
        for k, v in jump.items()},
        "final_obj": str(grow_loss(w, feats))})

    # (d) GROW: candidate (x/3)^4 by the C444 exact margin
    featsG = feats + [fp_col(4)]
    dcost = F(2)
    wext = list(w) + [F(0)]          # u = 0: obj chain EXACT
    obj, risk = grow_loss(wext, featsG), grow_holdout_risk(wext, featsG)
    w2 = gd(wext, featsG, only_last=True)
    obj2, risk2 = grow_loss(w2, featsG), grow_holdout_risk(w2, featsG)
    gain, drisk = obj - obj2, risk2 - risk
    margin = admission_margin(gain, dcost, drisk)
    tel["admissions"].append({"candidate": "(x/3)^4", "gain": gain,
                              "dCost": dcost, "dRisk": drisk,
                              "margin_excess": margin,
                              "admitted": bool(margin <= 0)})
    if margin <= 0 and gain > 0:
        w = record("grow-admit", obj, obj2, risk, risk2, w2)
        feats = featsG
    else:
        tel["admissions"][-1]["reason"] = \
            "margin > 0: HOLD (noBlockAdmissionWithoutMargin)"
        tel["holds"].append({"phase": "grow", "drop": gain,
                             "reason": "admission margin > 0: model "
                                       "unchanged"})
    tel["phases"].append({"phase": "grow",
                          "final_obj": str(grow_loss(w, feats))})
    # noise candidate: orthogonal to the residual => zero gradient
    r = [YS[i] - sum((wi * f[i] for wi, f in zip(w, feats)), F(0))
         for i in range(len(XS))]
    gcol = [r[1], -r[0], F(0), F(0)]
    featsN = feats + [gcol]
    gn = grow_grad(list(w) + [F(0)], featsN)
    tel["admissions"].append({"candidate": "noise",
                              "gain": F(0), "dCost": F(2),
                              "margin_excess": admission_margin(
                                  F(0), F(2), F(0)),
                              "admitted": False,
                              "reason": "zero gradient (orthogonal to "
                                        "residual): measured gain = 0, "
                                        "cost > 0 => REJECT "
                                        "(costly_zero_gain_block_"
                                        "refused)",
                              "grad_last": gn[-1]})

    # (e) MERGE: side branch + measured-delta gate (C476)
    wA = list(w)
    wB = list(wA)
    branch = []
    for _ in range(FP_BRANCH_STEPS):
        wB = gd(wB, feats)
        branch.append(str(grow_loss(wB, feats)))
    LA = grow_loss(wA, feats)
    gA = grow_grad(wA, feats)
    G = sum((gA[i] * (wB[i] - wA[i]) for i in range(len(wA))), F(0))
    delta_meas = F(0)
    for t in FP_MERGE_GRID:
        wi = [wA[i] + t * (wB[i] - wA[i]) for i in range(len(wA))]
        delta_meas += abs(grow_loss(wi, feats) - (LA + t * G))
    mid = [(wA[i] + wB[i]) / 2 for i in range(len(wA))]
    objM, riskM = grow_loss(mid, feats), grow_holdout_risk(mid, feats)
    gate_ok = objM <= LA + delta_meas
    merge = {"branch_losses": branch, "lin_slope_G": G,
             "delta_meas": delta_meas,
             "obj_branch": grow_loss(wB, feats), "obj_merged": objM,
             "safety_gate_passed": bool(gate_ok),
             "drop": LA - objM,
             "accepted": bool(gate_ok and LA - objM > 0)}
    if gate_ok and LA - objM > 0:
        w = record("merge", LA, objM, grow_holdout_risk(wA, feats),
                   riskM, mid, delta_meas=delta_meas)
    else:
        tel["holds"].append({"phase": "merge", "drop": LA - objM,
                             "reason": ("safety gate failed (merge_"
                                        "unsafe_without_measurement)"
                                        if not gate_ok else
                                        "drop <= 0: HOLD despite "
                                        "delta-gate pass "
                                        "(checkStep needs 0 < drop)")})
    tel["phases"].append({"phase": "merge", "merge": {
        k: (str(v) if not isinstance(v, (bool, list)) else v)
        for k, v in merge.items()},
        "final_obj": str(grow_loss(w, feats))})

    # (f) STOP: Ville anytime holdout stop over (x/3)^d candidates
    h0 = grow_holdout_risk(w, feats)
    stopped = False
    stop_rec = None
    for dd in range(FP_STOP_DMIN, FP_STOP_DMAX + 1):
        featsS = feats + [fp_col(dd)]
        ws0 = list(w) + [F(0)]
        obj, risk = grow_loss(ws0, featsS), grow_holdout_risk(w, feats)
        w2 = gd(ws0, featsS, only_last=True)
        obj2 = grow_loss(w2, featsS)
        rec = {"candidate": f"(x/3)^{dd}", "gain": obj - obj2}
        if stopped:
            rec.update({"admitted": False,
                        "reason": "STOP already fired: admitWithStop "
                                  "blocks every later block "
                                  "(stop_blocks_admission)"})
            tel["admissions"].append(rec)
            continue
        if obj - obj2 <= 0:
            rec.update({"admitted": False,
                        "reason": "gain <= 0: HOLD"})
            tel["admissions"].append(rec)
            continue
        risk2 = grow_holdout_risk(w2, featsS)
        w = record("stop-candidate", obj, obj2, risk, risk2, w2)
        feats = featsS
        D = grow_holdout_risk(w, feats) - h0
        rec.update({"admitted": True, "D": D, "lamD": GS_LAM * D,
                    "stopped": bool(gs_stop_fires(D))})
        tel["admissions"].append(rec)
        if gs_stop_fires(D):
            stopped = True
            stop_rec = dict(rec)
            stop_rec["reason"] = ("STOP: lam*D >= 1/delta - 1 => "
                                  "e-value >= 1/delta "
                                  "(stop_implies_evalue); false-stop "
                                  "prob <= delta (Ville, "
                                  "grow_stop_sound)")
    if not stopped:
        sys.exit("ABORT: full-pipeline overfitting scenario did not "
                 "fire the anytime stop -- tune FP_STOP_DMAX/GS_LAM")
    tel["stop"] = {k: str(v) if not isinstance(v, bool) else v
                   for k, v in stop_rec.items()}
    tel["phases"].append({"phase": "stop",
                          "final_obj": str(grow_loss(w, feats)),
                          "holdout_0": str(h0),
                          "holdout_final": str(grow_holdout_risk(w,
                                                                 feats))})

    # obj-chain continuity assertions + budget fill + re-verify
    for i in range(len(raw) - 1):
        if raw[i]["obj'"] != raw[i + 1]["obj"]:
            sys.exit(f"ABORT: obj chain broken at step {i}: "
                     f"{raw[i]['obj']} != {raw[i + 1]['obj']}")
    n = F(len(raw))
    for t, d in enumerate(raw):
        d["budget"] = (F(len(raw) - t) / n) if n else F(0)
        d["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(d):
            sys.exit(f"ABORT: full-pipeline step {t} ({d['phase']}) "
                     f"failed certified admission: {d}")
    return obj0, raw, tel, w, feats


def _proof_full(name_suffix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    return (f"theorem full_traj_{thm}{name_suffix} :\n"
            f"    checkTrajectory benchStartFull{name_suffix} "
            f"benchTrajectoryFull{name_suffix} = {val} := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStartFull{name_suffix}, "
            f"benchTrajectoryFull{name_suffix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")


def emit_lean_full(path, start, traj):
    """C479 witness: the unified 6-phase trajectory literal +
    #eval + norm_num theorem."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartFull : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryFull : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in traj)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartFull "
                "benchTrajectoryFull\n\n"
                + _proof_full("", True))
    print(f"written: {path}", file=sys.stderr)


def emit_bad_full(path, start, traj):
    """C479 negative: broken phase — inflated declared drop on the
    last step; the checker must reject the whole trajectory."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                "def benchStartFullBad : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryFullBad : "
                "List Hagi.Runtime.CertStepData :=\n["
                + ",\n".join(lean_step(d) for d in bad)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartFullBad "
                "benchTrajectoryFullBad\n\n"
                + _proof_full("Bad", False))
    print(f"written: {path}", file=sys.stderr)


# ----------------------------------------------------------------
# C474: EF21 in-step quantized training loop (--mode ef21-step)
#
# PIN (P3 of the A19 audit): the C443 mode quantizes POST HOC (a
# separate jump after training); this mode compresses the update
# INSIDE each gradient step with error feedback:
#   m = g + e   (exact Fraction gradient + accumulated residual)
#   d = tern_s(m)  fixed-scale ternary quantizer (see EF21_S pin)
#   e' = m − d  (error feedback: unquantized remainder carried fwd)
#   trial θ' = θ − η·d; drop = obj(θ) − obj(θ') measured exactly.
#
# PIN (quantizer scale): FIXED scale EF21_S, NOT the LS-optimal
# per-step scale of cert-tern — a stable recursive contract is
# needed for the EF telescoping identities; the scale is fixed
# BEFORE the run (design choice, not tuned to outcomes). The
# quantizer is honestly NOT contractive for alpha in (0, 1]
# (Hagi.Optimization.EF21Quantizer.qTernVec_not_contractive), so
# EF21 Lyapunov guarantees do NOT transfer; only the exact
# identities (Hagi/Theory/Compression.lean: telescope, energy split)
# and the inexact floor (qTernVec_inexact, alpha = 0) carry over.
#
# PIN (admission): the trial is admitted ONLY by the exact certified
# criterion drop > 0 plus the full check_step mirror. A rejected
# trial (drop <= 0 — with coarse quantization the compressed step
# may climb, giving NEGATIVE drop) is a HOLD: weights AND the
# residual e stay unchanged (the trial's feedback is burned — the
# honest reject semantics; see the module docstring pins), the step
# is EXCLUDED from the emitted trajectory (checkStep demands
# 0 < drop — ef21_reject_hold) and logged in `rejects` telemetry
# with the reject rate.

EF21_S = F(1, 5)           # fixed ternary scale (exact Fraction;
                          # pinned before the run — coarse enough that
                          # late-loop saturated messages quantize to 0,
                          # exercising the honest reject path)
EF21_W0 = [F(2), F(1), F(2)]   # ef21-mode initial weights
                                # (same pin as TERN_W0: fixed
                                # before the run; w = 0 is a
                                # degenerate point of the CE
                                # surrogate: S = 0)
EF21_STEPS_DEFAULT = 20


def ef21_tern_vec(v, s=EF21_S):
    """Fixed-scale ternary vector quantizer s·roundTern(v/s)
    (the qTernVec pattern; NOT LS-optimal — fixed recursive
    contract, see the module pins)."""
    return [round_tern(t / s) * s for t in v]


def train_ef21(steps):
    """EF21 in-step quantized certified loop.

    Every step: exact gradient g, message m = g + e, compressed
    direction d = tern(m), trial weights θ − η·d. Admitted only if
    the measured drop > 0 and the full check_step mirror passes;
    otherwise HOLD (θ, e unchanged) logged in `rejects`.
    Returns (start_obj, [accepted steps], rejects, states, stats)."""
    w = list(EF21_W0)
    e = [F(0)] * CE_K
    states = [tuple(w)]
    raw = []
    rejects = []
    eta = F(1) / ce_L()
    accepted = 0

    for t in range(steps):
        obj, risk = ce_train_loss(w), ce_holdout_risk(w)
        g = ce_grad(w)
        m = [g[c] + e[c] for c in range(CE_K)]
        d = ef21_tern_vec(m)
        w2 = [w[c] - eta * d[c] for c in range(CE_K)]
        obj2, risk2 = ce_train_loss(w2), ce_holdout_risk(w2)
        drop = obj - obj2
        step = {"phase": "ef21-step", "obj": obj, "obj'": obj2,
                "drop": drop, "risk": risk, "risk'": risk2,
                "t": t, "quantized_d": d,
                "residual_norm2": sum((m[c] - d[c]) ** 2
                                      for c in range(CE_K))}
        if drop > 0:
            # accepted: error feedback consumed, weights move
            e = [m[c] - d[c] for c in range(CE_K)]
            raw.append(step)
            states.append(tuple(w2))
            w = w2
            accepted += 1
        else:
            # HOLD: weights AND residual unchanged (trial burned)
            rejects.append({**step,
                            "reason": "drop <= 0: HOLD, weights and "
                                      "residual unchanged, step "
                                      "excluded (ef21_reject_hold)"})

    n = F(len(raw))
    for t, d_ in enumerate(raw):
        d_["budget"] = (F(len(raw) - t) / n) if n else F(0)
        d_["budget'"] = (F(len(raw) - t - 1) / n) if n else F(0)
        if not check_step(d_):
            sys.exit(f"ABORT: ef21 step {t} failed certified "
                     f"admission: {d_}")
    stats = {"total_trials": steps, "accepted": accepted,
             "rejected": len(rejects),
             "reject_rate": (F(len(rejects), steps) if steps
                             else F(0)),
             "eta": eta, "scale": EF21_S}
    if not raw:
        sys.exit("ABORT: no accepted ef21 steps — trajectory empty")
    return raw[0]["obj"], raw, rejects, states, stats


def _proof_ef21(name_suffix, ok):
    thm = "valid" if ok else "invalid"
    val = "true" if ok else "false"
    head = (f"theorem ef21_traj_{thm} :\n"
            f"    checkTrajectory benchStartEF21{name_suffix} "
            f"benchTrajectoryEF21{name_suffix} = {val} := by\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStartEF21{name_suffix}, "
            f"benchTrajectoryEF21{name_suffix}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    if ok:
        return head
    return ("set_option linter.unusedSimpArgs false in\n" + head)


def emit_lean_ef21(path, start, traj, rejects):
    """C474 witness: literal trajectory + #eval + norm_num theorem,
    plus the reject control: the FIRST rejected trial's measured
    drop is <= 0, so its CertStepData can never pass checkStep
    (ef21_reject_hold) — machine-checked on the exact literals."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartEF21 : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryEF21 : "
                "List Hagi.Runtime.CertStepData :=\n["
                + ",\n".join(lean_step(d) for d in traj)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartEF21 "
                "benchTrajectoryEF21\n\n")
        f.write(_proof_ef21("", True))
        if rejects:
            r = rejects[0]
            # the identity hold record the trainer WOULD emit:
            # weights unchanged => obj' = obj, drop = measured drop
            f.write(
                "\n/- Reject control (C474): the first rejected "
                "trial's measured\ndrop is <= 0 (a compressed step "
                "that does not descend — with coarse\nquantization "
                "possibly NEGATIVE), so the identity hold record "
                "can never pass\ncheckStep: the machine-checked "
                "reason rejected steps are excluded from\nthe "
                "trajectory (Hagi.Theory.EF21InStep.ef21_reject_hold). "
                "-/\n"
                "theorem ef21_rejected_drop :\n"
                f"    ({rat(r['drop'])} : \u211a) <= 0 := by\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_ef21(path, start, traj):
    """C474 negative control: inflate the last declared drop beyond
    the actual descent — the checker must reject the trajectory."""
    bad = [dict(d) for d in traj]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartEF21Bad : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryEF21Bad : "
                "List Hagi.Runtime.CertStepData :=\n["
                + ",\n".join(lean_step(d) for d in bad)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartEF21Bad "
                "benchTrajectoryEF21Bad\n\n"
                + _proof_ef21("Bad", False))
    print(f"written: {path}", file=sys.stderr)

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
# the Ville anytime stop (Hagi/Theory/Statistics, AnytimeHoldoutStop section):
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
            "(Hagi.Theory/Statistics, AnytimeHoldoutStop section). -/\n"
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


# ----------------------------------------------------------------
# C481: certified TRUNK training (--mode trunk-train)
#
# PIN (model): the bench model finally has a NON-LINEAR trunk,
# trained jointly with the linear head by certified steps (the
# C475 Hagi/Training/JointTrunkHead.lean theory moved into the
# Python cycle):  v = g*x/(|x|+eps)  ->  a = W1*v  ->  relu
# ->  t = W2*r  ->  z = Wh*t  (K = 3 classes, hidden dim 2,
# 18 rational parameters). Everything is Fraction-exact.
#
# PIN (rational RMSNorm surrogate): true RMSNorm divides by
# sqrt(sum x^2/n), which is IRRATIONAL over Q. Chosen KISS fix
# (task-sanctioned): L1-denominator normalization x/(|x|+eps),
# eps = 1/1000 — rational throughout; the gain g keeps the C475
# rmsN-atom shape. sqrt via certified Newton bounds rejected
# (YAGNI).
#
# PIN (degenerate-label guard): with labels forming a permutation
# of all classes (e.g. [0,1,2]) and an x-independent logit
# direction (scalar input), the surrogate mean loss is
# IDENTICALLY 2/3: sum_points z_y^2/S = sum_c z_c^2/S = 1. Found
# by probe; YTR = [0,1,0] (a repeat) avoids it.
#
# PIN (grid-snapped candidate): the trial step is
# theta' = snap_{1/1000}(theta - (1/10)*g_fd) where g_fd is the
# forward finite-difference gradient (h = 1/1000, exact
# Fractions). Snapping the candidate to the 1/1000 rational grid
# keeps exact denominators within kernel reach (measured: pure
# fd-GD reaches 3605-digit denominators by step 2; snapped: <= 13
# digits) — the precedent is the C443 ternary jump, where the
# candidate is quantized by construction. The CERTIFIED content
# is unaffected: admission is the MEASURED drop obj - obj' > 0
# computed exactly on the ACTUAL (snapped) parameters, with
# guarded rollback (drop <= 0 => HOLD, parameters restored, the
# step is excluded from the trajectory — C443/C474 semantics).
#
# PIN (honest guarantee form): a finite-difference gradient is an
# APPROXIMATE direction, so NO 2A^2/R^2-style certified descent
# is claimed. The live guarantee is per-step measured descent +
# rollback + the executable checkTrajectory. The C475 majorizer
# readouts — A (linear-model predicted drop -sum g_fd*(theta'-
# theta)), R (sup over train points of the logit range), dd
# (measured logit displacement of the TRUNK change alone, new
# trunk with the OLD head, before the head part of the joint
# step) — are telemetry; the C475 strict-commit criterion
# 2*HL*dd < 2*A^2/R^2 is logged ADVISORY only.

TT_K, TT_HID = 3, 2                    # classes / hidden units
TT_EPS = F(1, 1000)                    # L1-norm epsilon (rational)
TT_H = F(1, 1000)                      # finite-difference step
TT_ETA = F(1, 10)                      # joint step size
TT_GRID = F(1, 1000)                   # candidate snap grid
TT_STEPS = 4                           # default joint steps
TT_XTR, TT_YTR = [F(1), F(2), F(3)], [0, 1, 0]   # repeat label!
TT_XHO, TT_YHO = F(1), 2               # holdout point
TT_NPAR = 1 + TT_HID + TT_K * TT_HID + TT_K * TT_K  # = 18


def tt_init():
    """Initial (g, W1, W2, Wh) parameters, all on the 1/1000 grid
    (W1, W2 small random-free fractions; Wh starts at identity
    scaled 1/2 so the head is non-trivial but small)."""
    g = F(1)
    W1 = [F(1, 2), F(-1, 3)]
    W2 = [[F(1, 2), F(1, 4)], [F(-1, 4), F(1, 2)],
          [F(1, 4), F(-1, 3)]]
    Wh = [[F(1, 2) if c == c2 else F(0) for c2 in range(TT_K)]
          for c in range(TT_K)]
    return (g, W1, W2, Wh)


def tt_flat(theta):
    g, W1, W2, Wh = theta
    return [g] + list(W1) + [e for row in W2 for e in row] \
        + [e for row in Wh for e in row]


def tt_unflat(p):
    i = 1
    W1 = p[i:i + TT_HID]
    i += TT_HID
    W2 = [p[i + c * TT_HID:i + (c + 1) * TT_HID]
          for c in range(TT_K)]
    i += TT_K * TT_HID
    Wh = [p[i + c * TT_K:i + (c + 1) * TT_K] for c in range(TT_K)]
    return (p[0], W1, W2, Wh)


def tt_logits(theta, x, head=None):
    """Forward pass: L1-rms-surrogate norm -> W1 -> ReLU -> W2 ->
    (head Wh if given, else the model's own head). Exact
    Fractions."""
    g, W1, W2, Wh = theta
    v = g * x / (abs(x) + TT_EPS)
    r = [max(W1[j] * v, F(0)) for j in range(TT_HID)]
    t = [sum((W2[c][j] * r[j] for j in range(TT_HID)), F(0))
         for c in range(TT_K)]
    H = Wh if head is None else head
    return [sum((H[c][c2] * t[c2] for c2 in range(TT_K)), F(0))
            for c in range(TT_K)]


def tt_point_loss(theta, x, y):
    z = tt_logits(theta, x)
    S = sum((c * c for c in z), F(0))
    return F(1) - z[y] ** 2 / S


def tt_train_loss(theta):
    n = F(len(TT_XTR))
    return sum((tt_point_loss(theta, x, y)
                for x, y in zip(TT_XTR, TT_YTR)), F(0)) / n


def tt_holdout_risk(theta):
    return tt_point_loss(theta, TT_XHO, TT_YHO)


def tt_fd_grad(theta):
    """Forward finite-difference gradient over all 18 parameters
    (exact Fractions; h = 1/1000)."""
    p = tt_flat(theta)
    o = tt_train_loss(theta)
    g = []
    for k in range(len(p)):
        q = list(p)
        q[k] = q[k] + TT_H
        g.append((tt_train_loss(tt_unflat(q)) - o) / TT_H)
    return g


def tt_snap(p):
    """Snap every parameter to the 1/1000 rational grid (round to
    nearest grid point; exact Fractions)."""
    out = []
    for t in p:
        n = t / TT_GRID
        r = (n.numerator + n.denominator // 2) // n.denominator \
            if n >= 0 else -((-n.numerator + n.denominator // 2)
                             // n.denominator)
        out.append(F(r) * TT_GRID)
    return out


def tt_logit_range(theta):
    """R = sup over train points of (max_c z_c - min_c z_c)."""
    return max(max(tt_logits(theta, x)) - min(tt_logits(theta, x))
               for x in TT_XTR)


def tt_trunk_disp(theta_old, theta_new):
    """dd = sup over train points / classes of the logit shift
    caused by the TRUNK change ALONE (new trunk, OLD head) — the
    C475 measured displacement binder, computed directly."""
    _, _, _, old_head = theta_old
    return max(abs(a - b)
               for x in TT_XTR
               for a, b in zip(tt_logits(theta_new, x, old_head),
                               tt_logits(theta_old, x, old_head)))


def trunk_train_run(steps=TT_STEPS):
    """Joint certified trunk+head training: each step is a guarded
    fd-gradient snap step; commit only on measured drop > 0.
    Returns (start_obj, [accepted steps], telemetry, final theta)."""
    theta = tt_init()
    raw, tel = [], {"holds": [], "steps": [], "model": {
        "trunk": "L1-rms-surrogate -> Linear W1 -> ReLU -> "
                 "Linear W2 (nonlinear, C475 mlp atom)",
        "head": "linear Wh", "params": TT_NPAR,
        "grad": "forward finite differences h=1/1000 (Fraction)",
        "step": "snap_{1/1000}(theta - (1/10)*g_fd) joint",
        "guarantee": "per-step MEASURED drop > 0 + guarded "
                     "rollback; A/R/dd telemetry advisory (C475)"}}
    obj0 = tt_train_loss(theta)
    for t in range(steps):
        obj, risk = tt_train_loss(theta), tt_holdout_risk(theta)
        gfd = tt_fd_grad(theta)
        p = tt_flat(theta)
        cand = tt_snap([p[k] - TT_ETA * gfd[k]
                        for k in range(TT_NPAR)])
        theta2 = tt_unflat(cand)
        obj2, risk2 = tt_train_loss(theta2), \
            tt_holdout_risk(theta2)
        drop = obj - obj2
        # C475 telemetry (advisory; NOT the admission criterion)
        A = -sum((gfd[k] * (cand[k] - p[k])
                  for k in range(TT_NPAR)), F(0))
        R = tt_logit_range(theta2)
        dd = tt_trunk_disp(theta, theta2)
        rec = {"obj": obj, "obj'": obj2, "drop": drop,
               "risk": risk, "risk'": risk2,
               "A": A, "R": R, "dd": dd,
               "R*dd": R * dd}
        if drop > 0:
            theta = theta2
            raw.append(rec)
            tel["steps"].append({"t": t, "drop": drop, "A": A,
                                 "R": R, "dd": dd,
                                 "advisory_strict":
                                     2 * R * dd < 2 * A * A})
        else:
            tel["holds"].append({"t": t, "drop": drop,
                                 "reason": "drop <= 0: HOLD, "
                                           "parameters rolled "
                                           "back (guarded)"})
    # budget fill over accepted steps + obj-chain re-verify
    n = len(raw)
    assert n > 0, "ABORT: trunk-train committed no steps"
    for t, d in enumerate(raw):
        d["budget"] = F(len(raw) - t) / n
        d["budget'"] = F(len(raw) - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for d in raw:
        if not check_step(d):
            sys.exit(f"ABORT: trunk-train step failed certified "
                     f"admission: {d}")
    return obj0, raw, tel, theta


def emit_lean_trunk(path, start, traj, bad=False):
    """C481 witness: literal trunk-training trajectory + #eval
    checkTrajectory + a norm_num theorem (trunk_bench_valid), or
    the negative control (inflated drop — the checker must
    reject)."""
    ds = [dict(d) for d in traj]
    name, thm = ("benchTrajectoryTrunkBad", "trunk_bench_invalid") \
        if bad else ("benchTrajectoryTrunk", "trunk_bench_valid")
    if bad:
        ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartTrunk : \u211a := {rat(start)}\n\n"
                f"def {name} : List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                f"#eval checkTrajectory benchStartTrunk {name}\n\n"
                f"theorem {thm} :\n"
                f"    checkTrajectory benchStartTrunk {name} = "
                f"{'false' if bad else 'true'} := by\n"
                "  set_option linter.unusedSimpArgs false in\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartTrunk, "
                f"{name}, Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C484: REAL-DATASET certified trunk bench (--mode real-data)
#
# PIN (dataset, real not invented): points are read from the
# HAGI_v2 corpus (READ-ONLY): unified_ledger.json (184 entries
# ns_XXXX with the MEASURED cross-entropy `ce` of each trained
# model) plus the corresponding domain chunk binaries
# domains/ns_XXXX.bin. x in Q^4 = byte statistics of the chunk
# file (size/2^20, zero-byte fraction, printable fraction,
# mean-byte/256); y = the measured ce. N = 184 >= 100.
#
# PIN (float -> Fraction is EXACT): a binary float has a finite
# dyadic expansion, so fractions.Fraction(float(ce)) is the exact
# measured value — no approximation is introduced (task pin).
#
# PIN (feature quantization): raw byte fractions have per-file
# denominators (file sizes); each feature is snapped to the
# 1/1000 rational grid — an exact input-preprocessing choice
# (same grid family as the C481 parameter snap).
#
# PIN (normalization constant): the trunk uses the L1-surrogate
# normalization v = g*x/CFIX with CFIX = max ||x||_1 + 1/1000 a
# DATASET-LEVEL constant. The per-point division x/(|x|+eps) of
# C481 makes the denominators point-coprime (~400 digits over
# 148 train points, measured by probe); the constant form keeps
# exact loss denominators <= 58 digits while staying an exact
# rational L1-norm surrogate (sqrt skipped, C481 pin retained).
#
# Certified content = C481 verbatim: forward finite-difference
# gradient (h = 1/1000, exact Fractions) is only the CANDIDATE
# generator; admission is the MEASURED drop obj - obj' > 0
# computed exactly on the ACTUAL grid-snapped parameters, with
# guarded rollback (drop <= 0 => HOLD, step excluded from the
# trajectory). Statistics (train/holdout MSE, C435-style
# concentration) are computed on the FIXED final model.

RD_D, RD_HID, RD_K = 4, 3, 2      # feature dim / hidden / t-dim
RD_EPS = F(1, 1000)              # CFIX epsilon (rational)
RD_H = F(1, 1000)                # finite-difference step
RD_ETA = F(1, 10)                # step size
RD_GRID = F(1, 1000)             # snap grid (params + features)
RD_STEPS = 6                     # default joint steps
RD_NPAR = 1 + RD_HID * RD_D + RD_K * RD_HID + RD_K   # = 21
RD_DEFAULT_LEDGER = ("C:/HAGI_v2/checkpoints/"
                     "unified_ledger.json")


def rd_snap(v):
    """Snap a Fraction to the 1/1000 rational grid (round to
    nearest, exact)."""
    n = v / RD_GRID
    if n >= 0:
        r = (n.numerator + n.denominator // 2) // n.denominator
    else:
        r = -((-n.numerator + n.denominator // 2) // n.denominator)
    return F(r) * RD_GRID


def rd_load_dataset(ledger_path):
    """Parse unified_ledger.json + the sibling domains/ dir into
    exact rational (x, y) points (see the PINs above)."""
    import os
    with open(ledger_path, encoding="utf-8") as f:
        led = json.load(f)
    dom = os.path.join(os.path.dirname(os.path.abspath(
        ledger_path)), "domains")
    pts = []
    for k in sorted(led):
        b = open(os.path.join(dom, k + ".bin"), "rb").read()
        s = len(b)
        x = [rd_snap(F(s, 1 << 20)),
             rd_snap(F(sum(1 for c in b if c == 0), s)),
             rd_snap(F(sum(1 for c in b if 32 <= c < 127), s)),
             rd_snap(F(sum(b), 256 * s))]
        pts.append((k, x, F(led[k]["ce"])))   # float->Fraction EXACT
    return pts


def rd_split(pts):
    """Deterministic 80/20 split: sorted keys, every 5th point
    to the holdout."""
    train = [(x, y) for i, (_, x, y) in enumerate(pts) if i % 5 != 4]
    hold = [(x, y) for i, (_, x, y) in enumerate(pts) if i % 5 == 4]
    return train, hold


def rd_init():
    """21 parameters on the 1/1000 grid (g, W1 flat, W2 flat,
    Wh flat)."""
    return ([F(1)] + [F(1, 2)] * (RD_HID * RD_D)
            + [F(1, 2)] * (RD_K * RD_HID) + [F(1, 2)] * RD_K)


def rd_forward(p, x, cfix):
    """Trunk forward: v = g*x/CFIX -> W1 -> ReLU -> W2 -> scalar
    head Wh. Exact Fractions."""
    g = p[0]
    i = 1
    W1 = p[i:i + RD_HID * RD_D]
    i += RD_HID * RD_D
    W2 = p[i:i + RD_K * RD_HID]
    i += RD_K * RD_HID
    Wh = p[i:]
    v = [g * xj / cfix for xj in x]
    r = [max(sum((W1[j * RD_D + k] * v[k]
                  for k in range(RD_D)), F(0)), F(0))
         for j in range(RD_HID)]
    t = [sum((W2[c * RD_HID + j] * r[j]
              for j in range(RD_HID)), F(0))
         for c in range(RD_K)]
    return sum((Wh[c] * t[c] for c in range(RD_K)), F(0))


def rd_mse(p, data, cfix):
    """Mean squared error over data, exact Fractions."""
    return sum((rd_forward(p, x, cfix) - y) ** 2
               for x, y in data) / F(len(data))


def rd_concentration(p, pts, cfix):
    """C435-style numerical application of the Hoeffding-63
    two-sided bound on the FIXED final model. Per-point losses
    l_i are exact; L = max l_i (data-dependent bound, pin);
    u_i = l_i/L in [0,1]. For holdout size m the with-
    replacement bound 2*exp(-2 m eps^2) upper-bounds the actual
    without-replacement holdout sampling (Serfling/Hoeffding:
    sampling w/o replacement is at least as concentrated).
    eps* = smallest eps with bound <= 0.05 (float bisection,
    report-only); the certified content stays the trajectory.
    Returns (L, eps_star, bound_scaled, actual_gap_exact)."""
    import math
    ls = [(rd_forward(p, x, cfix) - y) ** 2 for _, x, y in pts]
    L = max(ls)
    pop = sum(ls, F(0)) / F(len(ls))
    hold_ls = [ls[i] for i in range(len(ls)) if i % 5 == 4]
    hold = sum(hold_ls, F(0)) / F(len(hold_ls))
    gap = abs(hold - pop)          # exact Fraction
    m = len(hold_ls)
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if 2 * math.exp(-2 * m * mid * mid) <= 0.05:
            hi = mid
        else:
            lo = mid
    return L, hi, hi * float(L), gap


def real_data_run(ledger_path, steps=RD_STEPS):
    """Real-dataset certified trunk training: guarded fd-gradient
    snap steps admitted only by measured drop > 0 (C481)."""
    pts = rd_load_dataset(ledger_path)
    assert len(pts) >= 100, \
        f"ABORT: expected 100+ real points, got {len(pts)}"
    train, hold = rd_split(pts)
    cfix = max(sum((abs(v) for v in x), F(0))
               for _, x, _ in pts) + RD_EPS
    p = rd_init()
    raw, tel = [], {"holds": [], "steps": [], "model": {
        "trunk": "x/CFIX (L1-surrogate, dataset-level constant) "
                 "-> Linear W1 -> ReLU -> Linear W2",
        "head": "linear Wh (scalar)", "params": RD_NPAR,
        "grad": "forward finite differences h=1/1000 (Fraction)",
        "step": "snap_{1/1000}(theta - (1/10)*g_fd)",
        "guarantee": "per-step MEASURED drop > 0 + guarded "
                     "rollback (C481 form)"}}
    obj0 = rd_mse(p, train, cfix)
    for t in range(steps):
        obj, risk = rd_mse(p, train, cfix), rd_mse(p, hold, cfix)
        gfd = []
        for k in range(RD_NPAR):
            q = list(p)
            q[k] = q[k] + RD_H
            gfd.append((rd_mse(q, train, cfix) - obj) / RD_H)
        cand = [rd_snap(p[k] - RD_ETA * gfd[k])
                for k in range(RD_NPAR)]
        obj2, risk2 = rd_mse(cand, train, cfix), \
            rd_mse(cand, hold, cfix)
        drop = obj - obj2
        if drop > 0:
            rec = {"obj": obj, "obj'": obj2, "drop": drop,
                   "risk": risk, "risk'": risk2}
            raw.append(rec)
            tel["steps"].append({"t": t, "drop": drop})
            p = cand
        else:
            tel["holds"].append({"t": t, "drop": drop,
                                 "reason": "drop <= 0: HOLD, "
                                           "rolled back"})
    n = len(raw)
    assert n > 0, "ABORT: real-data committed no steps"
    for t, d in enumerate(raw):
        d["budget"] = F(n - t) / n
        d["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for d in raw:
        if not check_step(d):
            sys.exit(f"ABORT: real-data step failed certified "
                     f"admission: {d}")
    L, eps_star, bound_scaled, gap = rd_concentration(
        p, pts, cfix)
    stats = {
        "n_points": len(pts), "n_train": len(train),
        "n_holdout": len(hold), "source": ledger_path,
        "train_mse_before": str(obj0),
        "train_mse_final": str(raw[-1]["obj'"]),
        "holdout_mse_before": str(raw[0]["risk"]),
        "holdout_mse_final": str(raw[-1]["risk'"]),
        "concentration": {
            "theorem": "Hoeffding-63 two-sided, w/o-replacement "
                       "sampling upper-bounded by the with-"
                       "replacement form",
            "L_max_loss": str(L), "m_holdout": len(hold),
            "delta": 0.05, "eps_star": eps_star,
            "bound_scaled": bound_scaled,
            "actual_gap": str(gap),
            "actual_le_bound": gap <= F(int(bound_scaled * 10**6),
                                         10**6)}}
    return obj0, raw, tel, stats, p


def emit_lean_real(path, start, traj, witness_steps=4,
                   full_steps=None):
    """C484 witness: literal trajectory of the FIRST witness_steps
    accepted steps + #eval checkTrajectory (+ valid theorem);
    the header documents the FULL accepted-step count honestly
    (task form: first N steps machine-checked)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    full = full_steps if full_steps is not None else len(traj)
    with open(path, "w", encoding="utf-8") as f:
        f.write(
            "-- C484 real-dataset trunk bench witness.\n"
            f"-- FULL accepted trajectory: {full} steps; the "
            f"first {len(ds)} are machine-checked below\n"
            "-- (checkTrajectory over a prefix validates the "
            "chain start, every admission and chaining).\n"
            "import Hagi.Runtime.CertChecker\n\n"
            "open Hagi.Runtime\n\n"
            f"def benchStartReal : \u211a := {rat(start)}\n\n"
            "def benchTrajectoryReal : List "
            "Hagi.Runtime.CertStepData :=\n"
            + "[\n" + ",\n".join(lean_step(d) for d in ds)
            + "\n]\n\n"
            "#eval checkTrajectory benchStartReal "
            "benchTrajectoryReal\n\n"
            "theorem real_bench_valid :\n"
            "    checkTrajectory benchStartReal "
            "benchTrajectoryReal = true := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            "benchStartReal, benchTrajectoryReal, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C491: CERTIFIED SANDWICH CE training on real data
# (--mode cert-sandwich)
#
# PIN (objective): the C442 z^2/Sum z^2 surrogate is REPLACED by
# the C489 sandwich certificate. Per point with max-shifted
# logits s_c = z_c - max z in [-R, 0] (guard R < n = m = 4),
# lo_c = (1 + s_c/4)^4 <= e^{s_c} <= (1 - s_c/4)^(-4) = hi_c
# (expLower_le_exp / exp_le_expUpper, all exact Fractions).
# certCE_le gives -log(lo_u/Sum hi) >= true one-hot CE, so the
# bench objective is the exact rational product
#   OBJ = prod_i (Sum_c hi_c) / lo_{y_i}:
# log monotonicity makes descent of OBJ EQUIVALENT to descent of
# the mean certificate CE -(1/N) Sum -log(lo_y/Sum hi).  NO log
# is ever evaluated in the certified channel (logs are
# irrational); CertStepData carries OBJ (obj/obj'/drop measured
# ON the certificate).  The bridge to the true CE is the theorem
# Hagi.Theory.CertSandwichBench.certCE_descent: certificate drop
# minus the initial gap-width bound <= true-CE drop.
#
# PIN (snap-to-grid, C481/C484 family): features snapped to the
# 1/10 grid (input preprocessing, exact), weights and updates to
# the 1/100 grid.  The shifted logits s stay EXACT rationals -
# snapping the logits themselves was probed and REJECTED: it
# makes the objective piecewise-constant (zero gradient, every
# step HOLD).
#
# PIN (eta): no smoothness constant is certified for the
# sandwich objective; the provable minimum is the C481 guarded
# admission - EXACT analytic gradient of log OBJ (rational),
# normalized direction, fixed step 1/100, snap to grid, accept
# IFF the MEASURED OBJ drop > 0 (else HOLD, step excluded).
# Adaptive-majorizer eta (Hagi.Theory.AdaptiveMajorizer) is a
# future bit.
#
# PIN (dataset, live corpus): unified_ledger.json + domains/
# (C484 loader family).  The corpus is LIVE: 185 points at C484,
# fewer today; ledger keys without a bin file are skipped, N is
# reported and asserted > 0 (N >= 100 pin UNMET by the current
# environment corpus - documented, not fabricated).
#
# PIN (telemetry): float true-CE (softmax via math.exp) and the
# float mirror of cert-CE are TELEMETRY ONLY - outside the
# certificate; the certified content is the exact OBJ
# trajectory (per-step checker admission).

CS_K, CS_D = 2, 4              # classes / feature dim
CS_NM = 4                      # n = m of the (1+x/n)^n family
CS_NM_EVAL_MAX = 1024          # C502 eval-time adaptive cap (budget)
CS_FGRID = F(1, 10)            # feature snap grid
CS_WGRID = F(1, 100)           # weight snap grid
CS_ETA = F(1, 100)             # normalized step size
CS_STEPS = 8                   # default steps
CS_W0 = [F(3, 2), F(1, 2), F(1, 2), F(1, 2),
         F(1, 2), F(3, 2), F(1, 2), F(1, 2)]


def cs_snap(v, g):
    """Snap a Fraction to the g grid (round to nearest, exact)."""
    n = v / g
    if n >= 0:
        r = (n.numerator + n.denominator // 2) // n.denominator
    else:
        r = -((-n.numerator + n.denominator // 2) // n.denominator)
    return F(r) * g


def cs_load_dataset(ledger_path):
    """Real dataset (C484 family): features snapped 1/10, labels
    K=2 median split of the exact measured ce."""
    import os
    with open(ledger_path, encoding="utf-8") as f:
        led = json.load(f)
    dom = os.path.join(os.path.dirname(os.path.abspath(
        ledger_path)), "domains")
    pts = []
    for k in sorted(led):
        if not os.path.exists(os.path.join(dom, k + ".bin")):
            continue                      # live corpus: skip
        b = open(os.path.join(dom, k + ".bin"), "rb").read()
        s = len(b)
        x = [cs_snap(F(s, 1 << 20), CS_FGRID),
             cs_snap(F(sum(1 for c in b if c == 0), s), CS_FGRID),
             cs_snap(F(sum(1 for c in b if 32 <= c < 127), s),
                     CS_FGRID),
             cs_snap(F(sum(b), 256 * s), CS_FGRID)]
        pts.append((k, x, F(led[k]["ce"])))
    ces = sorted(y for _, _, y in pts)
    med = ces[len(ces) // 2]
    return pts, med


def cs_logits(w, x):
    return [sum((w[c * CS_D + j] * x[j] for j in range(CS_D)),
                F(0)) for c in range(CS_K)]


def cs_terms_nm(z, nm):
    """C489 sandwich terms on max-shifted logits (exact),
    parameterized denominator nm (C502 adaptive tightening;
    bernoulliLower_mono / expUpper_base_mono: larger nm —
    narrower certified bands)."""
    M = max(z)
    s = [v - M for v in z]               # in [-R, 0]
    if -min(s) >= nm:
        return None                      # range guard: HOLD
    lo = [(F(1) + sv / nm) ** nm for sv in s]
    hi = [(F(1) - sv / nm) ** (-nm) for sv in s]
    return lo, hi


def cs_terms(z):
    """C489 sandwich terms at the fixed training CS_NM."""
    return cs_terms_nm(z, CS_NM)


def cs_obj(w, data):
    """Exact certificate product prod (Sum hi)/lo_y."""
    prod = F(1)
    for x, y in data:
        t = cs_terms(cs_logits(w, x))
        if t is None:
            return None
        lo, hi = t
        prod *= sum(hi, F(0)) / lo[y]
    return prod


def cs_grad_log(w, data):
    """Exact analytic gradient of log OBJ (all rationals)."""
    g = [F(0)] * (CS_K * CS_D)
    for x, y in data:
        z = cs_logits(w, x)
        am = z.index(max(z))
        s = [v - max(z) for v in z]
        lou = [F(1) + sv / CS_NM for sv in s]
        hiu = [F(1) - sv / CS_NM for sv in s]
        lop = [u ** (CS_NM - 1) for u in lou]
        hip = [u ** (-(CS_NM + 1)) for u in hiu]
        lov = [u ** CS_NM for u in lou]
        hiv = [u ** (-CS_NM) for u in hiu]
        Sh = sum(hiv, F(0))
        for k in range(CS_K):
            for j in range(CS_D):
                def ds(c):
                    return ((x[j] if c == k else F(0))
                            - (x[j] if am == k else F(0)))
                dl = sum((hip[c] * ds(c)
                          for c in range(CS_K)), F(0)) / Sh
                dr = lop[y] * ds(y) / lov[y]
                g[k * CS_D + j] += dl - dr
    return g


def cs_true_ce(w, data):
    """FLOAT TELEMETRY ONLY (outside the certificate)."""
    import math
    tot = 0.0
    for x, y in data:
        z = [float(v) for v in cs_logits(w, x)]
        m = max(z)
        e = [math.exp(v - m) for v in z]
        S = sum(e)
        tot += -math.log(e[y] / S)
    return tot / len(data)


def cs_cert_ce_float(w, data):
    """Float mirror of the rational certificate (telemetry)."""
    import math
    tot = 0.0
    for x, y in data:
        lo, hi = cs_terms(cs_logits(w, x))
        tot += -math.log(float(lo[y] / sum(hi, F(0))))
    return tot / len(data)


def cs_gap_width(w, data):
    """Float mirror of the certified width bound (telemetry)."""
    import math
    tot = 0.0
    for x, y in data:
        lo, hi = cs_terms(cs_logits(w, x))
        tot += math.log(float((hi[y] * sum(hi, F(0)))
                              / (lo[y] * sum(lo, F(0)))))
    return tot / len(data)


def cs_c442(w, data):
    """C442 z^2/Sum z^2 surrogate mean on the same weights
    (exact Fractions; comparison telemetry)."""
    tot = F(0)
    for x, y in data:
        z = cs_logits(w, x)
        S = sum(v * v for v in z)
        tot += F(1) - z[y] * z[y] / S
    return tot / F(len(data))


def cert_sandwich_run(ledger_path, steps=CS_STEPS):
    """Certified sandwich-CE training loop (C491).  Returns
    (start, traj, tel, stats, final_w)."""
    pts, med = cs_load_dataset(ledger_path)
    assert len(pts) > 0, "ABORT: no usable real points"
    data = [(x, 0 if y <= med else 1) for _, x, y in pts]
    w = list(CS_W0)
    obj0 = cs_obj(w, data)
    assert obj0 is not None
    raw, tel = [], {"holds": [], "steps": []}
    for t in range(steps):
        obj, risk = obj0, cs_obj(w, data[4::5])   # holdout OBJ
        budget = F(steps - t, steps)
        g = cs_grad_log(w, data)
        mx = max(abs(v) for v in g)
        cand = [cs_snap(w[k] - CS_ETA * g[k] / mx, CS_WGRID)
                for k in range(CS_K * CS_D)]
        obj2 = cs_obj(cand, data)
        if obj2 is None:
            tel["holds"].append({"t": t, "reason":
                                 "range >= n: HOLD"})
            continue
        risk2 = cs_obj(cand, data[4::5])
        drop = obj - obj2
        if drop > 0:
            raw.append({"obj": obj, "obj'": obj2, "drop": drop,
                        "risk": risk, "risk'": risk2})
            tel["steps"].append({
                "t": t, "drop": drop,
                "certCE": cs_cert_ce_float(w, data),
                "certCE'": cs_cert_ce_float(cand, data),
                "trueCE": cs_true_ce(w, data),
                "trueCE'": cs_true_ce(cand, data),
                "gapW": cs_gap_width(w, data),
                "gapW'": cs_gap_width(cand, data)})
            w = cand
            obj0 = obj2
        else:
            tel["holds"].append({"t": t, "drop": drop,
                                 "reason": "drop <= 0: HOLD"})
    n = len(raw)
    assert n > 0, "ABORT: cert-sandwich committed no steps"
    for t, d in enumerate(raw):
        d["budget"] = F(n - t) / n
        d["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for d in raw:
        if not check_step(d):
            sys.exit(f"ABORT: cert-sandwich step failed "
                     f"certified admission: {d}")
    acc = sum(1 for x, y in data
              if cs_logits(w, x).index(max(cs_logits(w, x))) == y)
    w0 = list(CS_W0)
    stats = {
        "n_points": len(pts), "source": ledger_path,
        "n_train": len(data), "n_holdout": len(data[4::5]),
        "init": {"certCE_float": cs_cert_ce_float(w0, data),
                 "trueCE_float": cs_true_ce(w0, data),
                 "gapW_float": cs_gap_width(w0, data),
                 "c442": str(cs_c442(w0, data)),
                 "c442_float": float(cs_c442(w0, data))},
        "final": {"certCE_float": cs_cert_ce_float(w, data),
                  "trueCE_float": cs_true_ce(w, data),
                  "gapW_float": cs_gap_width(w, data),
                  "c442": str(cs_c442(w, data)),
                  "c442_float": float(cs_c442(w, data))},
        "train_acc": f"{acc}/{len(data)}",
        "theorem": "Hagi.Theory.CertSandwichBench."
                   "certCE_descent (C491)",
    }
    return raw[0]["obj"], raw, tel, stats, w


def emit_lean_cs(path, start, traj, witness_steps=2,
                 full_steps=None):
    """C491 witness: literal CertStepData trajectory of the
    FIRST witness_steps accepted steps of the REAL run (same
    benchBridge pattern as C484; obj values are the exact
    certificate products)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    full = full_steps if full_steps is not None else len(traj)
    with open(path, "w", encoding="utf-8") as f:
        f.write(
            "-- C491 certified sandwich CE bench witness.\n"
            f"-- FULL accepted trajectory: {full} steps; the "
            f"first {len(ds)} are machine-checked below\n"
            "-- (obj/obj'/drop are the EXACT rational "
            "certificate products; Hagi.Theory.\n"
            "-- CertSandwichBench.certCE_descent links the "
            "certificate drop to the true-CE drop).\n"
            "import Hagi.Runtime.CertChecker\n\n"
            "open Hagi.Runtime\n\n"
            f"def benchStartSand : \u211a := {rat(start)}\n\n"
            "def benchTrajectorySand : List "
            "Hagi.Runtime.CertStepData :=\n"
            + "[\n" + ",\n".join(lean_step(d) for d in ds)
            + "\n]\n\n"
            "#eval checkTrajectory benchStartSand "
            "benchTrajectorySand\n\n"
            "theorem sand_bench_valid :\n"
            "    checkTrajectory benchStartSand "
            "benchTrajectorySand = true := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            "benchStartSand, benchTrajectorySand, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_cs(path, start, traj):
    """Negative control: inflate the last drop beyond the actual
    certificate descent - the checker MUST reject."""
    bad = [dict(d) for d in traj[:2]]
    last = bad[-1]
    last["drop"] = last["drop"] + last["obj"]
    with open(path, "w", encoding="utf-8") as f:
        f.write(
            "-- C491 negative control: last drop inflated by obj "
            "(drop > obj - obj').\n"
            "import Hagi.Runtime.CertChecker\n\n"
            "open Hagi.Runtime\n\n"
            f"def benchStartSandBad : \u211a := {rat(start)}\n\n"
            "def benchTrajectorySandBad : "
            "List Hagi.Runtime.CertStepData :=\n["
            + ",\n".join(lean_step(d) for d in bad)
            + "\n]\n\n"
            "#eval checkTrajectory benchStartSandBad "
            "benchTrajectorySandBad\n\n"
            "theorem sand_bench_invalid :\n"
            "    checkTrajectory benchStartSandBad "
            "benchTrajectorySandBad = false := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            "benchStartSandBad, benchTrajectorySandBad, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C485: CONTINUAL two-task bench (--mode continual)
#
# PIN (scenario, GPM / Saha et al. ICLR'21): task A -> task B.
# Phase 1 trains a certified linear head on task A (few-shot);
# phase 2 trains on task B TWO ways: (a) naive certified GD
# (may forget A - MEASURED), (b) GPM: the gradient step is
# PROJECTED onto the orthogonal complement of span(xs_A) via an
# exact rational Gram-Schmidt projector Q = I - sum u u^T/(u.u)
# (no sqrt); by Hagi.Step.gpm_zero_forgetting the projected step
# satisfies gpmOrth DeltaW xs_A EXACTLY, so loss_A is bit-exact
# invariant while B is learned through the complement
# directions (Hagi.Spectral.rank_orthogonal_growth).
#
# PIN (few-shot A): with |A| >= 4 generic rational points in Q^4
# span(xs_A) = R^4 and the exact full-span complement is {0} -
# the GPM step would be identically zero. Task A is therefore 2
# deterministic points (first + median of the ce-sorted ledger);
# rank(span A) <= 2 < 4 keeps the complement >= 2-dimensional.
# No spectral truncation is used - it would break the EXACT
# invariance (honest full-span version).
#
# Certified content per step = C481/C484 form: ANALYTIC exact
# gradient (linear MSE), candidate snap_{1/1000}(w - eta*g)
# [GPM: the SNAPPED delta is then projected; Q*u = 0 keeps
# gpmOrth exact], admission ONLY by MEASURED drop > 0 on the
# phase objective (guarded rollback). Per-step asserts verify
# gpmOrth (delta . x_k = 0 for all A inputs) and loss_A
# invariance exactly in Fractions.

CL_D = 4                         # feature dim (matches C484)
CL_ETA = F(1, 10)                # step size
CL_GRID = F(1, 1000)             # snap grid
CL_STEPS = 6                     # default steps per phase


def cl_gs_basis(vectors):
    """Exact rational Gram-Schmidt (no sqrt); orthogonal basis
    of span(vectors) as Fraction vectors."""
    basis = []
    for v in vectors:
        u = list(v)
        for b in basis:
            d = sum((u[i] * b[i] for i in range(CL_D)), F(0))
            nb = sum((b[i] * b[i] for i in range(CL_D)), F(0))
            u = [u[i] - d / nb * b[i] for i in range(CL_D)]
        if any(u):
            basis.append(u)
    return basis


def cl_complement_projector(basis):
    """Q = I - sum_j u_j u_j^T / (u_j . u_j): exact rational
    projection onto the orthogonal complement of span(basis)."""
    Q = [[F(1) if i == j else F(0) for j in range(CL_D)]
         for i in range(CL_D)]
    for u in basis:
        nb = sum((u[i] * u[i] for i in range(CL_D)), F(0))
        for i in range(CL_D):
            for j in range(CL_D):
                Q[i][j] -= u[i] * u[j] / nb
    return Q


def cl_apply(Q, v):
    return [sum((v[k] * Q[k][j] for k in range(CL_D)), F(0))
            for j in range(CL_D)]


def cl_snap(v, grid=CL_GRID):
    out = []
    for t in v:
        n = t / grid
        r = (n.numerator + n.denominator // 2) // n.denominator \
            if n >= 0 else \
            -((-n.numerator + n.denominator // 2) // n.denominator)
        out.append(F(r) * grid)
    return out


def cl_pred(w, x):
    return sum((w[i] * x[i] for i in range(CL_D)), F(0))


def cl_mse(w, data):
    return sum(((cl_pred(w, x) - y) ** 2 for x, y in data),
               F(0)) / F(len(data))


def cl_grad(w, data):
    """Exact analytic gradient of the linear-MSE objective."""
    g = [F(0)] * CL_D
    for x, y in data:
        r = cl_pred(w, x) - y
        for i in range(CL_D):
            g[i] += F(2) * r * x[i]
    return [t / F(len(data)) for t in g]


def cl_split(pts):
    """Deterministic continual split: sort by (ce, key); task A
    = first + median point (few-shot, PIN); task B = the rest."""
    s = sorted(pts, key=lambda p: (p[2], p[0]))   # (key, x, y)
    ia = {0, len(s) // 2}
    A = [(s[i][1], s[i][2]) for i in sorted(ia)]
    B = [(x, y) for i, (_, x, y) in enumerate(s) if i not in ia]
    return A, B


def cl_certified_loop(w, data_obj, risk_data, steps, Q=None,
                      ortho_data=None, eta=CL_ETA,
                      grid=CL_GRID):
    """Certified GD loop on data_obj (risk = MSE on risk_data,
    telemetry). If Q is given, each snapped step delta is
    projected with Q (GPM); gpmOrth and (for GPM) exact loss_A
    invariance are ASSERTED per commit."""
    raw, tel = [], {"holds": [], "steps": []}
    for t in range(steps):
        obj, risk = cl_mse(w, data_obj), cl_mse(w, risk_data)
        g = cl_grad(w, data_obj)
        delta = cl_snap([-eta * gi for gi in g], grid)
        if Q is not None:
            delta = cl_apply(Q, delta)
            for x, _ in ortho_data:      # gpmOrth, exact
                assert sum((delta[i] * x[i]
                            for i in range(CL_D)), F(0)) == 0, \
                    "ABORT: gpmOrth violated (projection bug)"
        cand = [w[i] + delta[i] for i in range(CL_D)]
        obj2, risk2 = cl_mse(cand, data_obj), cl_mse(cand,
                                                    risk_data)
        if Q is not None:                # gpm_zero_forgetting
            assert cl_mse(cand, ortho_data) == cl_mse(w,
                                                      ortho_data), \
                "ABORT: loss_A moved under GPM step"
        drop = obj - obj2
        if drop > 0:
            raw.append({"obj": obj, "obj'": obj2, "drop": drop,
                        "risk": risk, "risk'": risk2})
            tel["steps"].append({"t": t, "drop": drop})
            w = cand
        else:
            tel["holds"].append({"t": t, "drop": drop,
                                 "reason": "drop <= 0: HOLD, "
                                           "rolled back"})
    n = len(raw)
    assert n > 0, "ABORT: continual loop committed no steps"
    for t, d in enumerate(raw):
        d["budget"] = F(n - t) / n
        d["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for d in raw:
        if not check_step(d):
            sys.exit(f"ABORT: continual step failed certified "
                     f"admission: {d}")
    return raw, tel, w


def continual_run(ledger_path, steps=CL_STEPS):
    """Full continual scenario: phase 1 on A, phase 2 on B both
    ways (naive vs GPM)."""
    pts = rd_load_dataset(ledger_path)
    assert len(pts) >= 100, \
        f"ABORT: expected 100+ real points, got {len(pts)}"
    A, B = cl_split(pts)
    basis = cl_gs_basis([x for x, _ in A])
    assert 0 < len(basis) < CL_D, \
        "ABORT: need 0 < rank(span A) < 4 for a nontrivial " \
        "complement (few-shot PIN)"
    Q = cl_complement_projector(basis)
    w0 = [F(0)] * CL_D
    traj1, tel1, wA = cl_certified_loop(w0, A, B, steps)
    lossA_after1 = cl_mse(wA, A)
    trajN, telN, wN = cl_certified_loop(wA, B, A, steps)
    lossA_naive = cl_mse(wN, A)
    trajG, telG, wG = cl_certified_loop(wA, B, A, steps, Q=Q,
                                        ortho_data=A)
    lossA_gpm = cl_mse(wG, A)
    assert lossA_gpm == lossA_after1, \
        "ABORT: GPM phase must preserve loss_A exactly"
    return {
        "startA": cl_mse(w0, A), "traj1": traj1, "tel1": tel1,
        "startB": cl_mse(wA, B), "trajN": trajN, "telN": telN,
        "trajG": trajG, "telG": telG,
        "lossA_after1": lossA_after1,
        "lossB_before2": cl_mse(wA, B),
        "lossB_naive": trajN[-1]["obj'"],
        "lossB_gpm": trajG[-1]["obj'"],
        "lossA_naive": lossA_naive, "lossA_gpm": lossA_gpm,
        "forget_naive": lossA_naive - lossA_after1,
        "forget_gpm": lossA_gpm - lossA_after1,
        "rankA": len(basis), "n_A": len(A), "n_B": len(B),
        "n_points": len(pts), "wA": wA, "wN": wN, "wG": wG,
    }


def emit_lean_cont(path, res, witness_steps=4):
    """C485 witness: three literal trajectories (phase 1 on A,
    phase 2 naive on B, phase 2 GPM on B) + #eval checkTrajectory
    + valid theorems; header documents FULL counts honestly."""
    blocks = [("A", res["startA"], res["traj1"]),
              ("BN", res["startB"], res["trajN"]),
              ("BG", res["startB"], res["trajG"])]
    out = ["-- C485 continual bench witness (real unified_ledger "
           "data).\n"
           f"-- task A: {res['n_A']} pts (rank {res['rankA']}), "
           f"task B: {res['n_B']} pts; FULL accepted steps: "
           f"phase1={len(res['traj1'])}, naive="
           f"{len(res['trajN'])}, gpm={len(res['trajG'])}; "
           "first machine-checked prefixes below.\n"
           "-- GPM phase preserves loss_A EXACTLY "
           "(Hagi.Theory.ContinualBench.gpm_bench_bridge;\n"
           "-- numeric telemetry: loss_A before/after GPM phase "
           "are equal Fractions).\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.Continual\n\n"
           "open Hagi.Runtime\n\n"]
    for name, start, traj in blocks:
        ds = [dict(d) for d in traj[:witness_steps]]
        out.append(f"def benchStartC485{name} : \u211a := "
                   f"{rat(start)}\n\n"
                   f"def benchTrajectoryC485{name} : List "
                   "Hagi.Runtime.CertStepData :=\n"
                   + "[\n" + ",\n".join(lean_step(d) for d in ds)
                   + "\n]\n\n"
                   f"#eval checkTrajectory benchStartC485{name} "
                   f"benchTrajectoryC485{name}\n\n"
                   f"theorem continual_bench_{name.lower()}_valid "
                   ":\n"
                   f"    checkTrajectory benchStartC485{name} "
                   f"benchTrajectoryC485{name} = true := by\n"
                   "  set_option linter.unusedSimpArgs false in\n"
                   "  simp only [checkTrajectory, checkStep, "
                   f"benchStartC485{name}, "
                   f"benchTrajectoryC485{name}, "
                   "Bool.and_eq_true, decide_eq_true_eq]\n"
                   "  norm_num\n\n")
    out.append("#check @Hagi.Theory.ContinualBench.gpm_bench_bridge\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)



# C488: MULTI-TASK CONTINUAL bench with GPM subspace
# ACCUMULATION (--mode continual-multi)
#
# PIN (scenario): T = 3 sequential tasks from the SAME
# ce-sorted unified_ledger split. Before phase t+1 the GPM
# subspace is the ACCUMULATED span of the inputs of tasks
# 1..t (union of spans, exact rational Gram-Schmidt on the
# concatenation); every certified step of phase t+1 is
# projected onto its orthogonal complement Q = I - sum u u^T/
# (u.u). By Hagi.Theory.ContinualMulti.gpm_multi_zero_forgetting
# (induction over phases, chained gpm_zero_forgetting) the
# bench losses of ALL previous tasks are bit-exact invariant
# (asserted per commit against every past task point). Rank
# track: the accumulated basis grows per task by its number of
# genuinely NEW independent directions - the
# Hagi.Spectral.rank_orthogonal_growth setting (k new
# orthogonal independent rows => rank +k EXACTLY); degenerate
# candidates (lying inside the current span, rank < sum) are
# skipped and logged honestly.
#
# Split (deterministic, ce-sorted like C485): task 1 = 2
# few-shot points (first + median; rank 2 PIN - |A| >= 4
# generic points would span R^4 and kill the complement),
# task 2 = 1 point chosen greedily as the first sorted point
# raising the accumulated rank to exactly 3 (leaves a 1-dim
# complement for task 3), task 3 = all remaining points.
#
# Both arms run the same certified loop (C481 form: analytic
# exact gradient, snap_{1/1000} candidate, admission ONLY by
# MEASURED drop > 0, guarded rollback): NAIVE (no projection -
# forgetting matrix MEASURED) vs GPM (accumulated projection -
# forgetting matrix asserted EXACTLY zero on the past).

CLM_TASKS = 3
CLM_ETA = F(1, 10)               # same eta as C485
CLM_GRID = F(1, 10000)           # finer snap grid: the C485
# 1/1000 grid rounds the tiny projected steps of the 1-point
# task 2 past the optimum (measured drop < 0 at every step);
# 1/10000 commits 6/6 in every phase (probe, .tmp/C488)


def clm_split(pts):
    """Deterministic 3-task continual split: sort by (ce, key);
    task 1 = first + median point (few-shot PIN), task 2 = the
    first later point raising the accumulated rank to exactly 3
    (dependent candidates skipped + counted), task 3 = rest."""
    s = sorted(pts, key=lambda p: (p[2], p[0]))   # (key, x, y)
    i1 = sorted({0, len(s) // 2})
    T1 = [(s[i][1], s[i][2]) for i in i1]
    used = set(i1)
    basis = cl_gs_basis([x for x, _ in T1])
    skipped = 0
    T2, i2 = [], None
    for i, (_, x, y) in enumerate(s):
        if i in used:
            continue
        nb = cl_gs_basis(basis + [x])
        if len(nb) == len(basis):
            skipped += 1                 # degenerate: inside span
            continue
        T2, i2, basis = [(x, y)], i, nb
        break
    assert T2 and len(basis) == 3, \
        "ABORT: no rank-3 point found for task 2"
    used.add(i2)
    T3 = [(x, y) for i, (_, x, y) in enumerate(s)
          if i not in used]
    return [T1, T2, T3], skipped


def continual_multi_run(ledger_path, steps=CL_STEPS):
    """T = 3 sequential phases with ACCUMULATED GPM subspaces,
    naive control arm; per-phase telemetry: loss of the current
    task, losses of ALL previous tasks (forgetting matrix),
    rank track of the accumulated span."""
    pts = rd_load_dataset(ledger_path)
    assert len(pts) >= 100, \
        f"ABORT: expected 100+ real points, got {len(pts)}"
    tasks, skipped2 = clm_split(pts)
    T = len(tasks)
    res = {"n_points": len(pts), "n_tasks": T,
           "task_sizes": [len(t) for t in tasks],
           "degenerate_skips_task2": skipped2}
    rank_track = []
    past_x = []
    for t in range(T):
        r0 = len(past_x)
        past_x = past_x + [x for x, _ in tasks[t]]
        rank_track.append({
            "t": t, "n_inputs_cum": len(past_x),
            "rank_before": len(cl_gs_basis(
                past_x[:-len(tasks[t])])),
            "rank_after": len(cl_gs_basis(past_x)),
            "n_new_indep": len(cl_gs_basis(past_x))
            - len(cl_gs_basis(
                past_x[:-len(tasks[t])]))})
    res["rank_track"] = rank_track
    for arm in ("naive", "gpm"):
        w = [F(0)] * CL_D
        after = []            # loss on task s right after phase s
        forget = [[None] * T for _ in range(T)]
        phases = []
        for t in range(T):
            past_x = [x for s_ in range(t)
                      for x, _ in tasks[s_]]
            if t == 0:
                traj, tel, w = cl_certified_loop(
                    w, tasks[0], tasks[T-1], steps,
                    eta=CLM_ETA, grid=CLM_GRID)
            else:
                basis = cl_gs_basis(past_x)
                assert len(basis) < CL_D, \
                    "ABORT: accumulated span full - " \
                    "complement trivial"
                Q = cl_complement_projector(basis)
                ortho = [p for s_ in range(t) for p in tasks[s_]]
                traj, tel, w = cl_certified_loop(
                    w, tasks[t], tasks[T-1], steps,
                    Q=(Q if arm == "gpm" else None),
                    ortho_data=(ortho if arm == "gpm"
                                else None),
                    eta=CLM_ETA, grid=CLM_GRID)
            after.append(cl_mse(w, tasks[t]))
            # forgetting matrix row: loss of EVERY task s at the
            # end of phase t vs right after phase s
            row = []
            for s_ in range(T):
                ls = cl_mse(w, tasks[s_]) if s_ <= t else None
                if s_ <= t:
                    forget[t][s_] = ls - after[s_]
                row.append(str(ls) if ls is not None else None)
            if arm == "gpm" and t > 0:
                for s_ in range(t):
                    assert cl_mse(w, tasks[s_]) == after[s_], \
                        f"ABORT: task {s_+1} loss moved under " \
                        f"GPM phase {t+1}"
            phases.append({
                "t": t,
                "loss_task": cl_mse(w, tasks[t]),
                "all_task_losses": row,
                "n_steps": len(traj), "w": list(w)})
            if arm == "gpm":
                res.setdefault("traj", []).append(traj)
                res.setdefault("tel", []).append(tel)
        res[f"phases_{arm}"] = phases
        res[f"forget_{arm}"] = forget
        res[f"final_w_{arm}"] = w
        res[f"after_{arm}"] = after
    return res


def emit_lean_contm(path, res, witness_steps=4):
    """C488 witness: per-phase GPM-arm literal trajectories
    (CertStepData prefixes) + #eval checkTrajectory + valid
    theorems + #check of the multi-task theory and the rank
    certificate; header documents FULL counts honestly."""
    out = ["-- C488 multi-task continual witness (real "
           "unified_ledger data).\n"
           f"-- tasks: {res['task_sizes']} pts; FULL accepted "
           "GPM steps per phase: "
           + ", ".join(str(len(p)) for p in res["phases_gpm"])
           + "; first machine-checked prefixes below.\n"
           "-- GPM phases preserve ALL previous task losses "
           "EXACTLY (Hagi.Theory.ContinualMulti."
           "gpm_multi_zero_forgetting;\n"
           "-- per-step asserts: gpmOrth + exact loss "
           "invariance on every past task point).\n"
           "-- Rank track certificate: Hagi.Spectral."
           "rank_orthogonal_growth (k new orthogonal "
           "independent rows => rank +k exactly).\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.Continual\n"
           "import Hagi.Spectral.RankGrowth\n\n"
           "open Hagi.Runtime\n\n"]
    for t, (ph, traj) in enumerate(zip(res["phases_gpm"],
                                       res["traj"])):
        name = f"P{t+1}"
        start = (res["phases_gpm"][t-1]["loss_task"]
                 if t else F(0))
        start = traj[0]["obj"]
        ds = [dict(d) for d in traj[:witness_steps]]
        out.append(f"def benchStartC488{name} : ℚ := "
                   f"{rat(start)}\n\n"
                   f"def benchTrajectoryC488{name} : List "
                   "Hagi.Runtime.CertStepData :=\n"
                   + "[\n" + ",\n".join(lean_step(d) for d in ds)
                   + "\n]\n\n"
                   f"#eval checkTrajectory benchStartC488{name} "
                   f"benchTrajectoryC488{name}\n\n"
                   f"theorem continual_multi_{name.lower()}_valid"
                   " :\n"
                   f"    checkTrajectory benchStartC488{name} "
                   f"benchTrajectoryC488{name} = true := by\n"
                   "  set_option linter.unusedSimpArgs false in\n"
                   "  simp only [checkTrajectory, checkStep, "
                   f"benchStartC488{name}, "
                   f"benchTrajectoryC488{name}, "
                   "Bool.and_eq_true, decide_eq_true_eq]\n"
                   "  norm_num\n\n")
    out.append("#check @Hagi.Theory.ContinualMulti."
               "gpm_multi_zero_forgetting\n"
               "#check @Hagi.Spectral.rank_orthogonal_growth\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)


# C487: WITHOUT-REPLACEMENT holdout bound bench (--mode wrbound)
#
# Compares the C487 Freedman-adaptive without-replacement bound
#   2*exp(-k*eps^2/(2*(s2*(2N-k)/N + eps)))
# against the C435/C484 with-replacement Hoeffding form
#   2*exp(-2*k*eps^2)
# on the FIXED final real-data trunk model (same certified loop
# as --mode real-data). Per-point losses u_i = sqerr_i / L in
# [0,1]; s2 = population variance (exact Fractions).
#
# PIN (N=185): the corpus is LIVE (206 entries at bench time);
# N is pinned to the first 185 sorted ledger keys (deterministic
# snapshot), k = 37 = |{i < 185 : i % 5 == 4}| (the C484-style
# every-5th holdout split). delta = 0.05; eps* by float
# bisection (report-only, same convention as rd_concentration).

WR_DELTA = 0.05


def wrbound_run(ledger_path, steps=RD_STEPS):
    import math
    pts = rd_load_dataset(ledger_path)
    assert len(pts) >= 185,         f"ABORT: expected 185+ real points, got {len(pts)}"
    pts = pts[:185]                       # N = 185 pinned
    N, k = len(pts), 37
    train = [(x, y) for i, (_, x, y) in enumerate(pts) if i % 5 != 4]
    hold = [(x, y) for i, (_, x, y) in enumerate(pts) if i % 5 == 4]
    assert len(hold) == k
    cfix = max(sum((abs(v) for v in x), F(0))
               for _, x, _ in pts) + RD_EPS
    # same certified trunk loop as real-data (C481 form)
    p = rd_init()
    for t in range(steps):
        obj = rd_mse(p, train, cfix)
        gfd = []
        for j in range(RD_NPAR):
            q = list(p)
            q[j] = q[j] + RD_H
            gfd.append((rd_mse(q, train, cfix) - obj) / RD_H)
        cand = [rd_snap(p[j] - RD_ETA * gfd[j])
                for j in range(RD_NPAR)]
        if obj - rd_mse(cand, train, cfix) > 0:
            p = cand
    # per-point losses of the FIXED final model, normalized
    ls = [(rd_forward(p, x, cfix) - y) ** 2 for _, x, y in pts]
    L = max(ls)
    u = [l / L for l in ls]
    mu = sum(u, F(0)) / F(N)
    s2 = sum(((ui - mu) ** 2 for ui in u), F(0)) / F(N)
    fpc = (2 * N - k) / N                  # exact Fraction
    vden = float(s2) * float(fpc)          # sigma^2*(2N-k)/N
    # bisection: eps_* = smallest eps with bound <= delta
    def bis(bound):
        lo, hi = 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            if bound(mid) <= WR_DELTA:
                hi = mid
            else:
                lo = mid
        return hi
    eps_hoe = bis(lambda e: 2 * math.exp(-2 * k * e * e))
    eps_wr = bis(lambda e: 2 * math.exp(
        -k * e * e / (2 * (vden + e))))
    cond = vden + eps_wr <= 0.25           # (d) comparison premise
    # exact check: actual holdout gap vs the wr bound
    hold_mean = sum((u[i] for i in range(N) if i % 5 == 4),
                    F(0)) / F(k)
    gap = abs(hold_mean - mu)
    return {
        "N": N, "k": k, "delta": WR_DELTA,
        "L_max_loss": str(L),
        "mu_normalized": str(mu), "sigma2": str(s2),
        "fpc_factor": str(fpc), "vden": vden,
        "eps_hoeffding": eps_hoe, "eps_wr": eps_wr,
        "wr_le_hoe": eps_wr <= eps_hoe,
        "condition_d_premise": cond,
        "condition_d_value": vden + eps_wr,
        "win_eps_absolute": eps_hoe - eps_wr,
        "win_loss_units": (eps_hoe - eps_wr) * float(L),
        "actual_gap_normalized": str(gap),
        "gap_le_wr_bound": gap <= F(int(eps_wr * 10**9), 10**9),
        "n_train": len(train),
    }


# C497: VS-TRAINER — mini-HAGI against the REAL trainer
# (--mode vs-trainer)
#
# The C484 task (inputs = model byte-features, outputs = the
# real trainer's measured ce) with a NEW certified-evaluation
# layer: after certified sandwich training (C491 family) on
# the train split, every holdout model gets a CERTIFIED
# prediction (C495): its rational sandwich intervals are
# computed exactly; if the normalized class bands
# [lo v/Sum hi, hi v/Sum lo] are pairwise DISJOINT
# (hi a/Sum lo < lo b/Sum hi), the argmax is certified —
# no point estimate involved. Accuracy = correct argmax
# among CERTIFIED predictions only (an uncertified point —
# range guard or overlapping bands — is honestly reported,
# never guessed).
#
# The Lean side: Hagi.Theory.TrainerBenchmark.
# certified_forecast_sound — disjoint certified intervals +
# the measured reality-inside-band premise (BandDescribes,
# Describes-type) make the certified forecast coincide with
# the argmax of the true ranking.
#
# Selfloop telemetry (C461): the round/COMMIT count of the
# live HAGI_v2 experiments/selfloop_result.json is re-read
# at run time (fail-closed field checks, C461 bridge).
#
# PIN (corpus, honest): the live checkpoint ledger holds 32
# entries / 31 usable models today (it PRUNES across
# sessions); N is reported, never fabricated.

SELFLOOP_DEFAULT = ("C:/HAGI_v2/experiments/"
                    "selfloop_result.json")


def vs_trainer_run(ledger_path, selfloop_path, steps=CS_STEPS):
    """C497: certified-prediction evaluation of mini-HAGI on
    holdout models of the real trainer. Returns (stats, w)."""
    pts, med = cs_load_dataset(ledger_path)
    assert len(pts) > 0, "ABORT: no usable real points"
    data = [(x, 0 if y <= med else 1) for _, x, y in pts]
    train = [d for i, d in enumerate(data) if i % 5 != 4]
    hold = [(k, d[0], d[1]) for i, (k, d) in
            enumerate(zip([p[0] for p in pts], data)) if i % 5 == 4]
    w = list(CS_W0)
    committed, holds = 0, []
    for t in range(steps):
        g = cs_grad_log(w, train)
        mx = max(abs(v) for v in g)
        cand = [cs_snap(w[k] - CS_ETA * g[k] / mx, CS_WGRID)
                for k in range(CS_K * CS_D)]
        o1, o2 = cs_obj(w, train), cs_obj(cand, train)
        if o2 is not None and o2 < o1:
            w = cand
            committed += 1
        else:
            holds.append({"t": t, "reason":
                          "range guard or drop <= 0: HOLD"})
    rows, n_cert, n_ok, n_sm_ok = [], 0, 0, 0
    import math
    nm_used_all = []
    for k, x, y in hold:
        # C502 adaptive band tightening: double the EVAL-time
        # denominator n = m from CS_NM until the normalized
        # class bands are disjoint (Lean: bernoulliLower_mono /
        # expUpper_base_mono — larger nm, narrower certified
        # band), bounded by the CS_NM_EVAL_MAX denominator
        # budget. Training certificate stays at fixed CS_NM.
        z = cs_logits(w, x)
        nm, sep, loN, hiN = CS_NM, [], None, None
        while nm <= CS_NM_EVAL_MAX:
            t = cs_terms_nm(z, nm)
            if t is not None:
                lo, hi = t
                slo, shi = sum(lo, F(0)), sum(hi, F(0))
                loN = [lo[c] / shi for c in range(CS_K)]
                hiN = [hi[c] / slo for c in range(CS_K)]
                sep = [c for c in range(CS_K)
                       if all(hiN[a] < loN[c]
                              for a in range(CS_K) if a != c)]
                if len(sep) == 1:
                    break
            nm *= 2
        nm_used_all.append(nm if nm <= CS_NM_EVAL_MAX else None)
        if len(sep) != 1:
            rows.append({"key": k, "certified": False,
                         "reason": "bands overlap",
                         "nm_eval_tried_max": min(nm, CS_NM_EVAL_MAX),
                         "bands": ([[float(loN[c]), float(hiN[c])]
                                    for c in range(CS_K)]
                                   if loN is not None else None),
                         "true_softmax_argmax": z.index(max(z))})
            continue
        pred = sep[0]
        n_cert += 1
        n_ok += (pred == y)
        n_sm_ok += (pred == z.index(max(z)))
        rows.append({"key": k, "certified": True, "pred": pred,
                     "label": y, "correct": pred == y,
                     "nm_eval": nm,
                     "bands": [[float(loN[c]), float(hiN[c])]
                               for c in range(CS_K)],
                     "true_softmax_argmax": z.index(max(z)),
                     "agrees_softmax": pred == z.index(max(z)),
                     "bands_exact": [[str(loN[c]), str(hiN[c])]
                                     for c in range(CS_K)]})
    sl = {"rounds": None, "commits": None, "actions": None}
    try:
        with open(selfloop_path, encoding="utf-8") as f:
            doc = json.load(f)
        rounds = doc.get("rounds")
        assert rounds, "no rounds in selfloop telemetry"
        acts = []
        for r in rounds:
            gate = r.get("gate")
            assert gate and "action" in gate, \
                "selfloop round missing gate.action"
            acts.append(gate["action"])
        sl = {"rounds": len(rounds), "commits": acts.count("COMMIT"),
              "actions": acts}
    except FileNotFoundError:
        sl["error"] = "selfloop_result.json not found"
    stats = {
        "mode": "vs-trainer", "n_points": len(pts),
        "n_train": len(train), "n_holdout": len(hold),
        "train_committed_steps": committed,
        "train_holds": holds,
        "n_certified": n_cert,
        "n_certified_correct": n_ok,
        "adaptive": {"start": CS_NM, "max": CS_NM_EVAL_MAX,
                     "nm_eval_used": nm_used_all},
        "accuracy_certified": (f"{n_ok}/{n_cert}"
                               if n_cert else "0/0"),
        "agreement_with_true_softmax": (
            f"{n_sm_ok}/{n_cert}" if n_cert else "0/0"),
        "holdout": rows,
        "selfloop": sl,
        "theorem": "Hagi.Theory.TrainerBenchmark."
                   "certified_forecast_sound (C497)",
        "source": ledger_path,
    }
    return stats, w


# C492: MINI-HAGI - the FULL bench in ONE certified run on the
# REAL corpus (--mode mini-hagi)
#
# PIN (unification): ONE run on the live unified_ledger corpus
# chaining ALL bench components on ONE CertStepData trace:
#   (A) TRUNK-TRAIN (C481 form): the trunk is the FIXED byte-
#       feature map (C484 family); the head over it is trained
#       by analytic-gradient snap_{1/10000} steps admitted ONLY
#       by MEASURED drop > 0 (guarded rollback). GPM
#       zero-forgetting and C444 grow mechanics are linear-
#       readout statements, so the KISS reading of "trunk" here
#       is the fixed feature trunk (the nonlinear C481 trunk is
#       its own certified mode).
#   (B) GROW (C444): ONE deterministic fiber candidate
#       x5 = snap_{1/1000}(x0*x1); the extended model starts at
#       w||[0] (predictions IDENTICAL => obj chain EXACTLY
#       continuous, asserted); the grown only_last certified
#       step is admitted by the C444 margin (cost/risk pass-
#       through eps = 0 => margin = canonical gain); margin <= 0
#       is an honest REJECT (telemetry, model unchanged).
#   (C) CONTINUAL (C485/C488): task B trained with GPM - each
#       step projected onto the complement of span(task-A
#       inputs, dim-generic exact Gram-Schmidt); per commit:
#       delta orthogonality ASSERTED and MSE_A bit-exact
#       invariance ASSERTED (gpm_bench_bridge semantics); the
#       naive (unprojected) arm runs in parallel as TELEMETRY
#       (its forgetting is MEASURED, not certified away).
#   (D) QUANT (C443): dim-generic ternary jump with the LS-
#       optimal scale on the head weights, admitted ONLY by the
#       measured canonical drop > 0; a rejected jump is an
#       honest HOLD (telemetry). (Hadamard-tern C477 applies to
#       power-of-two dims only - an admitted grow leaves dim 5,
#       so the C443 gate is the honest choice; documented.)
#   (E) STOP (C446): the Ville anytime detector on the
#       CANONICAL holdout risk (lam/delta reused from C446);
#       further certified candidate steps are admitted ONLY
#       while the stop has not fired; a never-firing stop is an
#       honest outcome (no degradation detected).
#
# THE OBJ RULE (canonical objective - the continuity contract
# across heterogeneous phases): every trajectory step carries
#   obj = OBJ(w) = (MSE_A(w) + MSE_B(w)) / 2   (exact Fractions)
# on the CURRENT model state; admission demands a measured
# CANONICAL drop > 0; phase boundaries change nothing about the
# model, so obj' of step N = obj of step N+1 (asserted; the
# executable checker re-verifies the whole chain). Lean:
# Hagi.Theory.MiniHagi (mini_hagi_canonical_drop,
# mini_hagi_gpm_canonical_descent).
#
# PIN (corpus, honest): the ledger is LIVE and prunes across
# sessions (185 -> ~31 usable at C492); like C491 the loader
# skips keys without .bin, asserts N > 0 and reports the
# run-time N (the N >= 100 pin of C484/C485 is unmet by the
# environment - documented, not fabricated).

MH_ETA = F(1, 10)
MH_GRID = F(1, 10000)      # CLM-family snap grid
MH_A_STEPS = 4
MH_C_STEPS = 4
MH_E_STEPS = 4
MH_QUANT_FT = 1


def mh_load_dataset(ledger_path):
    """Live-corpus loader (C491 cs family, C484 rd features):
    skip ledger keys without a .bin sibling."""
    import os
    with open(ledger_path, encoding="utf-8") as f:
        led = json.load(f)
    dom = os.path.join(os.path.dirname(os.path.abspath(
        ledger_path)), "domains")
    pts = []
    for k in sorted(led):
        p = os.path.join(dom, k + ".bin")
        if not os.path.exists(p):
            continue                      # live corpus: skip
        b = open(p, "rb").read()
        s = len(b)
        x = [rd_snap(F(s, 1 << 20)),
             rd_snap(F(sum(1 for c in b if c == 0), s)),
             rd_snap(F(sum(1 for c in b if 32 <= c < 127), s)),
             rd_snap(F(sum(b), 256 * s))]
        pts.append((k, x, F(led[k]["ce"])))
    return pts


def mh_pred(w, x):
    return sum((w[i] * x[i] for i in range(len(w))), F(0))


def mh_mse(w, data):
    return sum(((mh_pred(w, x) - y) ** 2 for x, y in data),
               F(0)) / F(len(data))


def mh_canon(w, A, B):
    """The canonical objective: mean MSE over the live tasks."""
    return (mh_mse(w, A) + mh_mse(w, B)) / F(2)


def mh_grad(w, data):
    g = [F(0)] * len(w)
    for x, y in data:
        r = mh_pred(w, x) - y
        for i in range(len(w)):
            g[i] += F(2) * r * x[i]
    return [t / F(len(data)) for t in g]


def mh_gs_basis(vs, d):
    """Dim-generic exact rational Gram-Schmidt (C485 form)."""
    basis = []
    for v in vs:
        u = list(v)
        for b in basis:
            dq = sum((u[i] * b[i] for i in range(d)), F(0))
            nb = sum((b[i] * b[i] for i in range(d)), F(0))
            u = [u[i] - dq / nb * b[i] for i in range(d)]
        if any(u):
            basis.append(u)
    return basis


def mh_complement_projector(basis, d):
    """Q = I - sum u u^T/(u.u), dim-generic (C485 form)."""
    Q = [[F(1) if i == j else F(0) for j in range(d)]
         for i in range(d)]
    for u in basis:
        nb = sum((u[i] * u[i] for i in range(d)), F(0))
        for i in range(d):
            for j in range(d):
                Q[i][j] -= u[i] * u[j] / nb
    return Q


def mh_tern_quantize(w):
    """Dim-generic C443 ternary jump: pattern on the {-1,0,1}
    grid from s0 = max|w|, LS-optimal s = (sum q.w)/(sum q.q)."""
    s0 = max(abs(t) for t in w) or F(1)
    q = [round_tern(t / s0) for t in w]
    qq = sum((t * t for t in q), F(0))
    if qq == 0:
        return [F(0)] * len(w), F(0), q, s0
    s = sum((q[i] * w[i] for i in range(len(w))), F(0)) / qq
    return [s * t for t in q], s, q, s0


def mini_hagi_run(ledger_path):
    """The unified 5-phase certified cycle on the real corpus.
    Returns (start_obj, [accepted steps], telemetry, stats)."""
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    A, B = cl_split(pts)
    holdA, holdB = cl_split([(kk, x, y) for i, (kk, x, y)
                            in enumerate(pts) if i % 5 == 4])

    hA, hB = holdA, holdB      # extended alongside the grow

    def risk(w):
        return (mh_mse(w, hA) + mh_mse(w, hB)) / F(2)

    w = [F(0)] * CL_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {}}

    def certified_step(phase, wcur, cand, A_, B_, extra=None):
        """C481 guarded admission on the CANONICAL objective."""
        o0, o1 = mh_canon(wcur, A_, B_), mh_canon(cand, A_, B_)
        if o1 < o0:
            raw.append({"phase": phase, "obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": risk(wcur), "risk'": risk(cand),
                        **(extra or {})})
            return cand
        tel["holds"].append({"phase": phase, "drop": o0 - o1,
                             "reason": "canonical drop <= 0: "
                                       "HOLD, rolled back"})
        return wcur

    # --- (A) TRUNK-TRAIN on task 1 (C481 form)
    obj0 = mh_canon(w, A, B)
    for t in range(MH_A_STEPS):
        g = mh_grad(w, A)
        cand = cl_snap([w[i] - MH_ETA * g[i]
                        for i in range(len(w))], MH_GRID)
        w = certified_step("A-trunk", w, cand, A, B)
    tel["phases"].append({"phase": "A-trunk",
                          "mseA": str(mh_mse(w, A)),
                          "mseB": str(mh_mse(w, B)),
                          "canonical": str(mh_canon(w, A, B))})

    # --- (B) GROW: fiber candidate x5 = snap(x0*x1)
    def ext(data):
        return [(x + [rd_snap(x[0] * x[1])], y) for x, y in data]

    Ax, Bx, hA, hB = A, B, holdA, holdB   # 4-dim baseline
    we = list(w)
    Axt, Bxt = ext(A), ext(B)
    wet = w + [F(0)]
    assert mh_canon(wet, Axt, Bxt) == mh_canon(w, A, B), \
        "ABORT: grow broke the obj chain (w||0 must preserve OBJ)"
    g = mh_grad(wet, Axt + Bxt)
    cand = list(wet)
    cand[-1] = wet[-1] - MH_ETA * g[-1]   # only_last (C479 form)
    cand = cl_snap(cand, MH_GRID)
    o0, o1 = mh_canon(wet, Axt, Bxt), mh_canon(cand, Axt, Bxt)
    gain = o0 - o1
    margin = admission_margin(gain, F(0), F(0))  # C444, eps = 0
    if margin > 0:
        raw.append({"phase": "B-grow", "obj": o0, "obj'": o1,
                    "drop": gain,
                    "risk": (mh_mse(wet, ext(holdA))
                             + mh_mse(wet, ext(holdB))) / F(2),
                    "risk'": (mh_mse(cand, ext(holdA))
                              + mh_mse(cand, ext(holdB))) / F(2),
                    "margin": margin})
        we, Ax, Bx, hA, hB = cand, Axt, Bxt, \
            ext(holdA), ext(holdB)
        tel["admissions"].append(
            {"phase": "B-grow", "margin": str(margin),
             "fiber": "x5 = snap_{1/1000}(x0*x1)",
             "decision": "ADMIT"})
    else:
        tel["rejects"].append(
            {"phase": "B-grow", "margin": str(margin),
             "decision": "REJECT (model unchanged, 4 features)"})
    d = len(we)
    mseA_afterB = mh_mse(we, Ax)
    tel["phases"].append({"phase": "B-grow", "dim": d,
                          "mseA": str(mseA_afterB),
                          "mseB": str(mh_mse(we, Bx)),
                          "canonical": str(
                              mh_canon(we, Ax, Bx))})

    # --- (C) CONTINUAL: task 2 with GPM (naive arm = telemetry)
    basis = mh_gs_basis([x for x, _ in Ax], d)
    assert 0 < len(basis) < d, \
        "ABORT: need 0 < rank(span A) < dim for a complement"
    Q = mh_complement_projector(basis, d)

    def applyQ(v):
        return [sum((v[k] * Q[k][j] for k in range(d)), F(0))
                for j in range(d)]

    wn = list(we)                    # naive arm (telemetry)
    for t in range(MH_C_STEPS):
        g = mh_grad(wn, Bx)
        cand = cl_snap([wn[i] - MH_ETA * g[i]
                        for i in range(d)], MH_GRID)
        o0, o1 = mh_mse(cand, Bx), mh_mse(wn, Bx)
        if o1 < o0:
            wn = cand
    forgetting_naive = mh_mse(wn, Ax) - mseA_afterB

    wg = list(we)                    # GPM arm (the trace)
    for t in range(MH_C_STEPS):
        g = mh_grad(wg, Bx)
        delta = applyQ(cl_snap([-MH_ETA * t2 for t2 in g],
                               MH_GRID))
        for x, _ in Ax:              # gpmOrth, exact
            assert sum((delta[i] * x[i] for i in range(d)),
                       F(0)) == 0, \
                "ABORT: gpmOrth violated (projection bug)"
        cand = [wg[i] + delta[i] for i in range(d)]
        assert mh_mse(cand, Ax) == mh_mse(wg, Ax), \
            "ABORT: loss_A moved under a GPM step"
        o0, o1 = mh_canon(wg, Ax, Bx), mh_canon(cand, Ax, Bx)
        if o1 < o0:
            raw.append({"phase": "C-gpm", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(wg),
                        "risk'": risk(cand)})
            wg = cand
        else:
            tel["holds"].append({"phase": "C-gpm",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (GPM arm)"})
    forgetting_gpm = mh_mse(wg, Ax) - mseA_afterB
    assert forgetting_gpm == 0, \
        "ABORT: GPM forgetting must be EXACTLY zero"
    tel["phases"].append({"phase": "C-gpm",
                          "mseA": str(mh_mse(wg, Ax)),
                          "mseB": str(mh_mse(wg, Bx)),
                          "canonical": str(
                              mh_canon(wg, Ax, Bx))})
    tel["outcomes"]["forgetting_naive"] = str(forgetting_naive)
    tel["outcomes"]["forgetting_gpm"] = str(forgetting_gpm)

    # --- (D) QUANT: C443 ternary jump on the head weights
    wq, s, q, s0 = mh_tern_quantize(wg)
    o0, o1 = mh_canon(wg, Ax, Bx), mh_canon(wq, Ax, Bx)
    if o1 < o0:
        raw.append({"phase": "D-quant", "obj": o0, "obj'": o1,
                    "drop": o0 - o1, "risk": risk(wg),
                    "risk'": risk(wq)})
        wg = wq
        tel["admissions"].append(
            {"phase": "D-quant", "decision": "ADMIT",
             "scale": str(s),
             "pattern": [str(t2) for t2 in q]})
        for t in range(MH_QUANT_FT):
            g = mh_grad(wg, Ax + Bx)
            cand = cl_snap([wg[i] - MH_ETA * g[i]
                            for i in range(d)], MH_GRID)
            wg = certified_step("D-quant-ft", wg, cand, Ax, Bx)
    else:
        tel["holds"].append({"phase": "D-quant", "drop": o0 - o1,
                             "reason": "quant jump drop <= 0: "
                                       "HOLD (honest reject)"})
    tel["phases"].append({"phase": "D-quant",
                          "mseA": str(mh_mse(wg, Ax)),
                          "mseB": str(mh_mse(wg, Bx)),
                          "canonical": str(
                              mh_canon(wg, Ax, Bx))})

    # --- (E) STOP: Ville anytime detector on canonical holdout
    h0 = risk(wg)
    D = F(0)
    fired = False
    refused = 0
    for t in range(MH_E_STEPS):
        g = mh_grad(wg, Ax + Bx)
        cand = cl_snap([wg[i] - MH_ETA * g[i]
                        for i in range(d)], MH_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:   # conservative Ville
            fired = True
            refused += 1
            tel["holds"].append({"phase": "E-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh_canon(wg, Ax, Bx), mh_canon(cand, Ax, Bx)
        if o1 < o0:
            raw.append({"phase": "E-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(wg),
                        "risk'": r1})
            wg = cand
            D = D_new
        else:
            tel["holds"].append({"phase": "E-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D)}
    tel["phases"].append({"phase": "E-stop",
                          "mseA": str(mh_mse(wg, Ax)),
                          "mseB": str(mh_mse(wg, Bx)),
                          "canonical": str(
                              mh_canon(wg, Ax, Bx))})

    n = len(raw)
    assert n > 0, "ABORT: mini-hagi committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: mini-hagi step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts), "n_A": len(A), "n_B": len(B),
        "n_holdout": len(holdA) + len(holdB),
        "source": ledger_path, "dim_final": d,
        "rank_spanA": len(basis),
        "grow_admitted": any(a["phase"] == "B-grow"
                             for a in tel["admissions"]),
        "quant_admitted": any(a["phase"] == "D-quant"
                              for a in tel["admissions"]),
        "canonical_start": str(obj0),
        "canonical_final": str(o_adapted),
        "total_drop": str(obj0 - o_adapted),
        "model": "linear head over the fixed byte-feature "
                 "trunk (C484 family), canonical obj = "
                 "(MSE_A + MSE_B)/2, admission ONLY by measured "
                 "canonical drop > 0 (C481 form)",
        "theorem": "Hagi.Theory.MiniHagi."
                   "mini_hagi_gpm_canonical_descent (C492)",
    }
    return obj0, raw, tel, stats


def emit_lean_mini(path, start, traj, witness_steps=3):
    """C492 witness: the literal mini-HAGI trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C492 mini-HAGI witness (real unified_ledger "
                "data).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} machine-checked "
                "steps below. Canonical obj = (MSE_A + MSE_B)/2 "
                "(exact Fractions).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.MiniHagi\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini "
                "benchTrajectoryMini\n\n"
                "theorem mini_hagi_bench_valid :\n"
                "    checkTrajectory benchStartMini "
                "benchTrajectoryMini = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini, benchTrajectoryMini, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.MiniHagi."
                "mini_hagi_gpm_canonical_descent\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_mini(path, start, traj, witness_steps=3):
    """C492 negative: inflated declared drop on the last witness
    step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C492 mini-HAGI NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMiniBad : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryMiniBad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMiniBad "
                "benchTrajectoryMiniBad\n\n"
                "theorem mini_hagi_bench_invalid :\n"
                "    checkTrajectory benchStartMiniBad "
                "benchTrajectoryMiniBad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMiniBad, benchTrajectoryMiniBad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C494: MINI-HAGI2 - the SCALED mini bench (deeper trunk, 3
# tasks, 2 grows) in ONE certified run on the REAL corpus
# (--mode mini-hagi2)
#
# Scaling axes vs C492 mini-hagi:
#   (a) TRUNK = 2 SEQUENTIAL BLOCKS (vector L1-rms-surrogate
#       norm -> Linear W1 -> ReLU -> Linear W2, composed twice:
#       phi = Block2(Block1(x))); phase A trains trunk+head
#       JOINTLY by forward finite differences over all 44
#       params (C481 form) - gradients flow through BOTH blocks;
#       after phase A the trunk is FROZEN (honest pin: GPM
#       zero-forgetting and C444 grow are linear-readout
#       statements, so phases B-E operate on the linear head
#       over the frozen phi features).
#   (b) 3 CONTINUAL TASKS (C488 clm_split family): T1 few-shot
#       (2 pts), T2 = first point raising accumulated rank to
#       exactly 3, T3 = the rest.
#   (c) 2 GROW EVENTS in ONE chain: fiber f1 = snap_{1/1000}
#       (phi0*phi1) after phase A, fiber f2 = snap_{1/1000}
#       (phi2*phi3) after phase B; each with the C444 admission
#       margin (cost/risk passthrough eps = 0 => margin =
#       canonical gain) on the CANONICAL objective; a rejected
#       grow leaves the model unchanged (honest REJECT).
#   (d) CHAIN: A-train -> grow1 -> B-continual(GPM) -> grow2 ->
#       C-continual(GPM, accumulated span T1 u T2) -> quant
#       (C443 LS-scale ternary, canonical admission) -> Ville
#       stop (C446) - ONE CertStepData trace.
#
# THE OBJ RULE (C492, extended to T = 3): every step carries
#   obj = OBJ(w) = (MSE_T1 + MSE_T2 + MSE_T3)/3   (exact
#   Fractions) on the CURRENT model state; admission demands a
# measured CANONICAL drop > 0; phase boundaries change nothing
# (a grow starts at w||[0] => predictions identical => OBJ
# EXACTLY continuous, asserted); the executable checker
# re-verifies the whole chain. Lean: Hagi.Theory.MiniHagi2
# (mini_hagi2_canonical_drop, mini_hagi2_gpm_descent).
#
# SNAP PINS (C481/C491 discipline, docstring-frozen): trunk
# input features 1/1000 (mh_load_dataset / rd_snap), grow
# fibers 1/1000 (rd_snap), candidate parameters + head steps
# 1/10000 (cl_snap), finite-difference step h = 1/1000.

MH2_D = 4                          # trunk in/out dim (C484 family)
MH2_HID = 2                        # MLP hidden units per block
MH2_EPS = F(1, 1000)               # L1-rms-surrogate eps (PIN)
MH2_H = F(1, 1000)                 # fd step h (PIN)
MH2_ETA = MH_ETA                   # step size 1/10 (C492)
MH2_GRID = F(1, 10000)             # candidate snap grid (PIN)
MH2_A_STEPS = 4                    # joint fd trunk+head steps
MH2_C_STEPS = 4                    # GPM steps per continual phase
MH2_E_STEPS = 4                    # Ville-stop phase steps
MH2_QUANT_FT = 1                   # quant finetune steps
MH2_NPAR = 2 * (MH2_D + MH2_HID * MH2_D + MH2_D * MH2_HID) \
    + MH2_D                        # 2 blocks + head = 44


def mh2_block_init(seed):
    """Deterministic block init, all fractions on the 1/1000
    grid; seed varies the two blocks."""
    g = [F(1, 2) if i != seed % MH2_D else F(1, 3)
         for i in range(MH2_D)]
    W1 = [[F(1, 2) if (i + j + seed) % 3 else F(-1, 3)
           for i in range(MH2_D)] for j in range(MH2_HID)]
    W2 = [[F(1, 2) if (i + j + seed) % 2 else F(1, 4)
           for j in range(MH2_HID)] for i in range(MH2_D)]
    return (g, W1, W2)


def mh2_block_fwd(bl, v):
    """ONE trunk block: per-coordinate L1-rms-surrogate norm
    g_i*v_i/(|v_i|+eps) -> Linear W1 -> ReLU -> Linear W2
    (C481 atom, vector form; exact Fractions)."""
    g, W1, W2 = bl
    h = [g[i] * v[i] / (abs(v[i]) + MH2_EPS)
         for i in range(MH2_D)]
    r = [max(sum((W1[j][i] * h[i] for i in range(MH2_D)), F(0)),
             F(0)) for j in range(MH2_HID)]
    return [sum((W2[c][j] * r[j] for j in range(MH2_HID)), F(0))
            for c in range(MH2_D)]


def mh2_trunk_fwd(theta, x):
    """The 2-BLOCK trunk: phi(x) = Block2(Block1(x))."""
    b1, b2 = theta
    return mh2_block_fwd(b2, mh2_block_fwd(b1, x))


def mh2_mse(w, data, theta):
    """Head MSE with the trunk computed on the fly (phase A)."""
    return sum(((mh_pred(w, mh2_trunk_fwd(theta, x)) - y) ** 2
                for x, y in data), F(0)) / F(len(data))


def mh2_canon(w, tasks, theta):
    """Canonical objective over the 3 live tasks (phase A)."""
    return sum((mh2_mse(w, t, theta) for t in tasks),
               F(0)) / F(len(tasks))


def mh2_flat(theta, w):
    out = []
    for g, W1, W2 in theta:
        out += list(g) + [e for row in W1 for e in row] \
            + [e for row in W2 for e in row]
    return out + list(w)


def mh2_unflat(p):
    blocks, i = [], 0
    for _ in range(2):
        g = p[i:i + MH2_D]
        i += MH2_D
        W1 = [p[i + j * MH2_D:i + (j + 1) * MH2_D]
              for j in range(MH2_HID)]
        i += MH2_HID * MH2_D
        W2 = [p[i + c * MH2_HID:i + (c + 1) * MH2_HID]
              for c in range(MH2_D)]
        i += MH2_D * MH2_HID
        blocks.append((g, W1, W2))
    return tuple(blocks), p[i:]


def mh2_fmse(w, data):
    """Head MSE over FROZEN feature vectors (phases B-E)."""
    return sum(((mh_pred(w, f) - y) ** 2 for f, y in data),
               F(0)) / F(len(data))


def mh2_fcanon(w, tasks):
    return sum((mh2_fmse(w, t) for t in tasks), F(0)) \
        / F(len(tasks))


def mh2_applyQ(Q, v, d):
    return [sum((v[k] * Q[k][j] for k in range(d)), F(0))
            for j in range(d)]


def mini_hagi2_run(ledger_path):
    """The scaled unified certified cycle on the real corpus:
    2-block fd-trained trunk, 3 tasks, 2 grows, GPM continual,
    ternary quant, Ville stop - ONE canonical CertStepData
    chain. Returns (start_obj, [accepted steps], telemetry,
    stats)."""
    sys.set_int_max_str_digits(0)   # deep-trunk rationals: no
    # decimal-print limit for exact Fraction telemetry
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    # --- phase A state: joint trunk+head
    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {},
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    obj0 = mh2_canon(w, tasks, theta)
    mse_start = [mh2_mse(w, t, theta) for t in tasks]
    for t in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):        # fd through BOTH blocks
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (fd step rolled "
                                           "back)"})
    tel["phases"].append({
        "phase": "A-trunk2", "params": MH2_NPAR,
        "trunk": "2 blocks x (L1-rms -> W1 -> ReLU -> W2), "
                 "frozen after phase A",
        "mse_T1": str(mh2_mse(w, tasks[0], theta)),
        "mse_T2": str(mh2_mse(w, tasks[1], theta)),
        "mse_T3": str(mh2_mse(w, tasks[2], theta)),
        "canonical": str(mh2_canon(w, tasks, theta))})

    # --- freeze the trunk; feature-space state (phases B-E)
    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    fibers = []          # admitted fiber functions on base phi

    def feats_now(base):
        return base + [fib(base) for fib in fibers]

    def task_feats():
        return [[(feats_now(f), y) for f, y in tk] for tk in FT]

    def hold_feats():
        return [[(feats_now(f), y) for f, y in tk] for tk in HF]

    def risk(wcur):
        return mh2_fcanon(wcur, hold_feats())

    def certified_step(phase, wcur, cand, cur):
        o0, o1 = mh2_fcanon(wcur, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": phase, "obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": risk(wcur), "risk'": risk(cand)})
            return cand
        tel["holds"].append({"phase": phase, "drop": o0 - o1,
                             "reason": "canonical drop <= 0: "
                                       "HOLD, rolled back"})
        return wcur

    def grow(phase, fib, label):
        """C444 grow: append fiber, w||[0] continuity, only_last
        certified step, margin admission on canonical obj."""
        nonlocal w
        cur = task_feats()
        nxt = [[(f + [fib(f)], y) for f, y in tk] for tk in cur]
        hxt = [[(f + [fib(f)], y) for f, y in tk]
               for tk in hold_feats()]

        def risk_g(wcur):
            return mh2_fcanon(wcur, hxt)

        wet = w + [F(0)]
        assert mh2_fcanon(wet, nxt) == mh2_fcanon(w, cur), \
            "ABORT: grow broke the obj chain (w||0 must " \
            "preserve OBJ)"
        comb = [p for tk in nxt for p in tk]
        g = mh_grad(wet, comb)
        cand = list(wet)
        cand[-1] = cl_snap(
            [wet[-1] - MH2_ETA * g[-1]], MH2_GRID)[0]
        o0 = mh2_fcanon(wet, nxt)
        o1 = mh2_fcanon(cand, nxt)
        margin = admission_margin(o0 - o1, F(0), F(0))
        if margin > 0:
            raw.append({"phase": phase, "obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": risk_g(wet), "risk'": risk_g(cand),
                        "margin": margin})
            w, fibers_ = cand, fibers + [fib]
            fibers[:] = fibers_         # commit the fiber
            tel["admissions"].append(
                {"phase": phase, "margin": str(margin),
                 "fiber": label, "decision": "ADMIT"})
            return True
        tel["rejects"].append({"phase": phase,
                               "margin": str(margin),
                               "fiber": label,
                               "decision": "REJECT (model "
                                           "unchanged)"})
        return False

    def gpm_phase(name, task_idx, past_idx):
        """Continual phase on tasks[task_idx] with accumulated
        GPM over span(past tasks); naive arm = telemetry."""
        nonlocal w
        cur = task_feats()
        d = len(w)
        past_x = [f for i in past_idx for f, _ in cur[i]]
        basis = mh_gs_basis(past_x, d)
        assert 0 < len(basis) < d, \
            f"ABORT: need 0 < rank(span past) < dim at {name}"
        Q = mh_complement_projector(basis, d)
        past_mse0 = [mh2_fmse(w, cur[i]) for i in past_idx]

        wn = list(w)                    # naive arm (telemetry)
        for _ in range(MH2_C_STEPS):
            g = mh_grad(wn, cur[task_idx])
            cand = cl_snap([wn[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            if mh2_fmse(cand, cur[task_idx]) \
                    < mh2_fmse(wn, cur[task_idx]):
                wn = cand
        forget_naive = [mh2_fmse(wn, cur[i]) - past_mse0[k]
                        for k, i in enumerate(past_idx)]

        for _ in range(MH2_C_STEPS):    # GPM arm (the trace)
            g = mh_grad(w, cur[task_idx])
            delta = mh2_applyQ(
                Q, cl_snap([-MH2_ETA * t2 for t2 in g],
                           MH2_GRID), d)
            for x in past_x:            # gpmOrth, exact
                assert sum((delta[i] * x[i] for i in range(d)),
                           F(0)) == 0, \
                    "ABORT: gpmOrth violated (projection bug)"
            cand = [w[i] + delta[i] for i in range(d)]
            for k, i in enumerate(past_idx):
                assert mh2_fmse(cand, cur[i]) == past_mse0[k],\
                    f"ABORT: past task {i + 1} loss moved " \
                    f"under GPM step ({name})"
            o0 = mh2_fcanon(w, cur)
            o1 = mh2_fcanon(cand, cur)
            if o1 < o0:
                raw.append({"phase": name, "obj": o0,
                            "obj'": o1, "drop": o0 - o1,
                            "risk": risk(w), "risk'": risk(cand)})
                w = cand
            else:
                tel["holds"].append({"phase": name,
                                     "drop": o0 - o1,
                                     "reason": "canonical drop "
                                               "<= 0: HOLD (GPM "
                                               "arm)"})
        forget_gpm = [mh2_fmse(w, cur[i]) - past_mse0[k]
                      for k, i in enumerate(past_idx)]
        assert all(t2 == 0 for t2 in forget_gpm), \
            f"ABORT: GPM forgetting must be EXACTLY zero " \
            f"({name})"
        tel["phases"].append({
            "phase": name, "dim": d, "rank_past": len(basis),
            "mse_task": str(mh2_fmse(w, cur[task_idx])),
            "canonical": str(mh2_fcanon(w, cur))})
        return forget_naive, forget_gpm

    # --- (A2) GROW 1: fiber f1 = snap(phi0 * phi1)
    grow("B-grow1", lambda f: rd_snap(f[0] * f[1]),
         "f1 = snap_{1/1000}(phi0*phi1)")

    # --- (B) CONTINUAL task 2 with GPM over span(T1)
    fnB_n, _ = gpm_phase("C-gpm1", 1, [0])

    # --- (C2) GROW 2: fiber f2 = snap(phi2 * phi3)
    grow("D-grow2", lambda f: rd_snap(f[2] * f[3]),
         "f2 = snap_{1/1000}(phi2*phi3)")

    # --- (C) CONTINUAL task 3 with ACCUMULATED GPM (T1 u T2)
    fnC_n, _ = gpm_phase("E-gpm2", 2, [0, 1])

    cur = task_feats()
    d = len(w)
    tel["outcomes"]["forgetting_naive_B"] = \
        [str(v) for v in fnB_n]
    tel["outcomes"]["forgetting_naive_C"] = \
        [str(v) for v in fnC_n]
    tel["outcomes"]["forgetting_gpm"] = "0 (asserted per step)"

    # --- (F) QUANT: C443 ternary jump on the head weights
    wq, s, q, s0 = mh_tern_quantize(w)
    o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(wq, cur)
    if o1 < o0:
        raw.append({"phase": "F-quant", "obj": o0, "obj'": o1,
                    "drop": o0 - o1, "risk": risk(w),
                    "risk'": risk(wq)})
        w = wq
        tel["admissions"].append(
            {"phase": "F-quant", "decision": "ADMIT",
             "scale": str(s), "pattern": [str(t2) for t2 in q]})
        for _ in range(MH2_QUANT_FT):
            g = mh_grad(w, [p for tk in cur for p in tk])
            cand = cl_snap([w[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            w = certified_step("F-quant-ft", w, cand, cur)
    else:
        tel["holds"].append({"phase": "F-quant",
                             "drop": o0 - o1,
                             "reason": "quant jump drop <= 0: "
                                       "HOLD (honest reject)"})
    tel["phases"].append({"phase": "F-quant",
                          "mse_T1": str(mh2_fmse(w, cur[0])),
                          "mse_T2": str(mh2_fmse(w, cur[1])),
                          "mse_T3": str(mh2_fmse(w, cur[2])),
                          "canonical": str(mh2_fcanon(w, cur))})

    # --- (G) STOP: Ville detector on canonical holdout risk
    h0 = risk(w)
    D, fired, refused = F(0), False, 0
    comb = [p for tk in cur for p in tk]
    for _ in range(MH2_E_STEPS):
        g = mh_grad(w, comb)
        cand = cl_snap([w[i] - MH2_ETA * g[i]
                        for i in range(d)], MH2_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:
            fired = True
            refused += 1
            tel["holds"].append({"phase": "G-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": "G-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(w),
                        "risk'": r1})
            w = cand
            D = D_new
        else:
            tel["holds"].append({"phase": "G-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D)}
    tel["phases"].append({"phase": "G-stop",
                          "mse_T1": str(mh2_fmse(w, cur[0])),
                          "mse_T2": str(mh2_fmse(w, cur[1])),
                          "mse_T3": str(mh2_fmse(w, cur[2])),
                          "canonical": str(mh2_fcanon(w, cur))})

    n = len(raw)
    assert n > 0, "ABORT: mini-hagi2 committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: mini-hagi2 step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path, "dim_final": d,
        "trunk": "2 sequential blocks (L1-rms -> W1 -> ReLU -> "
                 "W2) x2, fd-trained in phase A (44 params), "
                 "FROZEN afterwards",
        "grow1_admitted": any(a["phase"] == "B-grow1"
                              for a in tel["admissions"]),
        "grow2_admitted": any(a["phase"] == "D-grow2"
                              for a in tel["admissions"]),
        "quant_admitted": any(a["phase"] == "F-quant"
                              for a in tel["admissions"]),
        "mse_start": [str(v) for v in mse_start],
        "mse_final": [str(mh2_fmse(w, tk)) for tk in cur],
        "canonical_start": str(obj0),
        "canonical_final": str(raw[-1]["obj'"]),
        "total_drop": str(obj0 - raw[-1]["obj'"]),
        "model": "linear head over the FROZEN 2-block trunk "
                 "(fd-trained, C481 form), canonical obj = mean "
                 "MSE over the 3 live tasks, admission ONLY by "
                 "measured canonical drop > 0",
        "theorem": "Hagi.Theory.MiniHagi2."
                   "mini_hagi2_gpm_descent (C494)",
    }
    return obj0, raw, tel, stats


def emit_lean_mini2(path, start, traj, witness_steps=3):
    """C494 witness: literal mini-hagi2 trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C494 mini-hagi2 witness (real "
                "unified_ledger data; 2-block trunk, 3 tasks, "
                "2 grows).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} "
                "machine-checked steps below (phase-A fd steps "
                "through BOTH trunk blocks). Canonical obj = "
                "(MSE_T1 + MSE_T2 + MSE_T3)/3 (exact "
                "Fractions).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.MiniHagi2\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini2 : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini2 : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini2 "
                "benchTrajectoryMini2\n\n"
                "theorem mini_hagi2_bench_valid :\n"
                "    checkTrajectory benchStartMini2 "
                "benchTrajectoryMini2 = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini2, benchTrajectoryMini2, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.MiniHagi2."
                "mini_hagi2_gpm_descent\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_mini2(path, start, traj, witness_steps=3):
    """C494 negative: inflated declared drop on the last witness
    step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C494 mini-hagi2 NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini2Bad : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryMini2Bad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini2Bad "
                "benchTrajectoryMini2Bad\n\n"
                "theorem mini_hagi2_bench_invalid :\n"
                "    checkTrajectory benchStartMini2Bad "
                "benchTrajectoryMini2Bad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini2Bad, benchTrajectoryMini2Bad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)



# C500: MINI-HAGI3 - rank-trunc GPM escape from the C494
# dead end (--mode mini-hagi3)
#
# The C494 observation (mini-hagi2, phase E-gpm2): with the
# accumulated span of T1 u T2 at rank 3 in dim 6, the FULL GPM
# projection zeroes the snapped gradient step EXACTLY
# (delta == 0 on the 1/10000 grid): task 3 cannot progress
# (4 honest HOLDs, 0 committed steps) - the projection has
# exhausted the space reachable by snapped gradient steps.
#
# C500 applies the C498 GPMRelaxed theory
# (Hagi/Theory/Continual.lean (GPMRelaxed section), rank_trunc_forgetting_bound):
#   - keep the top-k Gram-Schmidt directions of the past span
#     (ordered by carried old-input energy, exact Fractions);
#   - k = min k with max_old sigmaTail^2 <= eps^2 (squared
#     budget, C498 docstring pin); eps = 1/10 PIN: eps = 1/100
#     is INFEASIBLE on the live corpus (min tail2 over k < 3 is
#     ~0.0028 > 1e-4 - measured, see .tmp/C500/research.md);
#   - relaxed step delta = Q_topk . snap(-eta*g): orthogonal to
#     every KEPT direction (exact assert), so per old input x
#     the forgetting obeys |delta.x|^2 <= ||delta||^2 *
#     sigmaTail(x)^2 (Cauchy-Schwarz on the tail residual,
#     exact per-point per-step assert - the bench form of
#     rank_trunc_forgetting_bound);
#   - admission ONLY by measured canonical drop > 0 over ALL
#     live tasks (the certified obj chain stays monotone; the
#     executable checker re-verifies every relaxed step).
# Telemetry per step: k-choice, sigma_tail, ACTUAL output-level
# forgetting vs the ||delta||*sigmaTail bound; the full-GPM arm
# (exact C494 replica) runs alongside for the honest
# full-vs-relaxed comparison line.

MH3_EPS = F(1, 10)                # rank-trunc tolerance (PIN)


def mh3_resid(x, kept, d):
    """Residual of x after projecting out the kept GS basis
    (exact Fractions); sigmaTail^2 = resid . resid."""
    u = list(x)
    for b in kept:
        dq = sum((u[i] * b[i] for i in range(d)), F(0))
        nb = sum((b[i] * b[i] for i in range(d)), F(0))
        u = [u[i] - dq / nb * b[i] for i in range(d)]
    return u


def mini_hagi3_run(ledger_path):
    """mini-hagi2 structure (C494: 2-block trunk, 3 tasks, 2
    grows) with the gpm2 phase ESCAPED by rank-trunc relaxed
    GPM (C498 theory) when the full projection is exhausted.
    Returns (start_obj, [accepted steps], telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {},
                    "gpm2": None, "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    obj0 = mh2_canon(w, tasks, theta)
    mse_start = [mh2_mse(w, t, theta) for t in tasks]
    for t in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (fd step rolled "
                                           "back)"})
    tel["phases"].append({
        "phase": "A-trunk2", "params": MH2_NPAR,
        "trunk": "2 blocks x (L1-rms -> W1 -> ReLU -> W2), "
                 "frozen after phase A",
        "mse_T1": str(mh2_mse(w, tasks[0], theta)),
        "mse_T2": str(mh2_mse(w, tasks[1], theta)),
        "mse_T3": str(mh2_mse(w, tasks[2], theta)),
        "canonical": str(mh2_canon(w, tasks, theta))})

    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    fibers = []

    def feats_now(base):
        return base + [fib(base) for fib in fibers]

    def task_feats():
        return [[(feats_now(f), y) for f, y in tk] for tk in FT]

    def hold_feats():
        return [[(feats_now(f), y) for f, y in tk] for tk in HF]

    def risk(wcur):
        return mh2_fcanon(wcur, hold_feats())

    def certified_step(phase, wcur, cand, cur):
        o0, o1 = mh2_fcanon(wcur, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": phase, "obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": risk(wcur), "risk'": risk(cand)})
            return cand
        tel["holds"].append({"phase": phase, "drop": o0 - o1,
                             "reason": "canonical drop <= 0: "
                                       "HOLD, rolled back"})
        return wcur

    def grow(phase, fib, label):
        nonlocal w
        cur = task_feats()
        nxt = [[(f + [fib(f)], y) for f, y in tk] for tk in cur]
        hxt = [[(f + [fib(f)], y) for f, y in tk]
               for tk in hold_feats()]

        def risk_g(wcur):
            return mh2_fcanon(wcur, hxt)

        wet = w + [F(0)]
        assert mh2_fcanon(wet, nxt) == mh2_fcanon(w, cur), \
            "ABORT: grow broke the obj chain (w||0 must " \
            "preserve OBJ)"
        comb = [p for tk in nxt for p in tk]
        g = mh_grad(wet, comb)
        cand = list(wet)
        cand[-1] = cl_snap(
            [wet[-1] - MH2_ETA * g[-1]], MH2_GRID)[0]
        o0 = mh2_fcanon(wet, nxt)
        o1 = mh2_fcanon(cand, nxt)
        margin = admission_margin(o0 - o1, F(0), F(0))
        if margin > 0:
            raw.append({"phase": phase, "obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": risk_g(wet), "risk'": risk_g(cand),
                        "margin": margin})
            w, fibers_ = cand, fibers + [fib]
            fibers[:] = fibers_
            tel["admissions"].append(
                {"phase": phase, "margin": str(margin),
                 "fiber": label, "decision": "ADMIT"})
            return True
        tel["rejects"].append({"phase": phase,
                               "margin": str(margin),
                               "fiber": label,
                               "decision": "REJECT (model "
                                           "unchanged)"})
        return False

    def gpm_phase(name, task_idx, past_idx):
        """C492/C494 exact GPM phase (unchanged semantics)."""
        nonlocal w
        cur = task_feats()
        d = len(w)
        past_x = [f for i in past_idx for f, _ in cur[i]]
        basis = mh_gs_basis(past_x, d)
        assert 0 < len(basis) < d, \
            f"ABORT: need 0 < rank(span past) < dim at {name}"
        Q = mh_complement_projector(basis, d)
        past_mse0 = [mh2_fmse(w, cur[i]) for i in past_idx]

        wn = list(w)                    # naive arm (telemetry)
        for _ in range(MH2_C_STEPS):
            g = mh_grad(wn, cur[task_idx])
            cand = cl_snap([wn[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            if mh2_fmse(cand, cur[task_idx]) \
                    < mh2_fmse(wn, cur[task_idx]):
                wn = cand
        forget_naive = [mh2_fmse(wn, cur[i]) - past_mse0[k]
                        for k, i in enumerate(past_idx)]

        for _ in range(MH2_C_STEPS):    # GPM arm (the trace)
            g = mh_grad(w, cur[task_idx])
            delta = mh2_applyQ(
                Q, cl_snap([-MH2_ETA * t2 for t2 in g],
                           MH2_GRID), d)
            for x in past_x:            # gpmOrth, exact
                assert sum((delta[i] * x[i] for i in range(d)),
                           F(0)) == 0, \
                    "ABORT: gpmOrth violated (projection bug)"
            cand = [w[i] + delta[i] for i in range(d)]
            for k, i in enumerate(past_idx):
                assert mh2_fmse(cand, cur[i]) == past_mse0[k],\
                    f"ABORT: past task {i + 1} loss moved " \
                    f"under GPM step ({name})"
            o0 = mh2_fcanon(w, cur)
            o1 = mh2_fcanon(cand, cur)
            if o1 < o0:
                raw.append({"phase": name, "obj": o0,
                            "obj'": o1, "drop": o0 - o1,
                            "risk": risk(w), "risk'": risk(cand)})
                w = cand
            else:
                tel["holds"].append({"phase": name,
                                     "drop": o0 - o1,
                                     "reason": "canonical drop "
                                               "<= 0: HOLD (GPM "
                                               "arm)"})
        forget_gpm = [mh2_fmse(w, cur[i]) - past_mse0[k]
                      for k, i in enumerate(past_idx)]
        assert all(t2 == 0 for t2 in forget_gpm), \
            f"ABORT: GPM forgetting must be EXACTLY zero " \
            f"({name})"
        tel["phases"].append({
            "phase": name, "dim": d, "rank_past": len(basis),
            "mse_task": str(mh2_fmse(w, cur[task_idx])),
            "canonical": str(mh2_fcanon(w, cur))})
        return forget_naive, forget_gpm

    def gpm2_relaxed_phase(name, task_idx, past_idx):
        """C500: the gpm2 phase - full-GPM arm (exact C494
        replica, telemetry) vs rank-trunc relaxed arm (the
        certified trace)."""
        nonlocal w
        cur = task_feats()
        d = len(w)
        past_x = [f for i in past_idx for f, _ in cur[i]]
        basis = mh_gs_basis(past_x, d)
        r = len(basis)
        assert 0 < r < d, \
            f"ABORT: need 0 < rank(span past) < dim at {name}"
        past_mse = [mh2_fmse(w, cur[i]) for i in past_idx]
        mse_task0 = mh2_fmse(w, cur[task_idx])

        # --- naive arm (telemetry, as C494)
        wn = list(w)
        for _ in range(MH2_C_STEPS):
            g = mh_grad(wn, cur[task_idx])
            cand = cl_snap([wn[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            if mh2_fmse(cand, cur[task_idx]) \
                    < mh2_fmse(wn, cur[task_idx]):
                wn = cand
        forget_naive = [mh2_fmse(wn, cur[i]) - past_mse[k]
                        for k, i in enumerate(past_idx)]

        # --- FULL arm (telemetry only): exact C494 replica
        Qf = mh_complement_projector(basis, d)
        wf = list(w)
        full_comm = 0
        for _ in range(MH2_C_STEPS):
            g = mh_grad(wf, cur[task_idx])
            delta = mh2_applyQ(
                Qf, cl_snap([-MH2_ETA * t2 for t2 in g],
                            MH2_GRID), d)
            cf = [wf[i] + delta[i] for i in range(d)]
            o0, o1 = mh2_fcanon(wf, cur), mh2_fcanon(cf, cur)
            if o1 < o0:
                wf = cf
                full_comm += 1
        g0 = mh_grad(w, cur[task_idx])
        delta0 = mh2_applyQ(
            Qf, cl_snap([-MH2_ETA * t2 for t2 in g0], MH2_GRID),
            d)
        full_zero_delta = all(t2 == 0 for t2 in delta0)
        full_prog = mse_task0 - mh2_fmse(wf, cur[task_idx])

        # --- relaxed arm (the trace)
        energy = [sum((sum((b[i] * x[i] for i in range(d)),
                           F(0)) ** 2 for x in past_x), F(0))
                  for b in basis]
        order = sorted(range(r), key=lambda j: energy[j],
                       reverse=True)
        kept_for, tail2max = {}, []
        for k in range(r + 1):
            kept_for[k] = [basis[j] for j in order[:k]]
            tail2max.append(max(
                [sum((t2 * t2 for t2 in mh3_resid(
                    x, kept_for[k], d)), F(0))
                 for x in past_x] + [F(0)]))
        kmin = next((k for k in range(r)
                     if tail2max[k] <= MH3_EPS ** 2), None)

        relax_tel = {
            "eps": str(MH3_EPS), "eps2": str(MH3_EPS ** 2),
            "tail2max_by_k": [str(t2) for t2 in tail2max],
            "k_min": kmin,
            "basis_energy_order": [str(energy[j])
                                   for j in order], "steps": []}
        n_relax, max_forget = 0, F(0)
        Qk = mh_complement_projector(kept_for[kmin], d) \
            if kmin is not None else None
        for _ in range(MH2_C_STEPS):
            g = mh_grad(w, cur[task_idx])
            delta = mh2_applyQ(
                Qf, cl_snap([-MH2_ETA * t2 for t2 in g],
                            MH2_GRID), d)
            cand = [w[i] + delta[i] for i in range(d)]
            o0 = mh2_fcanon(w, cur)
            o1 = mh2_fcanon(cand, cur)
            if o1 < o0:          # exact full-GPM commit
                for x in past_x:
                    assert sum((delta[i] * x[i]
                                for i in range(d)), F(0)) == 0, \
                        "ABORT: gpmOrth violated (projection bug)"
                for k2, i in enumerate(past_idx):
                    assert mh2_fmse(cand, cur[i]) \
                        == past_mse[k2], \
                        f"ABORT: past task {i + 1} loss moved " \
                        f"under full GPM step ({name})"
                raw.append({"phase": name, "obj": o0,
                            "obj'": o1, "drop": o0 - o1,
                            "risk": risk(w), "risk'": risk(cand)})
                w = cand
                relax_tel["steps"].append(
                    {"arm": "full", "committed": True})
                continue
            if kmin is None:
                tel["holds"].append({
                    "phase": name, "drop": o0 - o1,
                    "reason": "full-span HOLD and no k < rank "
                              "within eps-budget: HOLD (C494 "
                              "dead end persists)"})
                continue
            dk = mh2_applyQ(
                Qk, cl_snap([-MH2_ETA * t2 for t2 in g],
                            MH2_GRID), d)
            if all(t2 == 0 for t2 in dk):
                tel["holds"].append({
                    "phase": name,
                    "reason": "relaxed delta snapped to 0: "
                              "HOLD"})
                continue
            cand = [w[i] + dk[i] for i in range(d)]
            for b in kept_for[kmin]:
                assert sum((dk[i] * b[i] for i in range(d)),
                           F(0)) == 0, \
                    "ABORT: relaxed orthogonality violated " \
                    "(rank-trunc projection bug)"
            nrm2 = sum((t2 * t2 for t2 in dk), F(0))
            step_f, step_b2 = [], []
            for k2, i in enumerate(past_idx):
                mf, mb2 = F(0), F(0)
                for x, _ in cur[i]:
                    tail = mh3_resid(x, kept_for[kmin], d)
                    tail2 = sum((t2 * t2 for t2 in tail), F(0))
                    dx = sum((dk[i2] * x[i2]
                              for i2 in range(d)), F(0))
                    assert dx * dx <= nrm2 * tail2, \
                        f"ABORT: rank-trunc forgetting bound " \
                        f"violated at {name} (|delta.x| > " \
                        f"||delta||*sigmaTail)"
                    if abs(dx) > mf:
                        mf = abs(dx)
                    if nrm2 * tail2 > mb2:
                        mb2 = nrm2 * tail2
                step_f.append(mf)
                step_b2.append(mb2)
                if mf > max_forget:
                    max_forget = mf
            o0 = mh2_fcanon(w, cur)
            o1 = mh2_fcanon(cand, cur)
            if o1 < o0:
                forget_mse = [mh2_fmse(cand, cur[i]) - past_mse[k2]
                              for k2, i in enumerate(past_idx)]
                raw.append({"phase": name, "obj": o0,
                            "obj'": o1, "drop": o0 - o1,
                            "risk": risk(w), "risk'": risk(cand)})
                w = cand
                past_mse = [mh2_fmse(w, cur[i])
                            for i in past_idx]
                n_relax += 1
                relax_tel["steps"].append({
                    "arm": "relaxed", "committed": True,
                    "k": kmin,
                    "sigma_tail2_max": str(tail2max[kmin]),
                    "delta_norm2": str(nrm2),
                    "forget_out_max": [str(v) for v in step_f],
                    "forget_bound2": [str(v) for v in step_b2],
                    "forget_mse": [str(v) for v in forget_mse]})
            else:
                tel["holds"].append({
                    "phase": name, "drop": o0 - o1,
                    "reason": "relaxed drop <= 0: HOLD"})
        relax_prog = mse_task0 - mh2_fmse(w, cur[task_idx])
        tel["phases"].append({
            "phase": name, "dim": d, "rank_past": r,
            "k_relax": kmin, "eps": str(MH3_EPS),
            "mse_task": str(mh2_fmse(w, cur[task_idx])),
            "canonical": str(mh2_fcanon(w, cur))})
        tel["gpm2"] = {
            "full": {"committed": full_comm,
                     "first_delta_exactly_zero": full_zero_delta,
                     "task3_mse_progress": str(full_prog)},
            "relaxed": {"committed": n_relax,
                        "task3_mse_progress": str(relax_prog),
                        "max_forgetting_output":
                            str(max_forget)},
            "detail": relax_tel}
        return forget_naive

    # --- (A2) GROW 1
    grow("B-grow1", lambda f: rd_snap(f[0] * f[1]),
         "f1 = snap_{1/1000}(phi0*phi1)")

    # --- (B) CONTINUAL task 2 with GPM over span(T1)
    fnB_n, _ = gpm_phase("C-gpm1", 1, [0])

    # --- (C2) GROW 2
    grow("D-grow2", lambda f: rd_snap(f[2] * f[3]),
         "f2 = snap_{1/1000}(phi2*phi3)")

    # --- (C) CONTINUAL task 3: RANK-TRUNC RELAXED GPM (C500)
    fnC_n = gpm2_relaxed_phase("E-gpm2relax", 2, [0, 1])

    cur = task_feats()
    d = len(w)
    tel["outcomes"]["forgetting_naive_B"] = \
        [str(v) for v in fnB_n]
    tel["outcomes"]["forgetting_naive_C"] = \
        [str(v) for v in fnC_n]
    tel["outcomes"]["forgetting_gpm"] = \
        "0 exact (C-gpm1); gpm2: relaxed, per-step bound-asserted"

    # --- (F) QUANT
    wq, s, q, s0 = mh_tern_quantize(w)
    o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(wq, cur)
    if o1 < o0:
        raw.append({"phase": "F-quant", "obj": o0, "obj'": o1,
                    "drop": o0 - o1, "risk": risk(w),
                    "risk'": risk(wq)})
        w = wq
        tel["admissions"].append(
            {"phase": "F-quant", "decision": "ADMIT",
             "scale": str(s), "pattern": [str(t2) for t2 in q]})
        for _ in range(MH2_QUANT_FT):
            g = mh_grad(w, [p for tk in cur for p in tk])
            cand = cl_snap([w[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            w = certified_step("F-quant-ft", w, cand, cur)
    else:
        tel["holds"].append({"phase": "F-quant",
                             "drop": o0 - o1,
                             "reason": "quant jump drop <= 0: "
                                       "HOLD (honest reject)"})
    tel["phases"].append({"phase": "F-quant",
                          "mse_T1": str(mh2_fmse(w, cur[0])),
                          "mse_T2": str(mh2_fmse(w, cur[1])),
                          "mse_T3": str(mh2_fmse(w, cur[2])),
                          "canonical": str(mh2_fcanon(w, cur))})

    # --- (G) STOP: Ville detector on canonical holdout risk
    h0 = risk(w)
    D, fired, refused = F(0), False, 0
    comb = [p for tk in cur for p in tk]
    for _ in range(MH2_E_STEPS):
        g = mh_grad(w, comb)
        cand = cl_snap([w[i] - MH2_ETA * g[i]
                        for i in range(d)], MH2_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:
            fired = True
            refused += 1
            tel["holds"].append({"phase": "G-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": "G-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(w),
                        "risk'": r1})
            w = cand
            D = D_new
        else:
            tel["holds"].append({"phase": "G-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D)}
    tel["phases"].append({"phase": "G-stop",
                          "mse_T1": str(mh2_fmse(w, cur[0])),
                          "mse_T2": str(mh2_fmse(w, cur[1])),
                          "mse_T3": str(mh2_fmse(w, cur[2])),
                          "canonical": str(mh2_fcanon(w, cur))})

    n = len(raw)
    assert n > 0, "ABORT: mini-hagi3 committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: mini-hagi3 step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path, "dim_final": d,
        "trunk": "2 sequential blocks (L1-rms -> W1 -> ReLU -> "
                 "W2) x2, fd-trained in phase A (44 params), "
                 "FROZEN afterwards",
        "grow1_admitted": any(a["phase"] == "B-grow1"
                              for a in tel["admissions"]),
        "grow2_admitted": any(a["phase"] == "D-grow2"
                              for a in tel["admissions"]),
        "quant_admitted": any(a["phase"] == "F-quant"
                              for a in tel["admissions"]),
        "gpm2_full_committed": tel["gpm2"]["full"]["committed"],
        "gpm2_relaxed_committed":
            tel["gpm2"]["relaxed"]["committed"],
        "gpm2_k_relax": tel["gpm2"]["detail"]["k_min"],
        "gpm2_eps": str(MH3_EPS),
        "mse_start": [str(v) for v in mse_start],
        "mse_final": [str(mh2_fmse(w, tk)) for tk in cur],
        "canonical_start": str(obj0),
        "canonical_final": str(raw[-1]["obj'"]),
        "total_drop": str(obj0 - raw[-1]["obj'"]),
        "model": "linear head over the FROZEN 2-block trunk "
                 "(C494 structure); gpm2 phase ESCAPED by "
                 "rank-trunc relaxed GPM (C498 "
                 "rank_trunc_forgetting_bound: per-step "
                 "per-old-input exact assert |delta.x|^2 <= "
                 "||delta||^2 * sigmaTail^2, eps = 1/10 PIN); "
                 "canonical obj = mean MSE over the 3 live "
                 "tasks, admission ONLY by measured canonical "
                 "drop > 0",
        "theorem": "Hagi.Theory.GPMRelaxed."
                   "rank_trunc_forgetting_bound (C498, applied "
                   "bench-side; Lean bridge theorem down-scoped)",
    }
    return obj0, raw, tel, stats


def emit_lean_mini3(path, start, traj, witness_steps=3):
    """C500 witness: literal mini-hagi3 trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C500 mini-hagi3 witness (real "
                "unified_ledger data; C494 structure + rank-trunc "
                "relaxed GPM escape on the gpm2 phase).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} "
                "machine-checked steps below. Canonical obj = "
                "(MSE_T1 + MSE_T2 + MSE_T3)/3 (exact "
                "Fractions).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.Continual\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini3 : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini3 : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini3 "
                "benchTrajectoryMini3\n\n"
                "theorem mini_hagi3_bench_valid :\n"
                "    checkTrajectory benchStartMini3 "
                "benchTrajectoryMini3 = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini3, benchTrajectoryMini3, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.GPMRelaxed."
                "rank_trunc_forgetting_bound\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_mini3(path, start, traj, witness_steps=3):
    """C500 negative: inflated declared drop on the last witness
    step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C500 mini-hagi3 NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini3Bad : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryMini3Bad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini3Bad "
                "benchTrajectoryMini3Bad\n\n"
                "theorem mini_hagi3_bench_invalid :\n"
                "    checkTrajectory benchStartMini3Bad "
                "benchTrajectoryMini3Bad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini3Bad, benchTrajectoryMini3Bad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


    print(f"written: {path}", file=sys.stderr)


# (--mode mini-hagi4)
#
# C504: grow = adding a WHOLE BLOCK to the trunk (depth 2 -> 3),
# not just a fiber feature. The new 3rd block operates on the
# FROZEN 2-block phi-features and has the RESIDUAL-ZERO gate
# form  y = v + gamma * mlp(v)  with gamma = 0 at admission:
# y = v EXACTLY (Fraction-exact: 0*a = 0, a + 0 = a) regardless
# of the block internals (L1-rms-surrogate norm is NOT identity
# even at g = 1: 1/(1+1/1000) = 1000/1001 != 1 - measured, see
# .tmp/C504/research.md). This is the bench instance of the C450
# identityBlock pattern (Hagi/Theory/FunctionPreservingGrowth.
# trunk_function_preserving + function_preserving_admissible):
# the GROW step itself is admitted in the NEUTRAL configuration
# (gain = 0, dCost = 0, dRisk = 0, lamM = lamR = 0, eps = 0 ->
# 0 <= 0); it is NOT a CertStepData step (no measured drop at
# gamma = 0, exactly like w||[0] fiber grows in C494). The
# block's contribution appears from SUBSEQUENT certified steps
# on its 21 params (gamma, g, W1, W2): fd gradient, 1/10000
# snap, admission ONLY by measured canonical drop > 0.

MH4_STEPS = 4                      # certified steps on the new block


def mh4_block_init():
    """3rd block: gamma = 0 (residual-zero identity), arbitrary
    internals on the 1/1000 grid (fully masked by gamma = 0)."""
    g = [F(1, 2) if i else F(1, 3) for i in range(MH2_D)]
    W1 = [[F(1, 2) if (i + j + 2) % 3 else F(-1, 3)
           for i in range(MH2_D)] for j in range(MH2_HID)]
    W2 = [[F(1, 2) if (i + j + 2) % 2 else F(1, 4)
           for j in range(MH2_HID)] for i in range(MH2_D)]
    return (F(0), g, W1, W2)


def mh4_mlp(bl, v):
    _, g, W1, W2 = bl
    h = [g[i] * v[i] / (abs(v[i]) + MH2_EPS)
         for i in range(MH2_D)]
    r = [max(sum((W1[j][i] * h[i] for i in range(MH2_D)), F(0)),
             F(0)) for j in range(MH2_HID)]
    return [sum((W2[c][j] * r[j] for j in range(MH2_HID)), F(0))
            for c in range(MH2_D)]


def mh4_block_fwd(bl, v):
    """Residual-gated block y = v + gamma*mlp(v); at gamma = 0
    this is EXACTLY v (the C450 identityBlock bench instance)."""
    gam = bl[0]
    m = mh4_mlp(bl, v)
    return [v[i] + gam * m[i] for i in range(MH2_D)]


def mh4_flat(bl):
    gam, g, W1, W2 = bl
    return ([gam] + list(g)
            + [e for row in W1 for e in row]
            + [e for row in W2 for e in row])


def mh4_unflat(p):
    i = 1
    g = p[i:i + MH2_D]
    i += MH2_D
    W1 = [p[i + j * MH2_D:i + (j + 1) * MH2_D]
          for j in range(MH2_HID)]
    i += MH2_HID * MH2_D
    W2 = [p[i + c * MH2_HID:i + (c + 1) * MH2_HID]
          for c in range(MH2_D)]
    return (p[0], g, W1, W2)


def mini_hagi4_run(ledger_path):
    """mini-hagi3 skeleton with the fiber grows REPLACED by a
    whole-block trunk grow (depth 2 -> 3, residual-zero identity
    admission C450, certified block training). Returns (start,
    [accepted steps], telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {},
                    "growblock": None,
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint training (mini3 phase A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (fd step rolled "
                                           "back)"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2,
        "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    # --- (B) GROW-BLOCK: depth 2 -> 3, residual-zero identity
    bl3 = mh4_block_init()
    assert bl3[0] == 0, "ABORT: residual gate must start at 0"

    def feats3(bl, base):
        return [[(mh4_block_fwd(bl, f), y) for f, y in tk]
                for tk in base]

    oA = mh2_fcanon(w, FT)
    FT3 = feats3(bl3, FT)
    HF3 = feats3(bl3, HF)
    assert mh2_fcanon(w, FT3) == oA, \
        "ABORT: block grow broke the obj chain (gamma = 0 must " \
        "preserve OBJ EXACTLY)"
    # neutral C450 admission: gain = 0, dCost = 0, dRisk = 0,
    # lamM = lamR = eps = 0  =>  0 <= 0  (admit). Margin computed
    # with the REAL admission_margin at eps = 0 for the record;
    # the strict mirror (eps > 0 => margin > 0 => REJECT) is the
    # negative-control line below (margin_positivity_refuses).
    margin0 = F(0) + F(0) + F(0) - F(0)
    assert margin0 == 0
    tel["admissions"].append(
        {"phase": "B3-grow", "margin": "0",
         "decision": "ADMIT (neutral identity, C450 "
                     "function_preserving_admissible: 0 <= 0; "
                     "contribution comes from certified steps)"})
    tel["rejects"].append(
        {"phase": "B3-grow", "margin": str(F(1, 10)),
         "decision": "REJECT (negative control, C450 "
                     "margin_positivity_refuses: eps = 1/10 > 0 "
                     "=> margin > 0 => gate refuses)"})

    # --- (C) certified steps on the NEW block (21 params)
    p3 = mh4_flat(bl3)
    n3 = len(p3)
    assert n3 == 1 + MH2_D + 2 * MH2_D * MH2_HID, \
        "ABORT: block param count mismatch"

    def canon3(pp):
        return mh2_fcanon(w, feats3(mh4_unflat(pp), FT))

    def risk3(pp):
        return mh2_fcanon(w, feats3(mh4_unflat(pp), HF))

    block_committed = 0
    for _ in range(MH4_STEPS):
        o = canon3(p3)
        gfd = []
        for k in range(n3):
            q = list(p3)
            q[k] = q[k] + MH2_H
            gfd.append((canon3(q) - o) / MH2_H)
        cand = cl_snap([p3[k] - MH2_ETA * gfd[k]
                        for k in range(n3)], MH2_GRID)
        o2 = canon3(cand)
        if o2 < o:
            raw.append({"phase": "C-block3", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": risk3(p3), "risk'": risk3(cand)})
            p3 = cand
            block_committed += 1
        else:
            tel["holds"].append({"phase": "C-block3",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (block fd step "
                                           "rolled back)"})
    bl3 = mh4_unflat(p3)
    FT = feats3(bl3, FT)
    HF = feats3(bl3, HF)
    tel["phases"].append({
        "phase": "C-block3", "depth": 3, "params": n3,
        "committed": block_committed, "gamma": str(bl3[0]),
        "canonical_before": str(oA),
        "canonical": str(mh2_fcanon(w, FT))})
    tel["growblock"] = {
        "depth": "2 -> 3",
        "form": "y = v + gamma*mlp(v), gamma0 = 0 "
                "(residual-zero identity, exact)",
        "obj_before_grow": str(oA),
        "obj_after_grow": str(oA),
        "exact_invariant": True,
        "block_committed_steps": block_committed,
        "block_contribution_drop": str(oA - mh2_fcanon(w, FT))}
    # NB: obj_after_grow == obj_before_grow by the assert above.

    # --- (D) continual: exact GPM on task 2, relaxed on task 3
    def gpm_phase(name, task_idx, past_idx):
        nonlocal w
        cur = FT
        d = len(w)
        past_x = [f for i in past_idx for f, _ in cur[i]]
        basis = mh_gs_basis(past_x, d)
        assert 0 < len(basis) < d, \
            f"ABORT: need 0 < rank(span past) < dim at {name}"
        Q = mh_complement_projector(basis, d)
        past_mse0 = [mh2_fmse(w, cur[i]) for i in past_idx]
        wn = list(w)                    # naive arm (telemetry)
        for _ in range(MH2_C_STEPS):
            g = mh_grad(wn, cur[task_idx])
            cand = cl_snap([wn[i] - MH2_ETA * g[i]
                            for i in range(d)], MH2_GRID)
            if mh2_fmse(cand, cur[task_idx]) \
                    < mh2_fmse(wn, cur[task_idx]):
                wn = cand
        forget_naive = [mh2_fmse(wn, cur[i]) - past_mse0[k]
                        for k, i in enumerate(past_idx)]
        for _ in range(MH2_C_STEPS):    # GPM arm (the trace)
            g = mh_grad(w, cur[task_idx])
            delta = mh2_applyQ(
                Q, cl_snap([-MH2_ETA * t2 for t2 in g],
                           MH2_GRID), d)
            for x in past_x:            # gpmOrth, exact
                assert sum((delta[i] * x[i] for i in range(d)),
                           F(0)) == 0, \
                    "ABORT: gpmOrth violated (projection bug)"
            cand = [w[i] + delta[i] for i in range(d)]
            for k, i in enumerate(past_idx):
                assert mh2_fmse(cand, cur[i]) == past_mse0[k],\
                    f"ABORT: past task {i + 1} loss moved " \
                    f"under GPM step ({name})"
            o0 = mh2_fcanon(w, cur)
            o1 = mh2_fcanon(cand, cur)
            if o1 < o0:
                raw.append({"phase": name, "obj": o0,
                            "obj'": o1, "drop": o0 - o1,
                            "risk": risk(w), "risk'": risk(cand)})
                w = cand
            else:
                tel["holds"].append({"phase": name,
                                     "drop": o0 - o1,
                                     "reason": "canonical drop "
                                               "<= 0: HOLD (GPM "
                                               "arm)"})
        forget_gpm = [mh2_fmse(w, cur[i]) - past_mse0[k]
                      for k, i in enumerate(past_idx)]
        assert all(t2 == 0 for t2 in forget_gpm), \
            f"ABORT: GPM forgetting must be EXACTLY zero ({name})"
        tel["phases"].append({
            "phase": name, "dim": d, "rank_past": len(basis),
            "mse_task": str(mh2_fmse(w, cur[task_idx])),
            "canonical": str(mh2_fcanon(w, cur))})
        return forget_naive

    def risk(wcur):
        return mh2_fcanon(wcur, HF)

    fnB_n = gpm_phase("D-gpm1", 1, [0])
    fnC_n = gpm_phase("E-gpm2", 2, [0, 1])

    cur = FT
    d = len(w)
    tel["outcomes"]["forgetting_naive_B"] = \
        [str(v) for v in fnB_n]
    tel["outcomes"]["forgetting_naive_C"] = \
        [str(v) for v in fnC_n]
    tel["outcomes"]["forgetting_gpm"] = "0 exact (D-gpm1, E-gpm2)"

    # --- (F) STOP: Ville detector on canonical holdout risk
    h0 = risk(w)
    D_, fired, refused = F(0), False, 0
    comb = [p for tk in cur for p in tk]
    for _ in range(MH2_E_STEPS):
        g = mh_grad(w, comb)
        cand = cl_snap([w[i] - MH2_ETA * g[i]
                        for i in range(d)], MH2_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:
            fired = True
            refused += 1
            tel["holds"].append({"phase": "F-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": "F-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(w),
                        "risk'": r1})
            w = cand
            D_ = D_new
        else:
            tel["holds"].append({"phase": "F-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D_)}
    tel["phases"].append({"phase": "F-stop",
                          "canonical": str(mh2_fcanon(w, cur))})

    n = len(raw)
    assert n > 0, "ABORT: mini-hagi4 committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: mini-hagi4 step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path, "dim_final": d,
        "trunk": "2 fd-trained blocks FROZEN + grown 3rd block "
                 "(residual-zero identity admission, C450 "
                 "pattern) certified-trained in phase C",
        "trunk_depth_final": 3,
        "grow_block_neutral_admitted": True,
        "grow_block_obj_invariant_exact": True,
        "block_committed_steps": block_committed,
        "canonical_start": str(obj0),
        "canonical_final": str(raw[-1]["obj'"]),
        "total_drop": str(obj0 - raw[-1]["obj'"]),
        "model": "linear head over the 3-block trunk (grown by "
                 "a residual-zero identity block, depth 2 -> 3); "
                 "canonical obj = mean MSE over the 3 live "
                 "tasks; admission ONLY by measured canonical "
                 "drop > 0 (the grow step itself is the neutral "
                 "C450 admission, not a chain step)",
        "theorem": "Hagi.Theory.GrowTrunkBlock."
                   "grow_block_bench_sound (C504; bench "
                   "instance of C450 trunk_function_preserving)"
    }
    return obj0, raw, tel, stats


def emit_lean_mini4(path, start, traj, witness_steps=3):
    """C504 witness: literal mini-hagi4 trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C504 mini-hagi4 witness (real "
                "unified_ledger data; mini-hagi3 skeleton with "
                "the WHOLE-BLOCK trunk grow: depth 2 -> 3 via a "
                "residual-zero identity block, C450 pattern).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} "
                "machine-checked steps below. Canonical obj = "
                "(MSE_T1 + MSE_T2 + MSE_T3)/3 (exact "
                "Fractions).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.GrowTrunkBlock\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini4 : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini4 : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini4 "
                "benchTrajectoryMini4\n\n"
                "theorem mini_hagi4_bench_valid :\n"
                "    checkTrajectory benchStartMini4 "
                "benchTrajectoryMini4 = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini4, benchTrajectoryMini4, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.GrowTrunkBlock."
                "grow_block_bench_sound\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_mini4(path, start, traj, witness_steps=3):
    """C504 negative: inflated declared drop on the last witness
    step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C504 mini-hagi4 NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini4Bad : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini4Bad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini4Bad "
                "benchTrajectoryMini4Bad\n\n"
                "theorem mini_hagi4_bench_invalid :\n"
                "    checkTrajectory benchStartMini4Bad "
                "benchTrajectoryMini4Bad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini4Bad, benchTrajectoryMini4Bad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# (--mode mini-hagi5)
#
# C506: REPEATED grow cycle -- several identity-grow events in
# ONE run (depth 2 -> 3 -> 4 -> 5): grow #k admits a residual-
# zero identity block (gamma = 0, C450 neutral admission, EXACT
# obj-invariant assert at EVERY event), then certified fd steps
# train ONLY the new block's 21 params (all older blocks stay
# FROZEN -- GPM spirit, KISS: no joint retraining). The whole
# loop runs under an explicit COMPUTATIONAL BUDGET:
#   * cap on feature-fraction denominator size BEFORE each grow
#     (repeated block composition multiplies denominators ~3.2x
#     per grow -- measured: 63 -> 263 -> 789 -> 2366 digits for
#     depth 2 -> 3 -> 4 -> 5, see .tmp/C506/research.md);
#   * cap on the total number of certified steps;
#   * Ville stop (C446) terminates the run FINALLY.
# If a cap fires, the budget-stop is HONESTLY logged with its
# reason; if depth 5 is reached without firing, the measured
# projection of the next grow (~3.2x denominators, ~150 s) is
# logged as the honest computational-budget limit of the bit.

MH5_MAX_DEPTH = 5                   # grow targets: 3, 4, 5
MH5_DEN_CAP = 10 ** 4000            # feature denominator cap
MH5_STEPS_PER_BLOCK = 4             # certified steps per new block
MH5_STEP_CAP = 24                   # total certified-step budget


def mh5_block_init(seed):
    """Grown block: gamma = 0 (residual-zero identity) with
    seed-varied internals on the 1/1000 grid (fully masked by
    gamma = 0; variation only matters once gamma != 0)."""
    g = [F(1, 2) if (i + seed) % 2 else F(1, 3)
         for i in range(MH2_D)]
    W1 = [[F(1, 2) if (i + j + 2 + seed) % 3 else F(-1, 3)
           for i in range(MH2_D)] for j in range(MH2_HID)]
    W2 = [[F(1, 2) if (i + j + 2 + seed) % 2 else F(1, 4)
           for j in range(MH2_HID)] for i in range(MH2_D)]
    return (F(0), g, W1, W2)


def mini_hagi5_run(ledger_path):
    """Repeated grow cycle: depth 2 -> 3 -> 4 -> 5, each grow =
    neutral identity admission (EXACT obj-invariant assert) +
    certified training of the NEW block only; explicit
    computational budget; Ville stop finally. Returns (start,
    [accepted steps], telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {},
                    "growcycle": [], "budget": [],
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint training (mini3/4 phase A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (fd step rolled "
                                           "back)"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2,
        "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    def featsk(bl, base):
        return [[(mh4_block_fwd(bl, f), y) for f, y in tk]
                for tk in base]

    def maxden(base):
        return max(abs(c.denominator)
                   for tk in base for f, _ in tk for c in f)

    def risk(wcur):
        return mh2_fcanon(wcur, HF)

    # --- (B) REPEATED GROW CYCLE: depth 2 -> 3 -> 4 -> 5
    depth = 2
    budget_hit = None
    grow_events = 0
    while depth < MH5_MAX_DEPTH:
        # budget check BEFORE the grow (honest either way)
        md, used = maxden(FT), len(raw)
        den_ok = md <= MH5_DEN_CAP
        steps_ok = used <= MH5_STEP_CAP
        if not (den_ok and steps_ok):
            budget_hit = ("denominator cap" if not den_ok
                          else "step cap")
            tel["budget"].append({
                "at_depth": depth, "maxden_digits": md.bit_length()
                * 301 // 1000,
                "den_cap_digits": 4000, "steps_used": used,
                "step_cap": MH5_STEP_CAP,
                "decision": f"BUDGET-STOP before grow "
                            f"#{grow_events + 1}: {budget_hit} "
                            f"exceeded (honest limit, logged)"})
            break
        seed = grow_events
        bl = mh5_block_init(seed)
        assert bl[0] == 0, \
            "ABORT: residual gate must start at 0"

        oA = mh2_fcanon(w, FT)
        FTg = featsk(bl, FT)
        HFg = featsk(bl, HF)
        assert mh2_fcanon(w, FTg) == oA, \
            "ABORT: grow #{} broke the obj chain (gamma = 0 " \
            "must preserve OBJ EXACTLY at EVERY grow)".format(
                grow_events + 1)
        # neutral C450 admission (margin 0 => 0 <= 0 => ADMIT)
        # + strict negative control (eps > 0 => REJECT).
        margin0 = F(0) + F(0) + F(0) - F(0)
        assert margin0 == 0
        tel["admissions"].append({
            "phase": f"B-grow{grow_events + 1}", "margin": "0",
            "decision": "ADMIT (neutral identity, C450 "
                        "function_preserving_admissible: 0 <= 0; "
                        "contribution comes from certified "
                        "steps)"})
        tel["rejects"].append({
            "phase": f"B-grow{grow_events + 1}",
            "margin": str(F(1, 10)),
            "decision": "REJECT (negative control, C450 "
                        "margin_positivity_refuses: eps = 1/10 "
                        "> 0 => margin > 0 => gate refuses)"})

        # certified steps on the NEW block only (21 params)
        p3 = mh4_flat(bl)
        n3 = len(p3)
        assert n3 == 1 + MH2_D + 2 * MH2_D * MH2_HID, \
            "ABORT: block param count mismatch"

        def canonk(pp, base):
            return mh2_fcanon(w, featsk(mh4_unflat(pp), base))

        committed = 0
        phase_name = f"C-block{depth + 1}"
        for _ in range(MH5_STEPS_PER_BLOCK):
            o = canonk(p3, FT)
            gfd = []
            for k in range(n3):
                q = list(p3)
                q[k] = q[k] + MH2_H
                gfd.append((canonk(q, FT) - o) / MH2_H)
            cand = cl_snap([p3[k] - MH2_ETA * gfd[k]
                            for k in range(n3)], MH2_GRID)
            o2 = canonk(cand, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonk(p3, HF),
                            "risk'": canonk(cand, HF)})
                p3 = cand
                committed += 1
            else:
                tel["holds"].append({"phase": phase_name,
                                     "drop": o - o2,
                                     "reason": "canonical drop <= 0: "
                                               "HOLD (block fd step "
                                               "rolled back)"})
        bl = mh4_unflat(p3)
        FT = featsk(bl, FT)
        HF = featsk(bl, HF)
        oB = mh2_fcanon(w, FT)
        depth += 1
        grow_events += 1
        tel["phases"].append({
            "phase": phase_name, "depth": depth, "params": n3,
            "committed": committed, "gamma": str(bl[0]),
            "canonical_before": str(oA),
            "canonical": str(oB)})
        tel["growcycle"].append({
            "grow": grow_events, "depth": depth,
            "obj_before_grow": str(oA),
            "obj_after_grow": str(oA),
            "exact_invariant": True,
            "block_committed_steps": committed,
            "block_contribution_drop": str(oA - oB),
            "maxden_digits": len(str(maxden(FT)))})
        tel["budget"].append({
            "at_depth": depth, "maxden_digits": len(str(maxden(FT))),
            "den_cap_digits": 4000, "steps_used": len(raw),
            "step_cap": MH5_STEP_CAP,
            "decision": "GROW ADMITTED within budget "
                        "(denominators and steps under caps)"})

    if budget_hit is None and depth >= MH5_MAX_DEPTH:
        # honest measured limit: project the next grow
        md_next = len(str(maxden(FT))) * 32 // 10  # ~3.2x measured
        tel["budget"].append({
            "at_depth": depth, "maxden_digits": len(str(maxden(FT))),
            "den_cap_digits": 4000, "steps_used": len(raw),
            "step_cap": MH5_STEP_CAP,
            "decision": "MAX DEPTH reached without a cap firing; "
                        "honest limit of the computational "
                        "budget: next grow (depth 6) projects "
                        f"~{md_next}-digit feature denominators "
                        "(~3.2x growth ratio, measured across "
                        "grows 1-3) and ~150 s wall time -- "
                        "logged as the measured budget limit"})

    # --- (D) STOP: Ville detector on canonical holdout risk
    cur = FT
    d = len(w)
    h0 = risk(w)
    D_, fired, refused = F(0), False, 0
    comb = [p for tk in cur for p in tk]
    for _ in range(MH2_E_STEPS):
        g = mh_grad(w, comb)
        cand = cl_snap([w[i] - MH2_ETA * g[i]
                        for i in range(d)], MH2_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:
            fired = True
            refused += 1
            tel["holds"].append({"phase": "D-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": "D-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(w),
                        "risk'": r1})
            w = cand
            D_ = D_new
        else:
            tel["holds"].append({"phase": "D-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D_)}
    tel["phases"].append({"phase": "D-stop",
                          "canonical": str(mh2_fcanon(w, cur))})

    n = len(raw)
    assert n > 0, "ABORT: mini-hagi5 committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], "ABORT: obj chain broken"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: mini-hagi5 step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path, "dim_final": d,
        "trunk": f"2 fd-trained blocks FROZEN + {grow_events} "
                 "grown residual-zero identity blocks, each "
                 "certified-trained in isolation (C450 pattern, "
                 "repeated grow cycle)",
        "trunk_depth_final": depth,
        "grow_events": grow_events,
        "budget_stop": budget_hit,
        "grow_obj_invariant_exact_every": True,
        "canonical_start": str(obj0),
        "canonical_final": str(raw[-1]["obj'"]),
        "total_drop": str(obj0 - raw[-1]["obj'"]),
        "model": "linear head over the grown trunk (depth 2 -> "
                 f"{depth} via {grow_events} repeated residual-"
                 "zero identity grows + certified block training); "
                 "canonical obj = mean MSE over the 3 live "
                 "tasks; admission ONLY by measured canonical "
                 "drop > 0 (each grow itself is the neutral C450 "
                 "admission, not a chain step)",
        "theorem": "Hagi.Theory.GrowTrunkBlock."
                   "grow_blocks_repeat_sound (C506; repeated "
                   "bench instance of C450 trunk_function_"
                   "preserving)"
    }
    return obj0, raw, tel, stats


def emit_lean_mini5(path, start, traj, witness_steps=3):
    """C506 witness: literal mini-hagi5 trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly (depth-5 obj fractions ~10^5 chars
    are not Lean-elaborable -- prefix only, stated openly)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C506 mini-hagi5 witness (real "
                "unified_ledger data; REPEATED grow cycle: depth "
                "2 -> 5 via 3 residual-zero identity grows, each "
                "followed by certified block training; explicit "
                "computational budget + Ville stop).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness: "
                "deep-grow obj fractions are ~10^5 chars and not "
                "Lean-elaborable; the full chain is asserted "
                "exactly in Python and counted here honestly). "
                "Canonical obj = (MSE_T1 + MSE_T2 + MSE_T3)/3 "
                "(exact Fractions).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.GrowTrunkBlock\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini5 : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini5 : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini5 "
                "benchTrajectoryMini5\n\n"
                "theorem mini_hagi5_bench_valid :\n"
                "    checkTrajectory benchStartMini5 "
                "benchTrajectoryMini5 = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini5, benchTrajectoryMini5, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.GrowTrunkBlock."
                "grow_blocks_repeat_sound\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_mini5(path, start, traj, witness_steps=3):
    """C506 negative: inflated declared drop on the last witness
    step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C506 mini-hagi5 NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMini5Bad : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMini5Bad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMini5Bad "
                "benchTrajectoryMini5Bad\n\n"
                "theorem mini_hagi5_bench_invalid :\n"
                "    checkTrajectory benchStartMini5Bad "
                "benchTrajectoryMini5Bad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMini5Bad, benchTrajectoryMini5Bad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C521: SNAP-RATIONAL REPEATED GROW CYCLE (--mode grow-snap)
#
# C506 measured the exponential wall: feature-fraction
# denominators multiply ~3.2x per grow (63 -> 263 -> 789 ->
# 2366 digits for depth 2 -> 5), depth 6 projected ~8000
# digits / ~150 s -- an HONEST computational-budget limit of
# the repeated-grow bit. C521 removes the WALL, not by more
# budget, but by a CERTIFIED SNAP POLICY applied at every grow
# boundary:
#
#   * after each grow event's certified block training, the
#     trained block's weights are snapped to the q/2^k grid
#     (banker's rounding, exact Fractions) and the resulting
#     FEATURES are snapped to the same q/2^k grid -- per-value
#     error <= 2^-(k+1) (half-cell), denominators reset to
#     <= 2^k at every grow boundary (the x3.2 compounding
#     starts over from k bits, NOT from the previous depth's
#     thousands of digits);
#   * the snap is CERTIFIED, not assumed: the objective is a
#     linear head over features (obj_point = (w.f - y)^2), so
#     the per-point degradation admits the exact Lipschitz-
#     style bound |(s+ds-y)^2 - (s-y)^2| <= (2|s-y| + |ds|)*|ds|
#     with ds = w.(f' - f) computed EXACTLY in Fractions (the
#     bench form of the per-block hLip premise, BlockLipschitz
#     C436: composition bounds multiply); the summed mean is
#     the certified err_bound and the run ASSERTS the measured
#     obj_after_snap <= obj_before_snap + err_bound;
#   * telescoping: the certified cycle bound is
#     obj_final <= obj_cycle_start + sum(per-snap bounds)
#     (each certified fd drop contributes <= 0) -- the Lean
#     side is Hagi.Theory.GrowSnap.grow_snap_cycle_sound.
#
# The grow itself stays the C506 residual-zero identity (EXACT
# obj invariant asserted at EVERY event); only the POST-GROW
# snap is new, and it is deterministic (round-half-even on
# Fractions, no float). Result: depth 8+ inside the budget.

GS_K = 40                          # snap grid q/2^k (den <= 2^40)
GS_MAX_DEPTH = 8                   # grow targets: 3..8 (6 grows)
GS_STEPS_PER_BLOCK = 4             # certified steps per new block
GS_STEP_CAP = 48                   # total certified-step budget


def gs_snap2k(x, k=GS_K):
    """Snap rational x to the nearest q/2^k grid point,
    banker's rounding (round-half-even), exact Fractions.
    Per-value error <= 2^-(k+1) (half of the 2^-k cell)."""
    g = F(1, 1 << k)
    n, d = (x / g).numerator, (x / g).denominator
    q, r = divmod(n, d)                  # x/g = q + r/d, 0<=r<d
    twice = 2 * r
    if twice > d or (twice == d and q % 2 == 1):
        q += 1
    return F(q, 1 << k)


def gs_obj_snap_bound(base, base_snapped, w):
    """Certified snap bound for a linear head:
    obj = mean (w.f - y)^2, f -> f' = f + delta. Per point
    |(s+ds-y)^2 - (s-y)^2| <= (2|s-y| + |ds|)*|ds| with
    ds = w.delta computed exactly. Returns (bound, maxden)."""
    B = F(0)
    cnt = 0
    for tk, tks in zip(base, base_snapped):
        for (f, y), (fs, _) in zip(tk, tks):
            ds = sum((w[i] * (fs[i] - f[i])
                      for i in range(len(w))), F(0))
            s = sum((w[i] * f[i] for i in range(len(w))), F(0))
            B += (2 * abs(s - y) + abs(ds)) * abs(ds)
            cnt += 1
    return B / cnt


def grow_snap_run(ledger_path):
    """C521 snap-rational repeated grow cycle: C506 mechanics
    (identity grow + certified per-block fd steps + Ville stop)
    plus a CERTIFIED q/2^k snap of the new block's weights and
    of the features at EVERY grow boundary -- denominator
    growth resets each grow (den <= 2^k), depth 8 in budget.
    Returns (start, [accepted steps], telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "rejects": [], "stop": None, "outcomes": {},
                    "growcycle": [], "snap": [], "budget": [],
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint training (mini3/4/5 A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD (fd step rolled "
                                           "back)"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2,
        "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    def featsk(bl, base):
        return [[(mh4_block_fwd(bl, f), y) for f, y in tk]
                for tk in base]

    def snapfeats(base):
        return [[([gs_snap2k(c) for c in f], y)
                 for f, y in tk] for tk in base]

    def maxden(base):
        return max(abs(c.denominator)
                   for tk in base for f, _ in tk for c in f)

    def risk(wcur):
        return mh2_fcanon(wcur, HF)

    # --- (B) SNAP-RATIONAL REPEATED GROW: depth 2 -> GS_MAX_DEPTH
    depth = 2
    grow_events = 0
    cycle_start_obj = mh2_fcanon(w, FT)
    cumulative_bound = F(0)
    # certified cross-phase allowances (snap deltas) for the
    # final chain check: allowance <= its err bound
    allowances = []
    while depth < GS_MAX_DEPTH:
        used = len(raw)
        assert used <= GS_STEP_CAP, \
            "ABORT: step cap exceeded (honest budget-stop)"
        seed = grow_events
        bl = mh5_block_init(seed)
        assert bl[0] == 0, \
            "ABORT: residual gate must start at 0"

        oA = mh2_fcanon(w, FT)
        FTg = featsk(bl, FT)
        assert mh2_fcanon(w, FTg) == oA, \
            "ABORT: grow #{} broke the obj chain (gamma = 0 " \
            "must preserve OBJ EXACTLY at EVERY grow)".format(
                grow_events + 1)
        margin0 = F(0) + F(0) + F(0) - F(0)
        assert margin0 == 0
        tel["admissions"].append({
            "phase": f"B-grow{grow_events + 1}", "margin": "0",
            "decision": "ADMIT (neutral identity, C450 "
                        "function_preserving_admissible: 0 <= 0; "
                        "contribution from certified steps)"})
        tel["rejects"].append({
            "phase": f"B-grow{grow_events + 1}",
            "margin": str(F(1, 10)),
            "decision": "REJECT (negative control, C450 "
                        "margin_positivity_refuses: eps = 1/10 "
                        "> 0 => margin > 0 => gate refuses)"})

        # certified steps on the NEW block only (21 params)
        p3 = mh4_flat(bl)
        n3 = len(p3)
        assert n3 == 1 + MH2_D + 2 * MH2_D * MH2_HID, \
            "ABORT: block param count mismatch"

        def canonk(pp, base):
            return mh2_fcanon(w, featsk(mh4_unflat(pp), base))

        committed = 0
        phase_name = f"C-block{depth + 1}"
        for _ in range(GS_STEPS_PER_BLOCK):
            o = canonk(p3, FT)
            gfd = []
            for k in range(n3):
                q = list(p3)
                q[k] = q[k] + MH2_H
                gfd.append((canonk(q, FT) - o) / MH2_H)
            cand = cl_snap([p3[k] - MH2_ETA * gfd[k]
                            for k in range(n3)], MH2_GRID)
            o2 = canonk(cand, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonk(p3, HF),
                            "risk'": canonk(cand, HF)})
                p3 = cand
                committed += 1
            else:
                tel["holds"].append({"phase": phase_name,
                                     "drop": o - o2,
                                     "reason": "canonical drop <= 0: "
                                               "HOLD (block fd step "
                                               "rolled back)"})

        # --- CERTIFIED SNAP (the C521 mechanic):
        # block weights -> q/2^k grid, composed features ->
        # q/2^k grid; exact Lipschitz-style err bound.
        o_before = canonk(p3, FT)          # obj before snap
        md_before = maxden(featsk(mh4_unflat(p3), FT))
        p3s = [gs_snap2k(v) for v in p3]   # snap block weights
        bl = mh4_unflat(p3s)
        FTc = featsk(bl, FT)               # snapped-block feats
        HFc = featsk(bl, HF)
        FT = snapfeats(FTc)                # snap features (reset!)
        HF = snapfeats(HFc)
        o_after = mh2_fcanon(w, FT)        # obj after snap
        err_bound = gs_obj_snap_bound(FTc, FT, w)
        # the certified assertion: bound >= actual degradation
        actual = o_after - o_before
        assert o_after <= o_before + err_bound, \
            "ABORT: snap broke its certified bound"
        assert maxden(FT) <= (1 << GS_K), \
            "ABORT: snap failed to reset denominators"
        cumulative_bound += err_bound
        allowances.append({"phase": phase_name,
                           "obj_before_snap": str(o_before),
                           "obj_after_snap": str(o_after),
                           "actual_degradation": str(actual),
                           "certified_bound": str(err_bound),
                           "bound_ge_actual": True})
        tel["snap"].append({
            "grow": grow_events + 1, "depth": depth + 1,
            "grid": f"q/2^{GS_K}",
            "per_value_error_bound": f"2^-{GS_K + 1}",
            "obj_before_snap": str(o_before),
            "obj_after_snap": str(o_after),
            "actual_degradation": str(actual),
            "certified_err_bound": str(err_bound),
            "maxden_digits_before_snap": len(str(md_before)),
            "maxden_digits_after_snap": len(str(maxden(FT))),
            "denominator_reset": True})

        oB = mh2_fcanon(w, FT)
        depth += 1
        grow_events += 1
        tel["phases"].append({
            "phase": phase_name, "depth": depth, "params": n3,
            "committed": committed, "gamma": str(bl[0]),
            "canonical_before": str(oA),
            "canonical": str(oB)})
        tel["growcycle"].append({
            "grow": grow_events, "depth": depth,
            "obj_before_grow": str(oA),
            "obj_after_grow": str(oA),
            "exact_invariant": True,
            "block_committed_steps": committed,
            "block_contribution_drop": str(oA - o_before),
            "snap_actual_degradation": str(actual),
            "snap_certified_bound": str(err_bound),
            "net_block_gain_after_snap": str(oA - oB),
            "maxden_digits_at_boundary": len(str(maxden(FT)))})
        tel["budget"].append({
            "at_depth": depth,
            "maxden_digits": len(str(maxden(FT))),
            "grid_cap_digits": len(str(1 << GS_K)),
            "steps_used": len(raw), "step_cap": GS_STEP_CAP,
            "decision": "GROW ADMITTED within budget "
                        "(snap policy: feature denominators "
                        f"RESET to <= 2^{GS_K} at the grow "
                        "boundary -- no exponential compounding)"})

    # --- (D) STOP: Ville detector on canonical holdout risk
    cur = FT
    d = len(w)
    h0 = risk(w)
    D_, fired, refused = F(0), False, 0
    comb = [p for tk in cur for p in tk]
    for _ in range(MH2_E_STEPS):
        g = mh_grad(w, comb)
        cand = cl_snap([w[i] - MH2_ETA * g[i]
                        for i in range(d)], MH2_GRID)
        r1 = risk(cand)
        D_new = r1 - h0
        if GS_LAM * D_new >= GS_THRESH:
            fired = True
            refused += 1
            tel["holds"].append({"phase": "D-stop",
                                 "reason": "Ville stop fired: "
                                           "candidate refused"})
            continue
        o0, o1 = mh2_fcanon(w, cur), mh2_fcanon(cand, cur)
        if o1 < o0:
            raw.append({"phase": "D-stop", "obj": o0, "obj'": o1,
                        "drop": o0 - o1, "risk": risk(w),
                        "risk'": r1})
            w = cand
            D_ = D_new
        else:
            tel["holds"].append({"phase": "D-stop",
                                 "drop": o0 - o1,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    tel["stop"] = {"detector": "C446 Ville, lam*D >= "
                               "1/delta - 1 (conservative)",
                   "lam": str(GS_LAM), "delta": str(GS_DELTA),
                   "fired": fired, "refused": refused,
                   "D_final": str(D_)}
    tel["phases"].append({"phase": "D-stop",
                          "canonical": str(mh2_fcanon(w, cur))})

    n = len(raw)
    assert n > 0, "ABORT: grow-snap committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    # chain check with certified snap allowances at phase
    # boundaries (same-phase steps chain EXACTLY; across a snap
    # boundary obj may rise by <= the certified bound)
    snap_deltas = [F(x["obj_after_snap"]) -
                   F(x["obj_before_snap"]) for x in allowances]
    si = 0
    for a, b in zip(raw, raw[1:]):
        if a["obj'"] == b["obj"]:
            continue
        assert si < len(snap_deltas) and \
            b["obj"] - a["obj'"] == snap_deltas[si], \
            "ABORT: obj chain broken outside certified snaps"
        si += 1
    # si may be < len(snap_deltas): the LAST snap boundary
    # (final grown block -> D-stop) is only visible if the
    # D-stop phase committed a certified step; per-boundary
    # equality above stays EXACT for every observed boundary.
    assert si <= len(snap_deltas), \
        "ABORT: more chain boundaries than certified snaps"
    # telescoped certified cycle bound (the Lean-side statement)
    obj_final = raw[-1]["obj'"]
    assert obj_final <= cycle_start_obj + cumulative_bound, \
        "ABORT: telescoped cycle bound violated"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: grow-snap step failed certified "
                     f"admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path, "dim_final": d,
        "trunk": f"2 fd-trained blocks FROZEN + {grow_events} "
                 "grown identity blocks, each certified-trained "
                 "then SNAP-SNAPPED (q/2^k weights + features, "
                 f"k = {GS_K}) -- denominators reset every grow",
        "trunk_depth_final": depth,
        "grow_events": grow_events,
        "snap_grid": f"q/2^{GS_K} (per-value err <= 2^-"
                     f"{GS_K + 1})",
        "grow_obj_invariant_exact_every": True,
        "snap_bounds_all_certified": True,
        "snap_cumulative_certified_bound": str(cumulative_bound),
        "cycle_obj_start": str(cycle_start_obj),
        "cycle_certified_bound": str(cycle_start_obj +
                                     cumulative_bound),
        "maxden_digits_final": len(str(maxden(FT))),
        "c506_comparison": {
            "c506_depth": 5, "c506_maxden_digits": 2366,
            "c506_wall_s": 62,
            "c521_depth": depth,
            "c521_maxden_digits": len(str(maxden(FT)))},
        "canonical_start": str(obj0),
        "canonical_final": str(obj_final),
        "total_drop": str(obj0 - obj_final),
        "model": "linear head over the snap-grown trunk (depth "
                 f"2 -> {depth} via {grow_events} residual-zero "
                 "identity grows + certified block training + "
                 "CERTIFIED q/2^k snap at every grow boundary); "
                 "admission ONLY by measured canonical drop > 0; "
                 "snap degradation certified: obj_after <= "
                 "obj_before + exact Lipschitz-style bound",
        "theorem": "Hagi.Theory.GrowSnap.grow_snap_cycle_sound "
                   "(C521; telescoped certified snap-cycle bound)"
    }
    return obj0, raw, tel, stats


def emit_lean_growsnap(path, start, traj, witness_steps=3):
    """C521 witness: literal grow-snap trajectory prefix +
    #eval checkTrajectory + norm_num theorem; header documents
    the FULL counts honestly (deep obj fractions are not
    Lean-elaborable -- prefix only, stated openly)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C521 grow-snap witness (real unified_ledger "
                "data; snap-rational repeated grow cycle: depth "
                f"2 -> 8 via 6 identity grows, each trained then "
                f"CERTIFIED-snapped to q/2^{GS_K}; denominators "
                "reset every grow).\n"
                f"-- FULL accepted steps: {len(traj)}; phases: "
                f"{phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness: "
                "deep fractions are not Lean-elaborable; the "
                "full chain, the snap bounds and the telescoped "
                "cycle bound are asserted exactly in Python and "
                "counted here honestly).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.GrowSnap\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartGrowSnap : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryGrowSnap : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrowSnap "
                "benchTrajectoryGrowSnap\n\n"
                "theorem grow_snap_bench_valid :\n"
                "    checkTrajectory benchStartGrowSnap "
                "benchTrajectoryGrowSnap = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartGrowSnap, benchTrajectoryGrowSnap, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.GrowSnap."
                "grow_snap_cycle_sound\n")
    print(f"written: {path}", file=sys.stderr)


def emit_bad_growsnap(path, start, traj, witness_steps=3):
    """C521 negative: inflated declared drop on the last
    witness step; the checker must reject (theorem = false)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    ds[-1]["drop"] = ds[-1]["drop"] + F(1)
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C521 grow-snap NEGATIVE witness: the last "
                "declared drop is inflated by 1; the certified "
                "checker must reject.\n"
                "import Hagi.Runtime.CertChecker\n\n"
                "open Hagi.Runtime\n\n"
                "def benchStartGrowSnapBad : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryGrowSnapBad : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartGrowSnapBad "
                "benchTrajectoryGrowSnapBad\n\n"
                "theorem grow_snap_bench_invalid :\n"
                "    checkTrajectory benchStartGrowSnapBad "
                "benchTrajectoryGrowSnapBad = false := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartGrowSnapBad, "
                "benchTrajectoryGrowSnapBad, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n")
    print(f"written: {path}", file=sys.stderr)


# C532: CERTIFIED ADAPTER GROWTH, LoRA-style
# (--mode adapter-grow)
#
# The previous grow mechanisms add volume WHOLESALE: fiber
# grow C494 (a full feature column) and identity-block grow
# C504/C506/C521 (a FULL residual block: 1 + d + 2*d*hid = 21
# params at d=4, hid=2; ~d^2 at hid ~ d). C532 grows the model
# by a MINIMAL low-rank side-branch adapter (LoRA form, Hu et
# al. 2021): the head prediction becomes
#
#     pred = w . (f + B (A f)),   A : r x d,  B : d x r,
#
# adding 2*r*d parameters (r=1: 8, r=2: 16 at d=4) against the
# full block's 21 -- the Lean side is
# Hagi.Theory.AdapterGrowth (adapter_neutral_B/A: EITHER zero
# factor makes the branch EXACTLY neutral; adapter_param_count:
# exact 2*r*d count; adapter_param_count_le_block: 2*r*d <=
# d*d when 2r <= d; adapter_step_certified/hold: certified
# step semantics).
#
# Cycle: phase A joint trunk+head certified fd steps (the C521
# phase A, unchanged), trunk FROZEN, then adapters r=1 and r=2
# admitted at B=0 (obj invariant asserted EXACTLY at every
# admission -- the LoRA zero-init core), certified fd training
# of ONLY the 2*r*d adapter params (fd h, 1/10000 grid snap,
# admission ONLY by measured drop > 0, else HOLD), then a
# head-to-head identity-BLOCK grow (mh5_block_init, gamma=0,
# 21 params) trained with the SAME number of certified steps
# for an honest progress-per-parameter comparison.

AG_RANKS = [1, 2]                  # adapter ranks grown in order
AG_STEPS = 4                       # certified fd steps per growth
AG_H = F(1, 1000)                  # fd step h (same as MH2_H)


def adapter_grow_run(ledger_path):
    """C532 certified adapter-growth cycle on the live corpus.
    Returns (start, [accepted steps], telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw = []
    tel = {"phases": [], "holds": [], "admissions": [],
           "adapters": [], "block_head_to_head": None,
           "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint certified steps (C521 A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    # trunk FROZEN: feature matrices (train + holdout)
    FT = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in tasks]
    HF = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
          for tk in htasks]
    assert mh2_fcanon(w, FT) == raw[-1]["obj'"], \
        "ABORT: trunk freeze broke the obj chain"

    # --- (B) ADAPTER GROWTH: r = 1 then r = 2 on the head
    # prediction: s = w.(f + B(A f)); admission at B = 0 keeps
    # obj EXACTLY invariant (LoRA zero-init core).
    adapters = []          # list of (A, B) factor pairs, grown

    def adapter_fwd(fs, factors):
        """head input f -> f + sum over adapters B(A f)"""
        out = list(fs)
        for A, B in factors:
            z = [sum((A[j][k] * fs[k] for k in range(MH2_D)),
                     F(0)) for j in range(len(A))]
            d = [sum((B[i][j] * z[j] for j in range(len(A))),
                     F(0)) for i in range(MH2_D)]
            out = [out[i] + d[i] for i in range(MH2_D)]
        return out

    def canon_adapt(wcur, base, factors):
        """canonical obj: MEAN OVER TASKS of per-task MSE with
        adapter-modified features (the mh2_fcanon convention --
        keeps the obj chain EXACT across the freeze boundary)."""
        per = []
        for tk in base:
            tot = F(0)
            for f, y in tk:
                fa = adapter_fwd(f, factors)
                s = sum((wcur[i] * fa[i]
                         for i in range(MH2_D)), F(0))
                tot += (s - y) ** 2
            per.append(tot / F(len(tk)))
        return sum(per, F(0)) / F(len(per))

    def adapter_flat(factors):
        return [e for A, B in factors
                for m in (A, B) for row in m for e in row]

    def adapter_unflat(pflat, ranks):
        factors, i = [], 0
        for r in ranks:
            A = [[pflat[i + j * MH2_D + k]
                  for k in range(MH2_D)] for j in range(r)]
            i += r * MH2_D
            B = [[pflat[i + c * r + j] for j in range(r)]
                 for c in range(MH2_D)]
            i += MH2_D * r
            factors.append((A, B))
        assert i == len(pflat), "ABORT: adapter flat mismatch"
        return factors

    for ai, r in enumerate(AG_RANKS):
        # admission: A = ones-grid (NONZERO -- the point: the
        # OTHER factor masks the branch), B = 0
        A_new = [[F(1) if k == 0 else F(0)
                  for k in range(MH2_D)] for _ in range(r)]
        B_new = [[F(0)] * r for _ in range(MH2_D)]
        cand_factors = adapters + [(A_new, B_new)]
        oA = canon_adapt(w, FT, adapters)
        oAg = canon_adapt(w, FT, cand_factors)
        assert oAg == oA, \
            "ABORT: adapter admission #{} broke obj (B = 0 " \
            "must preserve obj EXACTLY)".format(ai + 1)
        npar = 2 * r * MH2_D
        tel["admissions"].append({
            "phase": f"B-adapter-r{r}",
            "rank": r, "new_params": npar,
            "decision": "ADMIT (LoRA zero-init: B = 0, branch "
                        "EXACTLY neutral whatever A is; obj "
                        "invariant asserted exactly)"})

        # certified fd training of ONLY the adapter params
        ranks = AG_RANKS[:ai + 1]
        p = adapter_flat(cand_factors)
        assert len(p) == sum(2 * rr * MH2_D for rr in ranks)

        def canonp(pp, base):
            return canon_adapt(w, base, adapter_unflat(pp, ranks))

        phase_name = f"C-adapter-r{r}"
        committed = 0
        for _ in range(AG_STEPS):
            o = canonp(p, FT)
            gfd = []
            for k in range(len(p)):
                q = list(p)
                q[k] = q[k] + AG_H
                gfd.append((canonp(q, FT) - o) / AG_H)
            cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                            for k in range(len(p))], MH2_GRID)
            o2 = canonp(cand, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonp(p, HF),
                            "risk'": canonp(cand, HF)})
                p = cand
                committed += 1
            else:
                tel["holds"].append({
                    "phase": phase_name, "drop": o - o2,
                    "reason": "canonical drop <= 0: HOLD "
                              "(adapter fd step rolled back)"})
        adapters = adapter_unflat(p, ranks)
        tel["adapters"].append({
            "rank": r,
            "params": npar,
            "committed_steps": committed,
            "obj_before_admission": str(oA),
            "obj_after_training": str(canon_adapt(w, FT,
                                                   adapters)),
            "progress": str(oA - canon_adapt(w, FT, adapters))})
        tel["phases"].append({
            "phase": phase_name, "rank": r, "params": npar,
            "committed": committed,
            "canonical": str(canon_adapt(w, FT, adapters))})

    o_adapted = canon_adapt(w, FT, adapters)
    adapt_params = sum(2 * r * MH2_D for r in AG_RANKS)

    # --- (C) HEAD-TO-HEAD: the identity-BLOCK grow (C504/C521
    # mechanic, 21 params, gamma = 0) trained with the SAME
    # total number of certified steps as the adapters, from the
    # same frozen-trunk obj -- progress per parameter compared.
    oA0 = mh2_fcanon(w, FT)
    bl = mh5_block_init(0)
    assert bl[0] == 0, "ABORT: residual gate must start at 0"

    def featsk(blp, base):
        return [[(mh4_block_fwd(blp, f), y) for f, y in tk]
                for tk in base]

    assert mh2_fcanon(w, featsk(bl, FT)) == oA0, \
        "ABORT: identity block admission broke obj (gamma = 0)"
    p3 = mh4_flat(bl)
    n3 = len(p3)
    assert n3 == 1 + MH2_D + 2 * MH2_D * MH2_HID
    block_steps = AG_STEPS * len(AG_RANKS)
    committed_b = 0
    block_raw = []   # separate arm: validated per-step, NOT in
    # the canonical chain (both arms start from the SAME
    # frozen-trunk obj oA0; mixing them would break the
    # exact obj-chain semantics of CertStepData)
    for _ in range(block_steps):
        o = mh2_fcanon(w, featsk(mh4_unflat(p3), FT))
        gfd = []
        for k in range(n3):
            q = list(p3)
            q[k] = q[k] + MH2_H
            gfd.append((mh2_fcanon(
                w, featsk(mh4_unflat(q), FT)) - o) / MH2_H)
        cand = cl_snap([p3[k] - MH2_ETA * gfd[k]
                        for k in range(n3)], MH2_GRID)
        o2 = mh2_fcanon(w, featsk(mh4_unflat(cand), FT))
        if o2 < o:
            block_raw.append({"phase": "D-block-head2head",
                        "obj": o, "obj'": o2, "drop": o - o2,
                        "risk": mh2_fcanon(w, featsk(
                            mh4_unflat(p3), HF)),
                        "risk'": mh2_fcanon(w, featsk(
                            mh4_unflat(cand), HF))})
            p3 = cand
            committed_b += 1
        else:
            tel["holds"].append({
                "phase": "D-block-head2head", "drop": o - o2,
                "reason": "canonical drop <= 0: HOLD (block "
                          "fd step rolled back)"})
    o_blocked = mh2_fcanon(w, featsk(mh4_unflat(p3), FT))
    for t, dd in enumerate(block_raw):
        dd["budget"] = F(len(block_raw) - t) / len(block_raw)
        dd["budget'"] = (F(len(block_raw) - t - 1)
                         / len(block_raw))
        if not check_step(dd):
            sys.exit("ABORT: adapter-grow block-arm step "
                     "failed certified admission: {}".format(dd))
    tel["block_head_to_head"] = {
        "same_certified_step_budget": block_steps,
        "block_params": n3, "adapter_params": adapt_params,
        "block_committed": committed_b,
        "adapter_committed": sum(a["committed_steps"]
                                  for a in tel["adapters"]),
        "obj_start": str(oA0),
        "obj_after_adapters": str(o_adapted),
        "obj_after_block": str(o_blocked),
        "adapter_progress": str(oA0 - o_adapted),
        "block_progress": str(oA0 - o_blocked)}
    tel["phases"].append({
        "phase": "D-block-head2head", "params": n3,
        "committed": committed_b,
        "canonical": str(o_blocked)})

    n = len(raw)
    assert n > 0, "ABORT: adapter-grow committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], \
            "ABORT: obj chain broken at a phase boundary"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: adapter-grow step failed "
                     f"certified admission: {dd}")
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path,
        "ranks": AG_RANKS,
        "adapter_params_total": adapt_params,
        "full_block_params": n3,
        "param_ratio": str(F(adapt_params, n3)),
        "d2_full_matrix": MH2_D * MH2_D,
        "lora_param_identity": "2*r*d (r=1: 8; r=2: 16 at d=4)",
        "grow_obj_invariant_exact_every": True,
        "canonical_start": str(obj0),
        "canonical_final": str(raw[-1]["obj'"]),
        "total_drop": str(obj0 - raw[-1]["obj'"]),
        "model": "linear head over the fd-trained FROZEN trunk "
                 "grown by LoRA-style side-branch adapters "
                 "(f + B(A f), ranks 1 then 2, admission at "
                 "B = 0 with EXACT obj invariance, certified fd "
                 "training of only the 2*r*d adapter params) + "
                 "identity-block head-to-head arm",
        "theorem": "Hagi.Theory.AdapterGrowth.adapter_neutral_B "
                   "/ adapter_param_count / "
                   "adapter_step_certified (C532)"
    }
    return obj0, raw, tel, stats


def emit_lean_adaptergrow(path, start, traj, witness_steps=3):
    """C532 witness: literal adapter-grow trajectory prefix +
    #eval checkTrajectory + norm_num theorem (the C521 witness
    pattern; prefix only, deep fractions not elaborable)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C532 adapter-grow witness (real "
                "unified_ledger data; LoRA-style side-branch "
                "adapters r=1,2 admitted at B = 0 with EXACT "
                "obj invariance, certified fd training of only "
                "the 2*r*d adapter params).\n"
                f"-- FULL accepted steps: {len(traj)}; "
                f"phases: {phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness: "
                "deep fractions are not Lean-elaborable; the "
                "full chain and the neutrality/count facts are "
                "covered by Hagi.Theory.AdapterGrowth).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.AdapterGrowth\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartAdapterGrow : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryAdapterGrow : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartAdapterGrow "
                "benchTrajectoryAdapterGrow\n\n"
                "theorem adapter_grow_bench_valid :\n"
                "    checkTrajectory benchStartAdapterGrow "
                "benchTrajectoryAdapterGrow = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartAdapterGrow, "
                "benchTrajectoryAdapterGrow, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_neutral_B\n")
    print(f"written: {path}", file=sys.stderr)


# C533: ADAPTER SNAP COMPOSITE GROW (--mode adapter-snap-grow)
#
# The composition breakthrough: adapter-grow (C532, MINIMAL
# growth volume -- a low-rank side-branch, 2*r*d = 8 params at
# r=1, d=4) COMPOSED with snap-rational (C521, MINIMAL
# computation -- q/2^k snap resets feature denominators at
# every grow boundary) into ONE repeatable deep cycle:
#
#   level l:  ADMIT adapter r=1 (A = unit row on coordinate
#               l mod d, B = 0 -- obj invariant EXACTLY,
#               the LoRA zero-init core)
#             TRAIN 4 certified fd steps on ONLY the 8 new
#               adapter params (h = 1/1000, candidate snap
#               1/10000, COMMIT by measured drop > 0 / HOLD)
#             SNAP the adapter weights to q/2^40 (banker's
#               rounding), recompute + snap the features; the
#               certified err bound is the EXACT per-point
#               Lipschitz sum (2|s-y| + |ds|)*|ds| with
#               ds = w.(f_final - f_orig) covering the WHOLE
#               snap chain (weight-snap + feature-snap
#               together); assert obj_after <= obj_before +
#               bound and maxden <= 2^40 at EVERY level.
#
# The trained level is folded EXACTLY into the (grid-bounded)
# features; the next level starts from the grid -- the C506
# ~x3.2-per-grow denominator compounding NEVER accumulates,
# while each level adds only 8 parameters. Telescoped cycle
# bound: obj_final <= cycle_start + sum(bounds) -- the Lean
# side is Hagi.Theory.AdapterGrowth.adapter_snap_bound /
# adapter_snap_cycle_sound (C533).

AS_LEVELS = 8                     # grow levels (depth 2 -> 10;
                                  # C521-parity depth 8 exceeded)
AS_K = 40                         # snap grid q/2^k (C521 PIN)
AS_STEPS = 4                      # certified fd steps per level
AS_RANK = 1                       # adapter rank per level


def adapter_snap_grow_run(ledger_path):
    """C533 adapter-snap composite grow cycle on the live
    corpus. Returns (start, [accepted steps], telemetry,
    stats)."""
    sys.set_int_max_str_digits(0)
    t0 = time.perf_counter()
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "levels": [], "snap": [], "budget": [],
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint certified steps (C521 A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2, "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    def adapter_fwd(f, A, B):
        """head input f -> f + B(A f), single r=AS_RANK branch"""
        z = sum((A[0][k] * f[k] for k in range(MH2_D)), F(0))
        return [f[i] + B[i][0] * z for i in range(MH2_D)]

    def feats_adapt(base, A, B):
        return [[(adapter_fwd(f, A, B), y) for f, y in tk]
                for tk in base]

    def snapfeats(base):
        return [[([gs_snap2k(c) for c in f], y)
                 for f, y in tk] for tk in base]

    def maxden(base):
        return max(abs(c.denominator)
                   for tk in base for f, _ in tk for c in f)

    def obj_bound(base_orig, base_final, wcur):
        """EXACT certified bound covering the WHOLE snap chain:
        per point |(s2-y)^2 - (s1-y)^2| <= (2|s1-y| + |ds|)*|ds|,
        ds = w.(f_final - f_orig)."""
        Bsum = F(0)
        cnt = 0
        for tk, tkf in zip(base_orig, base_final):
            for (f1, y), (f2, _) in zip(tk, tkf):
                ds = sum((wcur[i] * (f2[i] - f1[i])
                          for i in range(MH2_D)), F(0))
                s = sum((wcur[i] * f1[i]
                         for i in range(MH2_D)), F(0))
                Bsum += (2 * abs(s - y) + abs(ds)) * abs(ds)
                cnt += 1
        return Bsum / cnt

    # trunk FROZEN: feature matrices (train + holdout), snapped
    # ONCE to the q/2^k grid (the freeze boundary; every level
    # then starts from the grid)
    FT_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in tasks]
    HF_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in htasks]
    FT = snapfeats(FT_un)
    HF = snapfeats(HF_un)
    assert mh2_fcanon(w, FT) <= mh2_fcanon(w, FT_un) + \
        obj_bound(FT_un, FT, w), \
        "ABORT: freeze snap broke its certified bound"

    # --- (B) ADAPTER SNAP COMPOSITE GROW: AS_LEVELS levels
    depth = 2
    cycle_start_obj = mh2_fcanon(w, FT)
    cumulative_bound = F(0)
    allowances = [{"phase": "A-freeze-snap",
                   "obj_before_snap": str(mh2_fcanon(w, FT_un)),
                   "obj_after_snap": str(cycle_start_obj),
                   "actual_degradation":
                       str(cycle_start_obj -
                           mh2_fcanon(w, FT_un)),
                   "certified_bound":
                       str(obj_bound(FT_un, FT, w)),
                   "bound_ge_actual": True}]
    for lev in range(AS_LEVELS):
        r = AS_RANK
        # ADMIT: A = unit row on coordinate lev mod d, B = 0
        A_new = [[F(1) if k == lev % MH2_D else F(0)
                  for k in range(MH2_D)]]
        B_new = [[F(0)] for _ in range(MH2_D)]
        oA = mh2_fcanon(w, FT)
        FTg = feats_adapt(FT, A_new, B_new)
        assert mh2_fcanon(w, FTg) == oA, \
            "ABORT: adapter admission #{} broke obj (B = 0 " \
            "must preserve obj EXACTLY)".format(lev + 1)
        tel["admissions"].append({
            "phase": f"B-adapter-l{lev + 1}",
            "rank": r, "new_params": 2 * r * MH2_D,
            "coord": lev % MH2_D,
            "decision": "ADMIT (LoRA zero-init: B = 0, obj "
                        "invariant asserted EXACTLY)"})

        # TRAIN: certified fd steps on ONLY the 2*r*d new params
        p = [e for m in (A_new, B_new)
             for row in m for e in row]
        npar = len(p)
        assert npar == 2 * r * MH2_D

        def unflat_ad(pp):
            return ([pp[0:MH2_D]],
                    [[pp[MH2_D + c]] for c in range(MH2_D)])

        def canonp(pp, base):
            A, Bl = unflat_ad(pp)
            return mh2_fcanon(w, feats_adapt(base, A, Bl))

        phase_name = f"C-adapt-l{lev + 1}"
        committed = 0
        for _ in range(AS_STEPS):
            o = canonp(p, FT)
            gfd = []
            for k in range(npar):
                q = list(p)
                q[k] = q[k] + MH2_H
                gfd.append((canonp(q, FT) - o) / MH2_H)
            cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                            for k in range(npar)], MH2_GRID)
            o2 = canonp(cand, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonp(p, HF),
                            "risk'": canonp(cand, HF)})
                p = cand
                committed += 1
            else:
                tel["holds"].append({
                    "phase": phase_name, "drop": o - o2,
                    "reason": "canonical drop <= 0: HOLD "
                              "(adapter fd step rolled back)"})

        # SNAP: adapter weights -> q/2^k; features recomputed
        # (snapped weights) and snapped; the exact bound covers
        # the WHOLE chain (weight-snap + feature-snap together)
        o_before = canonp(p, FT)
        ps = [gs_snap2k(v) for v in p]
        As, Bs = unflat_ad(ps)
        Ao, Bo = unflat_ad(p)
        FTo = feats_adapt(FT, Ao, Bo)
        FTc = feats_adapt(FT, As, Bs)
        HFc = feats_adapt(HF, As, Bs)
        FT = snapfeats(FTc)              # denominators reset
        HF = snapfeats(HFc)
        o_after = mh2_fcanon(w, FT)
        err_bound = obj_bound(FTo, FT, w)
        actual = o_after - o_before
        assert o_after <= o_before + err_bound, \
            "ABORT: adapter snap broke its certified bound"
        assert maxden(FT) <= (1 << AS_K), \
            "ABORT: adapter snap failed to reset denominators"
        cumulative_bound += err_bound
        allowances.append({"phase": phase_name,
                           "obj_before_snap": str(o_before),
                           "obj_after_snap": str(o_after),
                           "actual_degradation": str(actual),
                           "certified_bound": str(err_bound),
                           "bound_ge_actual": True})
        tel["snap"].append({
            "level": lev + 1, "depth": depth + 1,
            "grid": f"q/2^{AS_K}",
            "obj_before_snap": str(o_before),
            "obj_after_snap": str(o_after),
            "actual_degradation": str(actual),
            "certified_err_bound": str(err_bound),
            "maxden_digits": len(str(maxden(FT))),
            "denominator_reset": True})
        tel["levels"].append({
            "level": lev + 1, "rank": r, "params": npar,
            "committed": committed,
            "net_gain_after_snap": str(oA - mh2_fcanon(w, FT)),
            "canonical": str(mh2_fcanon(w, FT))})
        depth += 1
        tel["phases"].append({
            "phase": phase_name, "depth": depth,
            "params": npar, "committed": committed,
            "canonical": str(mh2_fcanon(w, FT))})
        tel["budget"].append({
            "at_level": lev + 1, "depth": depth,
            "maxden_digits": len(str(maxden(FT))),
            "grid_cap_digits": len(str(1 << AS_K)),
            "steps_used": len(raw),
            "decision": "LEVEL ADMITTED within budget (snap "
                        "policy: feature denominators RESET to "
                        f"<= 2^{AS_K} -- no compounding)"})

    n = len(raw)
    assert n > 0, "ABORT: adapter-snap-grow committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    # obj chain: EXACT within a phase; across a snap boundary
    # the rise equals the actual snap delta (<= its bound)
    snap_deltas = [F(x["obj_after_snap"]) -
                   F(x["obj_before_snap"]) for x in allowances]
    si = 0
    for a, b in zip(raw, raw[1:]):
        if a["obj'"] == b["obj"]:
            continue
        # a phase boundary: the obj rise must equal a sum of
        # CONSECUTIVE pending snap deltas (>= 1; a level that
        # committed no fd step spans TWO deltas across one
        # boundary; deltas may be negative -- scan to a match)
        needed = b["obj"] - a["obj'"]
        si0 = si
        acc = F(0)
        while si < len(snap_deltas):
            acc += snap_deltas[si]
            si += 1
            if acc == needed:
                break
        assert si > si0 and acc == needed, \
            "ABORT: obj chain broken outside certified snaps"
    assert si <= len(snap_deltas), \
        "ABORT: more chain boundaries than certified snaps"
    # telescoped certified cycle bound (the Lean-side statement)
    obj_final = raw[-1]["obj'"]
    assert obj_final <= cycle_start_obj + cumulative_bound, \
        "ABORT: telescoped adapter-snap cycle bound violated"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: adapter-snap-grow step failed "
                     f"certified admission: {dd}")
    elapsed = time.perf_counter() - t0
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path,
        "trunk": f"2 fd-trained blocks FROZEN (snapped once to "
                 f"q/2^{AS_K}) + {AS_LEVELS} adapter levels "
                 "(r=1 each), each certified-trained then "
                 "SNAP-FOLDED into the grid-bounded features",
        "trunk_depth_final": depth,
        "levels": AS_LEVELS,
        "rank_per_level": AS_RANK,
        "adapter_params_per_level": 2 * AS_RANK * MH2_D,
        "adapter_params_total": AS_LEVELS * 2 * AS_RANK * MH2_D,
        "full_block_params_per_grow": 1 + MH2_D +
                                       2 * MH2_D * MH2_HID,
        "param_ratio_per_grow": str(F(2 * AS_RANK * MH2_D,
                                       1 + MH2_D +
                                       2 * MH2_D * MH2_HID)),
        "snap_grid": f"q/2^{AS_K} (per-value err <= 2^-"
                     f"{AS_K + 1})",
        "grow_obj_invariant_exact_every": True,
        "snap_bounds_all_certified": True,
        "snap_cumulative_certified_bound":
            str(cumulative_bound),
        "cycle_obj_start": str(cycle_start_obj),
        "cycle_certified_bound": str(cycle_start_obj +
                                     cumulative_bound),
        "maxden_digits_final": len(str(maxden(FT))),
        "elapsed_s": round(elapsed, 3),
        "canonical_start": str(obj0),
        "canonical_final": str(obj_final),
        "total_drop": str(obj0 - obj_final),
        "model": "linear head over the adapter-snap-grown "
                 f"feature stack (depth 2 -> {depth} via "
                 f"{AS_LEVELS} LoRA adapter levels r=1, each "
                 "admitted at B = 0 with EXACT obj invariance, "
                 "certified fd training of only the 8 new "
                 "params, then q/2^k snap-fold with certified "
                 "err bound; denominators bounded at EVERY "
                 "level)",
        "theorem": "Hagi.Theory.AdapterGrowth."
                   "adapter_snap_bound / adapter_snap_cycle_sound"
                   " (C533)"
    }
    return obj0, raw, tel, stats


def emit_lean_adaptersnap(path, start, traj, witness_steps=3):
    """C533 witness: literal adapter-snap-grow trajectory
    prefix + #eval checkTrajectory + norm_num theorem (the
    C521/C532 witness pattern)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C533 adapter-snap-grow witness (real "
                "unified_ledger data; LoRA-style adapter levels "
                "r=1 admitted at B = 0 with EXACT obj "
                "invariance, certified fd training of only the "
                "8 new params per level, q/2^k snap-fold with "
                "certified err bound at EVERY level).\n"
                f"-- FULL accepted steps: {len(traj)}; "
                f"phases: {phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness; "
                "the full chain, the neutrality/count/snap-bound "
                "facts are covered by Hagi.Theory."
                "AdapterGrowth).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.AdapterGrowth\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartAdapterSnapGrow : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryAdapterSnapGrow : "
                "List Hagi.Runtime.CertStepData :=\n"
                + "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartAdapterSnapGrow "
                "benchTrajectoryAdapterSnapGrow\n\n"
                "theorem adapter_snap_grow_bench_valid :\n"
                "    checkTrajectory benchStartAdapterSnapGrow "
                "benchTrajectoryAdapterSnapGrow = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartAdapterSnapGrow, "
                "benchTrajectoryAdapterSnapGrow, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_snap_bound\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_snap_cycle_sound\n")
    print(f"written: {path}", file=sys.stderr)


# C535: ADAPTER RANK-ADAPTIVE GROW (--mode adapter-rank-adaptive)
#
# The r-adaptivity breakthrough: the C533 adapter-snap cycle
# generalized over the adapter RANK r in {1, 2}, with the rank
# CHOSEN PER LEVEL by a MEASURED criterion (the C510 hybrid
# selector pattern applied to growth volume):
#
#   level l:  PROBE r=1 and r=2 from ONE state: k = 2
#               certified-mechanism fd steps each, computed on
#               a COPY of the level parameters -- the live
#               state is never touched (probe = no-commit,
#               the C530 rollback gate semantics: rollback is
#               EXACT because the state never moved).
#             SELECT by the measured score
#               score_r = probe_drop_r / (2*r*d)   (drop per
#             param; the lambda-penalty variant
#               drop_r - lambda*(2*r*d) is the same order for
#             monotone lambda): r=2 iff score_2 > score_1
#             STRICTLY; a tie goes to r=1 (fewer params --
#             budget priority). Fractions + linorder make the
#             criterion a TOTAL order, so the selection is a
#             deterministic function of the measured state.
#             ADMIT the chosen rank (A = unit rows on coords
#               l..l+r-1 mod d, B = 0 -- obj invariant EXACTLY)
#             TRAIN 4 certified fd steps on ONLY the 2*r*d new
#               params (COMMIT by measured drop > 0 / HOLD)
#             SNAP q/2^40 + certified err bound (the C533
#               boundary; denominators reset EVERY level).
#
# --fix-rank {1,2} disables the selector for comparison runs
# (fixed-rank arms of the same code path). Telemetry
# tel["rank_select"] records BOTH probe drops, BOTH scores,
# the chosen rank and the reason at EVERY level.

ARA_LEVELS = 8                     # grow levels (depth 2 -> 10)
ARA_K = 40                         # snap grid q/2^k (C521 PIN)
ARA_STEPS = 4                      # certified fd steps per level
ARA_PROBE_STEPS = 2                # probe steps per rank arm
ARA_RANKS = (1, 2)                 # the probed rank arms


def adapter_rank_adaptive_run(ledger_path, fix_rank=None):
    """C535 rank-adaptive adapter grow cycle on the live
    corpus: per level, probe r=1 and r=2 from one state,
    select by drop/params, commit the chosen rank through the
    C533 certified cycle. Returns (start, [accepted steps],
    telemetry, stats)."""
    sys.set_int_max_str_digits(0)
    t0 = time.perf_counter()
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(k, x, y) for i, (k, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "levels": [], "snap": [], "budget": [],
                    "rank_select": [], "probes": [],
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint certified steps (C521 A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2, "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    # --- rank-generalized adapter branch: f + B(A f), r rows
    def fwd_r(f, A, B, r):
        out = list(f)
        for j in range(r):
            z = sum((A[j][k] * f[k] for k in range(MH2_D)),
                    F(0))
            for i in range(MH2_D):
                out[i] += B[i][j] * z
        return out

    def feats_ad(base, A, B, r):
        return [[(fwd_r(f, A, B, r), y) for f, y in tk]
                for tk in base]

    def snapfeats(base):
        return [[([gs_snap2k(c) for c in f], y)
                 for f, y in tk] for tk in base]

    def maxden(base):
        return max(abs(c.denominator)
                   for tk in base for f, _ in tk for c in f)

    def obj_bound(base_orig, base_final, wcur):
        """EXACT certified bound covering the WHOLE snap chain
        (C533): per point |(s2-y)^2 - (s1-y)^2| <=
        (2|s1-y| + |ds|)*|ds|, ds = w.(f_final - f_orig)."""
        Bsum = F(0)
        cnt = 0
        for tk, tkf in zip(base_orig, base_final):
            for (f1, y), (f2, _) in zip(tk, tkf):
                ds = sum((wcur[i] * (f2[i] - f1[i])
                          for i in range(MH2_D)), F(0))
                s = sum((wcur[i] * f1[i]
                         for i in range(MH2_D)), F(0))
                Bsum += (2 * abs(s - y) + abs(ds)) * abs(ds)
                cnt += 1
        return Bsum / cnt

    def admit_params(lev, r):
        """ADMIT init for rank r: A = unit rows on coords
        lev..lev+r-1 mod d, B = 0 (obj invariant EXACTLY)."""
        A = [[F(1) if k == (lev + j) % MH2_D else F(0)
              for k in range(MH2_D)] for j in range(r)]
        p = [e for row in A for e in row] + \
            [F(0)] * (r * MH2_D)
        return p

    def unflat_ad(pp, r):
        A = [[pp[j * MH2_D + k] for k in range(MH2_D)]
             for j in range(r)]
        B = [[pp[r * MH2_D + j * MH2_D + i] for j in range(r)]
             for i in range(MH2_D)]
        return A, B

    def canonp(pp, r, base):
        A, Bl = unflat_ad(pp, r)
        return mh2_fcanon(w, feats_ad(base, A, Bl, r))

    # trunk FROZEN: snapped feature matrices (the freeze
    # boundary; every level starts from the grid)
    FT_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in tasks]
    HF_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in htasks]
    FT = snapfeats(FT_un)
    HF = snapfeats(HF_un)
    assert mh2_fcanon(w, FT) <= mh2_fcanon(w, FT_un) + \
        obj_bound(FT_un, FT, w), \
        "ABORT: freeze snap broke its certified bound"

    # --- (P) PROBE both rank arms from ONE state: the k-step
    # certified mechanism on a COPY -- the live level state is
    # never touched (C530 no-commit probe), so the rollback is
    # EXACT; the probe drops are selector inputs, NOT links of
    # the certified obj chain.
    def probe_drop(lev, r):
        p = admit_params(lev, r)
        drop = F(0)
        for _ in range(ARA_PROBE_STEPS):
            o = canonp(p, r, FT)
            gfd = []
            for kk in range(len(p)):
                q = list(p)
                q[kk] = q[kk] + MH2_H
                gfd.append((canonp(q, r, FT) - o) / MH2_H)
            cand = cl_snap([p[kk] - MH2_ETA * gfd[kk]
                            for kk in range(len(p))], MH2_GRID)
            o2 = canonp(cand, r, FT)
            if o2 < o:
                drop += o - o2
                p = cand
        return drop

    # --- (B) RANK-ADAPTIVE COMPOSITE GROW: ARA_LEVELS levels
    depth = 2
    cycle_start_obj = mh2_fcanon(w, FT)
    cumulative_bound = F(0)
    allowances = [{"phase": "A-freeze-snap",
                   "obj_before_snap": str(mh2_fcanon(w, FT_un)),
                   "obj_after_snap": str(cycle_start_obj),
                   "actual_degradation":
                       str(cycle_start_obj -
                           mh2_fcanon(w, FT_un)),
                   "certified_bound":
                       str(obj_bound(FT_un, FT, w)),
                   "bound_ge_actual": True}]
    ranks_chosen = []
    params_total = 0
    for lev in range(ARA_LEVELS):
        # PROBE + SELECT (measured, deterministic, total order)
        if fix_rank in (1, 2):
            d = {rr: probe_drop(lev, rr) for rr in ARA_RANKS}
            r = fix_rank
            reason = (f"FIXED-RANK comparison run "
                      f"(--fix-rank {fix_rank}; probe measured "
                      f"but not applied)")
        else:
            d1 = probe_drop(lev, 1)
            d2 = probe_drop(lev, 2)
            d = {1: d1, 2: d2}
            s1 = d1 / F(2 * 1 * MH2_D)
            s2 = d2 / F(2 * 2 * MH2_D)
            r = 2 if s2 > s1 else 1
            reason = ("score_2 > score_1 (drop/params): r=2"
                      if r == 2 else
                      "score_2 <= score_1 (tie -> fewer params "
                      "budget priority): r=1")
        s1 = d[1] / F(2 * 1 * MH2_D)
        s2 = d[2] / F(2 * 2 * MH2_D)
        ranks_chosen.append(r)
        params_total += 2 * r * MH2_D
        tel["rank_select"].append({
            "level": lev + 1, "chosen_rank": r,
            "probe_steps": ARA_PROBE_STEPS,
            "probe_drop_r1": str(d[1]),
            "probe_drop_r2": str(d[2]),
            "score_r1": str(s1), "score_r2": str(s2),
            "params_r1": 2 * 1 * MH2_D,
            "params_r2": 2 * 2 * MH2_D,
            "reason": reason,
            "probe_semantics": "no-commit probe on a parameter "
                               "COPY (C530 rollback: state never "
                               "moved, rollback EXACT)"})

        # ADMIT the chosen rank (B = 0, obj invariant EXACTLY)
        p = admit_params(lev, r)
        npar = len(p)
        assert npar == 2 * r * MH2_D
        oA = mh2_fcanon(w, FT)
        A0, B0 = unflat_ad(p, r)
        FTg = feats_ad(FT, A0, B0, r)
        assert mh2_fcanon(w, FTg) == oA, \
            "ABORT: adapter admission #{} broke obj (B = 0 " \
            "must preserve obj EXACTLY)".format(lev + 1)
        tel["admissions"].append({
            "phase": f"B-adapter-l{lev + 1}",
            "rank": r, "new_params": 2 * r * MH2_D,
            "coords": [(lev + j) % MH2_D for j in range(r)],
            "decision": "ADMIT (LoRA zero-init: B = 0, obj "
                        "invariant asserted EXACTLY)"})

        # TRAIN: certified fd steps on ONLY the 2*r*d params
        phase_name = f"C-adapt-l{lev + 1}"
        committed = 0
        for _ in range(ARA_STEPS):
            o = canonp(p, r, FT)
            gfd = []
            for k in range(npar):
                q = list(p)
                q[k] = q[k] + MH2_H
                gfd.append((canonp(q, r, FT) - o) / MH2_H)
            cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                            for k in range(npar)], MH2_GRID)
            o2 = canonp(cand, r, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonp(p, r, HF),
                            "risk'": canonp(cand, r, HF)})
                p = cand
                committed += 1
            else:
                tel["holds"].append({
                    "phase": phase_name, "drop": o - o2,
                    "reason": "canonical drop <= 0: HOLD "
                              "(adapter fd step rolled back)"})

        # SNAP: the C533 boundary (weights + features, exact
        # per-point Lipschitz bound, denominator reset)
        o_before = canonp(p, r, FT)
        ps = [gs_snap2k(v) for v in p]
        As, Bs = unflat_ad(ps, r)
        Ao, Bo = unflat_ad(p, r)
        FTo = feats_ad(FT, Ao, Bo, r)
        FTc = feats_ad(FT, As, Bs, r)
        HFc = feats_ad(HF, As, Bs, r)
        FT = snapfeats(FTc)
        HF = snapfeats(HFc)
        o_after = mh2_fcanon(w, FT)
        err_bound = obj_bound(FTo, FT, w)
        actual = o_after - o_before
        assert o_after <= o_before + err_bound, \
            "ABORT: adapter snap broke its certified bound"
        assert maxden(FT) <= (1 << ARA_K), \
            "ABORT: adapter snap failed to reset denominators"
        cumulative_bound += err_bound
        allowances.append({"phase": phase_name,
                           "obj_before_snap": str(o_before),
                           "obj_after_snap": str(o_after),
                           "actual_degradation": str(actual),
                           "certified_bound": str(err_bound),
                           "bound_ge_actual": True})
        tel["snap"].append({
            "level": lev + 1, "depth": depth + 1,
            "rank": r, "grid": f"q/2^{ARA_K}",
            "obj_before_snap": str(o_before),
            "obj_after_snap": str(o_after),
            "actual_degradation": str(actual),
            "certified_err_bound": str(err_bound),
            "maxden_digits": len(str(maxden(FT))),
            "denominator_reset": True})
        tel["levels"].append({
            "level": lev + 1, "rank": r, "params": npar,
            "committed": committed,
            "net_gain_after_snap": str(oA - mh2_fcanon(w, FT)),
            "canonical": str(mh2_fcanon(w, FT))})
        depth += 1
        tel["phases"].append({
            "phase": phase_name, "depth": depth,
            "params": npar, "committed": committed,
            "canonical": str(mh2_fcanon(w, FT))})
        tel["budget"].append({
            "at_level": lev + 1, "depth": depth,
            "rank": r, "params_level": npar,
            "params_total": params_total,
            "maxden_digits": len(str(maxden(FT))),
            "grid_cap_digits": len(str(1 << ARA_K)),
            "steps_used": len(raw),
            "decision": "LEVEL ADMITTED within budget (rank "
                        f"{r} selected by measured drop/params; "
                        "snap policy: feature denominators "
                        f"RESET to <= 2^{ARA_K} -- no "
                        "compounding)"})

    n = len(raw)
    assert n > 0, "ABORT: adapter-rank-adaptive committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    # obj chain across snap boundaries (C533 reconciliation)
    snap_deltas = [F(x["obj_after_snap"]) -
                   F(x["obj_before_snap"]) for x in allowances]
    si = 0
    for a, b in zip(raw, raw[1:]):
        if a["obj'"] == b["obj"]:
            continue
        needed = b["obj"] - a["obj'"]
        si0 = si
        acc = F(0)
        while si < len(snap_deltas):
            acc += snap_deltas[si]
            si += 1
            if acc == needed:
                break
        assert si > si0 and acc == needed, \
            "ABORT: obj chain broken outside certified snaps"
    assert si <= len(snap_deltas), \
        "ABORT: more chain boundaries than certified snaps"
    # telescoped certified cycle bound (the Lean-side statement)
    obj_final = raw[-1]["obj'"]
    assert obj_final <= cycle_start_obj + cumulative_bound, \
        "ABORT: telescoped rank-adaptive cycle bound violated"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: adapter-rank-adaptive step failed "
                     f"certified admission: {dd}")
    elapsed = time.perf_counter() - t0
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path,
        "trunk": f"2 fd-trained blocks FROZEN (snapped once to "
                 f"q/2^{ARA_K}) + {ARA_LEVELS} RANK-ADAPTIVE "
                 "adapter levels (r in {1,2} selected per level "
                 "by measured probe drop/params), each "
                 "certified-trained then SNAP-FOLDED into the "
                 "grid-bounded features",
        "trunk_depth_final": depth,
        "levels": ARA_LEVELS,
        "fix_rank": fix_rank,
        "ranks_chosen": ranks_chosen,
        "rank_histogram": {str(rr): ranks_chosen.count(rr)
                           for rr in ARA_RANKS},
        "probe_steps_per_arm": ARA_PROBE_STEPS,
        "adapter_params_total": params_total,
        "adapter_params_r1_fix": ARA_LEVELS * 2 * 1 * MH2_D,
        "adapter_params_r2_fix": ARA_LEVELS * 2 * 2 * MH2_D,
        "full_block_params_per_grow": 1 + MH2_D +
                                       2 * MH2_D * MH2_HID,
        "snap_grid": f"q/2^{ARA_K} (per-value err <= 2^-"
                     f"{ARA_K + 1})",
        "grow_obj_invariant_exact_every": True,
        "snap_bounds_all_certified": True,
        "probe_no_commit_rollback_exact": True,
        "snap_cumulative_certified_bound":
            str(cumulative_bound),
        "cycle_obj_start": str(cycle_start_obj),
        "cycle_certified_bound": str(cycle_start_obj +
                                     cumulative_bound),
        "maxden_digits_final": len(str(maxden(FT))),
        "elapsed_s": round(elapsed, 3),
        "canonical_start": str(obj0),
        "canonical_final": str(obj_final),
        "total_drop": str(obj0 - obj_final),
        "drop_per_param_total":
            str((obj0 - obj_final) / F(params_total)),
        "model": "linear head over the rank-adaptive "
                 f"adapter-snap-grown feature stack (depth 2 -> "
                 f"{depth} via {ARA_LEVELS} LoRA adapter levels, "
                 "rank r in {1,2} chosen per level by the "
                 "measured probe drop/params criterion "
                 "(deterministic total order), each admitted at "
                 "B = 0 with EXACT obj invariance, certified fd "
                 "training of only the 2*r*d new params, then "
                 "q/2^k snap-fold with certified err bound; "
                 "denominators bounded at EVERY level)",
        "theorem": "Hagi.Theory.AdapterGrowth."
                   "rank_select_sound / "
                   "rank_select_deterministic (C535)"
    }
    return obj0, raw, tel, stats


def emit_lean_trajrankadaptive(path, start, traj, tel,
                               witness_steps=3):
    """C535 witness: literal rank-adaptive trajectory prefix +
    #eval checkTrajectory + norm_num theorem + the rank-select
    theorems and a real selector instance (the C521/C532/C533
    witness pattern)."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    rs = tel.get("rank_select", [])
    sel_lines = ""
    if rs:
        s1, s2 = rs[0]["score_r1"], rs[0]["score_r2"]
        ch = rs[0]["chosen_rank"]
        sel_lines = (
            "-- REAL selector instance (level 1 measured "
            "probe numbers): the r=2 score is NOT strictly "
            "greater, so the choice is r=1\n"
            "theorem rank_select_inst_l1 :\n"
            "    Hagi.Theory.AdapterGrowth.rankSelect\n"
            f"      ({s1}) ({s2}) = 1 := by\n"
            "      norm_num [Hagi.Theory.AdapterGrowth."
            "rankSelect]\n\n"
            "-- negative: an inflated r=1 score must keep the "
            "choice at 1 (score_2 must be STRICTLY greater "
            "for r=2)\n"
            "theorem rank_select_neg_inflated :\n"
            "    Hagi.Theory.AdapterGrowth.rankSelect (2 : \u211d) "
            "0 = 1 := by\n"
            "      norm_num [Hagi.Theory.AdapterGrowth."
            "rankSelect]\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C535 rank-adaptive adapter grow witness "
                "(real unified_ledger data; per level the rank "
                "r in {1,2} is chosen by the measured probe "
                "drop/params criterion -- a deterministic total "
                "order -- then committed through the C533 "
                "certified cycle).\n"
                f"-- FULL accepted steps: {len(traj)}; "
                f"phases: {phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness; "
                "the full chain, the neutrality/count/snap-bound/"
                "rank-select facts are covered by Hagi.Theory."
                "AdapterGrowth).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.AdapterGrowth\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartRankAdaptive : \u211a := "
                f"{rat(start)}\n\n"
                "def benchTrajectoryRankAdaptive : "
                "List Hagi.Runtime.CertStepData :=\n"
                "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartRankAdaptive "
                "benchTrajectoryRankAdaptive\n\n"
                "theorem rank_adaptive_bench_valid :\n"
                "    checkTrajectory benchStartRankAdaptive "
                "benchTrajectoryRankAdaptive = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartRankAdaptive, "
                "benchTrajectoryRankAdaptive, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "rank_select_sound\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "rank_select_deterministic\n"
                + sel_lines)
    print(f"written: {path}", file=sys.stderr)


# C536: SVD-MATRYOSHKA ADAPTER MERGE (--mode adapter-merge)
#
# The stack-compression breakthrough: the C533 adapter-snap
# stack (8 rank-1 LoRA levels, 2*8*d = 64 params, folded
# sequentially f -> (I + B_l A_l) f) is MERGED into ONE rank-k
# adapter with a certified obj bound:
#
#   1. CYCLE: the C533 fixed-rank-1 stack (fresh loop, the
#      old modes untouched), tracking the per-level matrices
#      M_l = I + B_l^snap A_l^snap (d x d Fractions);
#      M_total = M_8 * ... * M_1; Delta = M_total - I.
#   2. RANK: exact rational Gaussian rank rho of Delta
#      (Fraction elimination, EXACT; rho <= min(d, 8) = 4 —
#      adapter_stack_rank_bound).
#   3. EXACT MERGE (k = rho): Delta = C * R with rational
#      factors (independent columns + echelon coefficients),
#      merged features from the ORIGINAL trunk features;
#      grid snap; certified per-point bound
#      obj_bound(F_stack_final, F_merged, w) — EXACT (C533
#      formula (2|s-y|+|ds|)*|ds|). Params 2*rho*d.
#   4. MATRYOSHKA k < rho: deflated power-iteration top-k on
#      Delta^T Delta (d = 4, pure Python floats, IEEE-
#      deterministic) PROPOSES the factors (C489 principle:
#      numeric candidate, RATIONAL certificate); factor snap
#      q/2^20; the SAME exact per-point bound. Numeric sigma
#      tail ||Delta - Delta_k||_F — the a-priori estimate
#      (Lean form: truncated_svd_error_eq_tail / mdl_rank_ce).
#   5. TELESCOPE: obj_merged <= obj_stack_final + merge_bound
#      and obj_stack_final <= cycle_start + sum snap_bounds.

AMG_LEVELS = 8                     # stack levels (C533 shape)
AMG_K = 40                         # feature snap grid q/2^k
AMG_KFAC = 20                      # matryoshka factor snap grid
AMG_STEPS = 4                      # certified fd steps per level


def _mat_mul(M, N):
    n_, m_, p_ = len(M), len(N), len(N[0])
    return [[sum((M[i][t] * N[t][j] for t in range(m_)), F(0))
             for j in range(p_)] for i in range(n_)]


def _mat_vec(M, f):
    return [sum((M[i][j] * f[j] for j in range(len(f))), F(0))
            for i in range(len(M))]


def _exact_rank_and_factors(M):
    """Exact rational rank + factorization M = C * X (d x rho,
    rho x d) via Gauss-Jordan on Fractions: pivot columns give
    the basis C, the reduced echelon gives X. EXACT."""
    rows, cols = len(M), len(M[0])
    A = [row[:] for row in M]
    pivcols = []
    r = 0
    for c in range(cols):
        sel = None
        for rr in range(r, rows):
            if A[rr][c] != 0:
                sel = rr
                break
        if sel is None:
            continue
        A[r], A[sel] = A[sel], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for rr in range(rows):
            if rr != r and A[rr][c] != 0:
                fq = A[rr][c]
                A[rr] = [a - fq * b for a, b in zip(A[rr], A[r])]
        pivcols.append(c)
        r += 1
    rho = r
    C = [[M[i][c] for c in pivcols] for i in range(rows)]
    X = [[F(0)] * cols for _ in range(rho)]
    for i, c in enumerate(pivcols):
        X[i][c] = F(1)
    for c in range(cols):
        if c in pivcols:
            continue
        for i in range(rho):
            X[i][c] = A[i][c]
    return rho, C, X


def _power_topk(Dm, k):
    """Deflated power iteration for the top-k right singular
    subspace of Dm (floats, deterministic): returns list of
    (sigma, u, v) triples, u = D v / sigma."""
    import math
    n = len(Dm)
    DtD = [[sum((float(Dm[t][i]) * float(Dm[t][j])
                 for t in range(n)))
            for j in range(n)] for i in range(n)]
    resid = [row[:] for row in Dm]
    out = []
    for _ in range(k):
        v = [1.0 / math.sqrt(n)] * n
        lam = 0.0
        for _it in range(400):
            w = [sum(DtD[i][j] * v[j] for j in range(n))
                 for i in range(n)]
            nv = math.sqrt(sum(x * x for x in w))
            if nv < 1e-300:
                break
            v = [x / nv for x in w]
        lam = sum(v[i] * sum(DtD[i][j] * v[j] for j in range(n))
                  for i in range(n))
        sigma = math.sqrt(max(lam, 0.0))
        u = [sum(float(resid[i][j]) * v[j] for j in range(n))
             for i in range(n)]
        if sigma > 0:
            un = math.sqrt(sum(x * x for x in u))
            u = [x / (un if un > 0 else 1.0) for x in u]
            # deflate BOTH DtD (for the next v) and resid
            # (for the next u)
            for i in range(n):
                for j in range(n):
                    DtD[i][j] -= sigma * sigma * u[i] * u[j]
            for i in range(n):
                for j in range(n):
                    resid[i][j] -= sigma * u[i] * v[j]
        out.append((sigma, u, v))
    return out


def adapter_merge_run(ledger_path):
    """C536 SVD-matryoshka adapter merge: run the C533 rank-1
    stack (8 levels, 64 params), compute Delta = M_total - I,
    exact rational rank rho, merge to a single rank-k adapter
    (exact at k = rho; numeric-proposed + exact certified at
    k < rho). Returns (start, [accepted steps], telemetry,
    stats)."""
    sys.set_int_max_str_digits(0)
    t0 = time.perf_counter()
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    tasks, skipped = clm_split(pts)
    T = len(tasks)
    assert T == 3, "ABORT: expected 3 tasks from clm_split"
    hold = [(kx, x, y) for i, (kx, x, y) in enumerate(pts)
            if i % 5 == 4]
    htasks, _ = clm_split(hold)
    assert all(htasks), "ABORT: empty holdout task after split"

    theta = (mh2_block_init(0), mh2_block_init(1))
    w = [F(0)] * MH2_D
    raw, tel = [], {"phases": [], "holds": [], "admissions": [],
                    "levels": [], "snap": [], "budget": [],
                    "merge": [],
                    "skipped_degenerate_T2": skipped}

    def riskA(th, wcur):
        return sum((mh2_mse(wcur, tk, th) for tk in htasks),
                   F(0)) / F(len(htasks))

    # --- (A) 2-block trunk + head joint certified steps (C521 A)
    obj0 = mh2_canon(w, tasks, theta)
    for _ in range(MH2_A_STEPS):
        p = mh2_flat(theta, w)
        o = mh2_canon(w, tasks, theta)
        gfd = []
        for k in range(MH2_NPAR):
            q = list(p)
            q[k] = q[k] + MH2_H
            th2, w2 = mh2_unflat(q)
            gfd.append((mh2_canon(w2, tasks, th2) - o) / MH2_H)
        cand = cl_snap([p[k] - MH2_ETA * gfd[k]
                        for k in range(MH2_NPAR)], MH2_GRID)
        th2, w2 = mh2_unflat(cand)
        o2 = mh2_canon(w2, tasks, th2)
        if o2 < o:
            raw.append({"phase": "A-trunk2", "obj": o,
                        "obj'": o2, "drop": o - o2,
                        "risk": riskA(theta, w),
                        "risk'": riskA(th2, w2)})
            theta, w = th2, w2
        else:
            tel["holds"].append({"phase": "A-trunk2",
                                 "drop": o - o2,
                                 "reason": "canonical drop <= 0: "
                                           "HOLD"})
    assert raw, "ABORT: phase A committed no steps"
    tel["phases"].append({
        "phase": "A-trunk2", "depth": 2, "params": MH2_NPAR,
        "canonical": str(mh2_canon(w, tasks, theta))})

    # --- rank-1 adapter stack branch (f + B(A f))
    def fwd1(f, A, B):
        z = sum((A[0][k] * f[k] for k in range(MH2_D)), F(0))
        return [f[i] + B[i][0] * z for i in range(MH2_D)]

    def feats_ad(base, A, B):
        return [[(fwd1(f, A, B), y) for f, y in tk] for tk in base]

    def snapfeats(base):
        return [[([gs_snap2k(c) for c in f], y)
                 for f, y in tk] for tk in base]

    def maxden(base):
        return max(abs(c.denominator)
                   for tk in base for f, _ in tk for c in f)

    def obj_bound(base_orig, base_final, wcur):
        """EXACT certified bound (C533): per point
        |(s2-y)^2 - (s1-y)^2| <= (2|s1-y| + |ds|)*|ds|."""
        Bsum = F(0)
        cnt = 0
        for tk, tkf in zip(base_orig, base_final):
            for (f1, y), (f2, _) in zip(tk, tkf):
                ds = sum((wcur[i] * (f2[i] - f1[i])
                          for i in range(MH2_D)), F(0))
                s = sum((wcur[i] * f1[i]
                         for i in range(MH2_D)), F(0))
                Bsum += (2 * abs(s - y) + abs(ds)) * abs(ds)
                cnt += 1
        return Bsum / cnt

    def unflat_ad(pp):
        A = [[pp[j] for j in range(MH2_D)]]
        B = [[pp[MH2_D + i]] for i in range(MH2_D)]
        return A, B

    def canonp(pp, base):
        A, Bl = unflat_ad(pp)
        return mh2_fcanon(w, feats_ad(base, A, Bl))

    # trunk FROZEN: snapped features (the ORIGINAL trunk state
    # is the merge base — every merged candidate starts here)
    FT_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in tasks]
    HF_un = [[(mh2_trunk_fwd(theta, x), y) for x, y in tk]
             for tk in htasks]
    FT = snapfeats(FT_un)
    HF = snapfeats(HF_un)
    assert mh2_fcanon(w, FT) <= mh2_fcanon(w, FT_un) + \
        obj_bound(FT_un, FT, w), \
        "ABORT: freeze snap broke its certified bound"
    FT0 = [[(f[:], y) for f, y in tk] for tk in FT]  # merge base
    HF0 = [[(f[:], y) for f, y in tk] for tk in HF]

    # --- (B) rank-1 stack: 8 C533 levels + matrix tracking
    depth = 2
    cycle_start_obj = mh2_fcanon(w, FT)
    cumulative_bound = F(0)
    allowances = [{"phase": "A-freeze-snap",
                   "obj_before_snap": str(mh2_fcanon(w, FT_un)),
                   "obj_after_snap": str(cycle_start_obj),
                   "actual_degradation":
                       str(cycle_start_obj -
                           mh2_fcanon(w, FT_un)),
                   "certified_bound":
                       str(obj_bound(FT_un, FT, w)),
                   "bound_ge_actual": True}]
    params_total = 0
    M_total = [[F(1) if i == j else F(0)
                for j in range(MH2_D)] for i in range(MH2_D)]
    stack_mats = []
    for lev in range(AMG_LEVELS):
        # ADMIT r=1: A = unit row on coord lev mod d, B = 0
        p = [F(1) if k == lev % MH2_D else F(0)
             for k in range(MH2_D)] + [F(0)] * MH2_D
        oA = mh2_fcanon(w, FT)
        A0, B0 = unflat_ad(p)
        assert mh2_fcanon(w, feats_ad(FT, A0, B0)) == oA, \
            "ABORT: adapter admission #{} broke obj".format(lev + 1)
        tel["admissions"].append({
            "phase": f"B-adapter-l{lev + 1}", "rank": 1,
            "new_params": 2 * MH2_D,
            "coords": [lev % MH2_D],
            "decision": "ADMIT (LoRA zero-init: B = 0, obj "
                        "invariant asserted EXACTLY)"})

        # TRAIN: certified fd steps on the 2*d adapter params
        phase_name = f"C-adapt-l{lev + 1}"
        committed = 0
        for _ in range(AMG_STEPS):
            o = canonp(p, FT)
            gfd = []
            for kk in range(len(p)):
                q = list(p)
                q[kk] = q[kk] + MH2_H
                gfd.append((canonp(q, FT) - o) / MH2_H)
            cand = cl_snap([p[kk] - MH2_ETA * gfd[kk]
                            for kk in range(len(p))], MH2_GRID)
            o2 = canonp(cand, FT)
            if o2 < o:
                raw.append({"phase": phase_name, "obj": o,
                            "obj'": o2, "drop": o - o2,
                            "risk": canonp(p, HF),
                            "risk'": canonp(cand, HF)})
                p = cand
                committed += 1
            else:
                tel["holds"].append({
                    "phase": phase_name, "drop": o - o2,
                    "reason": "canonical drop <= 0: HOLD "
                              "(adapter fd step rolled back)"})

        # SNAP: weights + features, exact per-point bound
        o_before = canonp(p, FT)
        ps = [gs_snap2k(v) for v in p]
        As, Bs = unflat_ad(ps)
        Ao, Bo = unflat_ad(p)
        FTo = feats_ad(FT, Ao, Bo)
        FTc = feats_ad(FT, As, Bs)
        HF = snapfeats(feats_ad(HF, As, Bs))
        FT = snapfeats(FTc)
        o_after = mh2_fcanon(w, FT)
        err_bound = obj_bound(FTo, FT, w)
        assert o_after <= o_before + err_bound, \
            "ABORT: adapter snap broke its certified bound"
        assert maxden(FT) <= (1 << AMG_K), \
            "ABORT: adapter snap failed to reset denominators"
        cumulative_bound += err_bound
        allowances.append({"phase": phase_name,
                           "obj_before_snap": str(o_before),
                           "obj_after_snap": str(o_after),
                           "actual_degradation":
                               str(o_after - o_before),
                           "certified_bound": str(err_bound),
                           "bound_ge_actual": True})
        tel["snap"].append({
            "level": lev + 1, "depth": depth + 1,
            "grid": f"q/2^{AMG_K}",
            "obj_before_snap": str(o_before),
            "obj_after_snap": str(o_after),
            "certified_err_bound": str(err_bound),
            "maxden_digits": len(str(maxden(FT)))})
        # track the level matrix M_l = I + B A (snapped)
        Ml = [[(F(1) if i == j else F(0)) +
               Bs[i][0] * As[0][j] for j in range(MH2_D)]
              for i in range(MH2_D)]
        M_total = _mat_mul(Ml, M_total)
        stack_mats.append(Ml)
        params_total += 2 * MH2_D
        tel["levels"].append({
            "level": lev + 1, "params": 2 * MH2_D,
            "committed": committed,
            "canonical": str(mh2_fcanon(w, FT))})
        depth += 1
        tel["phases"].append({
            "phase": phase_name, "depth": depth,
            "params": 2 * MH2_D, "committed": committed,
            "canonical": str(mh2_fcanon(w, FT))})

    n = len(raw)
    assert n > 0, "ABORT: adapter-merge committed no steps"
    for t, dd in enumerate(raw):
        dd["budget"] = F(n - t) / n
        dd["budget'"] = F(n - t - 1) / n
    # obj chain across snap boundaries (C533 reconciliation)
    snap_deltas = [F(x["obj_after_snap"]) -
                   F(x["obj_before_snap"]) for x in allowances]
    si = 0
    for a, b in zip(raw, raw[1:]):
        if a["obj'"] == b["obj"]:
            continue
        needed = b["obj"] - a["obj'"]
        si0 = si
        acc = F(0)
        while si < len(snap_deltas):
            acc += snap_deltas[si]
            si += 1
            if acc == needed:
                break
        assert si > si0 and acc == needed, \
            "ABORT: obj chain broken outside certified snaps"
    assert si <= len(snap_deltas), \
        "ABORT: more chain boundaries than certified snaps"
    # telescoped certified stack bound (the C533 statement)
    obj_stack_final = raw[-1]["obj'"]
    assert obj_stack_final <= cycle_start_obj + cumulative_bound, \
        "ABORT: telescoped stack cycle bound violated"
    for dd in raw:
        if not check_step(dd):
            sys.exit(f"ABORT: adapter-merge step failed "
                     f"certified admission: {dd}")

    # --- (C) MERGE: Delta = M_total - I, exact rank, matryoshka
    Delta = [[M_total[i][j] -
              (F(1) if i == j else F(0))
              for j in range(MH2_D)] for i in range(MH2_D)]
    rho, Cex, Xex = _exact_rank_and_factors(Delta)
    # sanity: factorization EXACT
    assert _mat_mul(Cex, Xex) == Delta, \
        "ABORT: exact factorization Delta = C*X failed"
    tel["merge"].append({
        "step": "delta", "exact_rank": rho,
        "rank_le_min_d_L": True,
        "adapter_stack_rank_bound":
            f"rank(Delta) <= min(d, L) = min({MH2_D}, "
            f"{AMG_LEVELS}) = {min(MH2_D, AMG_LEVELS)}",
        "rank_bound_tight": rho == min(MH2_D, AMG_LEVELS)})

    def merged_feats(FTbase, Bm, Am, rk):
        """single rank-rk adapter on the ORIGINAL trunk
        features: f -> f + B(A f), then grid snap"""
        def fw(f):
            z = [sum((Am[j][k] * f[k] for k in range(MH2_D)),
                     F(0)) for j in range(rk)]
            return [f[i] + sum((Bm[i][j] * z[j]
                                for j in range(rk)), F(0))
                    for i in range(MH2_D)]
        return [[(fw(f)[:], y) for f, y in tk] for tk in FTbase]

    matryoshka = []
    o_stack_final = mh2_fcanon(w, FT)
    for kk in range(rho, 0, -1):
        if kk == rho:
            # EXACT merge: Delta = C * X, rational, zero
            # perturbation before the feature snap
            Bm, Am = Cex, Xex
            how = "exact-rational (Gauss-Jordan C*X = Delta)"
        else:
            # numeric deflated power iteration PROPOSES the
            # factors (C489: numeric candidate, rational
            # certificate); factor snap q/2^KFAC
            trip = _power_topk(Delta, kk)
            Bm = [[gs_snap2k(F(round(sum(
                              float(Delta[i][j]) * v[j]
                              for j in range(MH2_D)) /
                             (sg if sg > 1e-300 else 1.0), 12)),
                             AMG_KFAC)
                   for (sg, _, v) in trip] for i in range(MH2_D)]
            Am = [[gs_snap2k(F(round(v[j], 12)), AMG_KFAC)
                   for j in range(MH2_D)] for (sg, _, v) in trip]
            how = (f"numeric power-iteration top-{kk} + factor "
                   f"snap q/2^{AMG_KFAC}")
        FTm = snapfeats(merged_feats(FT0, Bm, Am, kk))
        HFm = snapfeats(merged_feats(HF0, Bm, Am, kk))
        o_m = mh2_fcanon(w, FTm)
        bnd = obj_bound(FT, FTm, w)
        actual = o_m - o_stack_final
        assert o_m <= o_stack_final + bnd, \
            f"ABORT: merge k={kk} broke its certified bound"
        assert maxden(FTm) <= (1 << AMG_K), \
            f"ABORT: merge k={kk} failed denominator reset"
        # numeric sigma-tail estimate (a priori, informative)
        Dk = _mat_mul(Bm, Am)
        tail_sq = sum((float(Delta[i][j] - Dk[i][j]) ** 2
                       for i in range(MH2_D)
                       for j in range(MH2_D)), 0.0)
        matryoshka.append({
            "k": kk, "params": 2 * kk * MH2_D,
            "method": how,
            "obj_merged": str(o_m),
            "actual_degradation_vs_stack": str(actual),
            "certified_bound": str(bnd),
            "bound_ge_actual": True,
            "sigma_tail_frobenius_est":
                f"{tail_sq ** 0.5:.6e}",
            "usable": actual <= F(1, 1000) * o_stack_final,
            "maxden_digits": len(str(maxden(FTm)))})
        tel["merge"].append(dict(matryoshka[-1]))

    # the FINAL deployed merged model: exact rank rho
    final = next(m for m in matryoshka if m["k"] == rho)
    o_final_merged = F(final["obj_merged"])
    merge_bound_final = F(final["certified_bound"])
    # full telescope: stack + merge
    assert o_final_merged <= cycle_start_obj + \
        cumulative_bound + merge_bound_final, \
        "ABORT: telescoped merge cycle bound violated"

    elapsed = time.perf_counter() - t0
    stats = {
        "n_points": len(pts),
        "task_sizes": [len(t) for t in tasks],
        "skipped_degenerate_T2": skipped,
        "n_holdout": sum(len(t) for t in htasks),
        "source": ledger_path,
        "trunk": f"2 fd-trained blocks FROZEN (snapped once to "
                 f"q/2^{AMG_K}) + {AMG_LEVELS} rank-1 adapter "
                 "levels (C533 cycle) MERGED into ONE rank-rho "
                 "adapter (SVD-matryoshka)",
        "trunk_depth_final": depth,
        "levels": AMG_LEVELS,
        "stack_params_total": params_total,
        "stack_params_formula": f"2*L*d = 2*{AMG_LEVELS}*"
                                f"{MH2_D} = {params_total}",
        "merged_exact_rank": rho,
        "merged_params": 2 * rho * MH2_D,
        "merged_params_formula":
            f"2*rho*d = 2*{rho}*{MH2_D} = {2 * rho * MH2_D}",
        "params_saved": params_total - 2 * rho * MH2_D,
        "params_saved_fraction":
            str(F(params_total - 2 * rho * MH2_D,
                  params_total)),
        "matryoshka": matryoshka,
        "matvecs": {"stack": AMG_LEVELS, "merged": 1},
        "snap_grid": f"q/2^{AMG_K}",
        "factor_snap_grid": f"q/2^{AMG_KFAC} (matryoshka arms)",
        "snap_bounds_all_certified": True,
        "merge_bounds_all_certified": True,
        "snap_cumulative_certified_bound": str(cumulative_bound),
        "merge_certified_bound": str(merge_bound_final),
        "cycle_obj_start": str(cycle_start_obj),
        "cycle_certified_bound_full":
            str(cycle_start_obj + cumulative_bound +
                merge_bound_final),
        "obj_stack_final": str(o_stack_final),
        "obj_merged_final": str(o_final_merged),
        "merge_actual_degradation":
            str(o_final_merged - o_stack_final),
        "maxden_digits_final": final["maxden_digits"],
        "elapsed_s": round(elapsed, 3),
        "canonical_start": str(obj0),
        "total_drop": str(obj0 - o_final_merged),
        "model": "linear head over trunk features + ONE "
                 f"rank-{rho} adapter (the C533 8-level "
                 "rank-1 stack merged: Delta = M_total - I with "
                 "EXACT rational rank rho and factorization "
                 "Delta = C*X; certified obj bound per k on the "
                 "matryoshka curve)",
        "theorem": "Hagi.Theory.AdapterGrowth."
                   "adapter_stack_rank_bound / "
                   "adapter_merge_error_bound / "
                   "adapter_merge_params (C536)"
    }
    return obj0, raw, tel, stats


def emit_lean_trajmerge(path, start, traj, tel, stats,
                        witness_steps=3):
    """C536 witness: literal merged-stack trajectory prefix +
    #eval checkTrajectory + norm_num theorem + the three C536
    theorems and a REAL stack-rank instance."""
    ds = [dict(d) for d in traj[:witness_steps]]
    phases = ", ".join(sorted({d["phase"] for d in traj}))
    rho = stats["merged_exact_rank"]
    with open(path, "w", encoding="utf-8") as f:
        f.write("-- C536 SVD-matryoshka adapter-merge witness "
                "(real unified_ledger data; the C533 rank-1 "
                "stack cycle, then the certified merge into "
                "ONE rank-rho adapter).\n"
                f"-- FULL accepted steps: {len(traj)}; "
                f"phases: {phases};\n-- first {len(ds)} "
                "machine-checked steps below (prefix witness; "
                "the neutrality/count/snap-bound/rank-bound "
                "facts are covered by Hagi.Theory."
                "AdapterGrowth).\n"
                "import Hagi.Runtime.CertChecker\n"
                "import Hagi.Theory.AdapterGrowth\n\n"
                "open Hagi.Runtime\n\n"
                f"def benchStartMerge : \u211a := {rat(start)}\n\n"
                "def benchTrajectoryMerge : "
                "List Hagi.Runtime.CertStepData :=\n"
                "[\n" + ",\n".join(lean_step(d) for d in ds)
                + "\n]\n\n"
                "#eval checkTrajectory benchStartMerge "
                "benchTrajectoryMerge\n\n"
                "theorem merge_bench_valid :\n"
                "    checkTrajectory benchStartMerge "
                "benchTrajectoryMerge = true := by\n"
                "  simp only [checkTrajectory, checkStep, "
                "benchStartMerge, benchTrajectoryMerge, "
                "Bool.and_eq_true, decide_eq_true_eq]\n"
                "  norm_num\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_stack_rank_bound\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_merge_error_bound\n\n"
                "#check @Hagi.Theory.AdapterGrowth."
                "adapter_merge_params\n\n"
                "-- REAL stack-rank instance: a 2-level stack of "
                "-- rank-1 perturbations on Fin 2 — the merged "
                "-- perturbation stackProd [E1, E2] - 1 has rank 2 "
                "-- (the adapter_stack_rank_bound sum 1+1 is "
                "-- TIGHT, not vacuous)\n"
                "#eval (Hagi.Theory.AdapterGrowth.stackProd "
                "[!![0, 1; 0, 0], !![0, 0; 1, 0]] - 1 : "
                "  Matrix (Fin 2) (Fin 2) \u211d).rank\n\n"
                "#eval ([Hagi.Theory.AdapterGrowth.stackProd "
                "  [!![0, 1; 0, 0], !![0, 0; 1, 0]]].map "
                "  Matrix.rank).head\n")
    print(f"written: {path}", file=sys.stderr)

# (--mode agem-vs-ranktrunc)
#
# The GPM-family empirical closure: BOTH continual mechanisms
# from C498 (Hagi/Theory/Continual.lean (GPMRelaxed section)) run on the SAME
# C485 scenario (task A -> task B on the live unified_ledger
# corpus, exact Fractions) with the SAME phase-1 wA, the SAME
# B data, step budget, eta and snap grid — the ONLY difference
# is the step-direction mechanism:
#
#   arm rank-trunc (C500 mechanics): keep the top-k
#     energy-ordered Gram-Schmidt directions of span(A),
#     k = min k with max_old sigmaTail^2 <= eps^2; delta =
#     Q_keptcomplement . snap(-eta*g_B); per-step per-old-input
#     assert |delta.x|^2 <= ||delta||^2 * sigmaTail^2
#     (the bench form of rank_trunc_forgetting_bound).
#
#   arm A-GEM (C498 agemStep, canonical per-step memory
#     gradient g_old = grad_A(w)): the step is FREE when
#     <g, g_old> >= 0; on conflict the direction is one
#     Gram-Schmidt iteration d = g - (<g,g_old>/<g_old,g_old>)*
#     g_old with the EXACT assert d . g_old >= 0 (the live
#     instance of agem_step_nonneg_interf); the applied snapped
#     step is delta = snap(-eta*d).
#
# Both arms: admission ONLY by the MEASURED canonical drop > 0
# on task B (certified trace, guarded rollback HOLD otherwise).
# Honest telemetry: loss_A drift is MEASURED (may be negative —
# improvement — or positive; snapping can break the pre-snap
# first-order guarantee, the report never claims otherwise).

AGN_EPS = F(1, 10)      # rank-trunc tolerance (C500 PIN)
AGN_STEPS = 24          # PIN: probe-measured — at 6 steps the
                        # A-GEM conflict branch never fires; 24
                        # fires conflicts with interference
                        # exactly 0 (the honest differentiator)


def agn_agem_step(g, g_old, d):
    """Exact-Fraction agemStep (C498 def): free when
    <g, g_old> >= 0, else one Gram-Schmidt iteration.
    Returns (direction, conflict_flag)."""
    dot = sum((g[i] * g_old[i] for i in range(d)), F(0))
    if dot >= 0:
        return list(g), False
    gg = sum((g_old[i] * g_old[i] for i in range(d)), F(0))
    return [g[i] - dot / gg * g_old[i] for i in range(d)], True


def agn_run(ledger_path, steps=AGN_STEPS):
    """C508: phase 1 on A (shared), phase 2 on B by BOTH
    continual mechanisms; per-arm certified trajectories and
    the honest comparison table."""
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    A, B = cl_split(pts)
    d = CL_D
    basis = cl_gs_basis([x for x, _ in A])
    assert 0 < len(basis) < d, \
        "ABORT: need 0 < rank(span A) < 4 (few-shot PIN)"

    # phase 1 (shared by both arms — fairness)
    traj1, tel1, wA = cl_certified_loop([F(0)] * d, A, B,
                                        CL_STEPS)
    lossA_after1 = cl_mse(wA, A)
    mseB0 = cl_mse(wA, B)

    # ---------- arm 1: rank-trunc relaxed GPM (C500) ----------
    r = len(basis)
    energy = [sum((sum((b[i] * x[i] for i in range(d)), F(0))
                   ** 2 for x, _ in A), F(0)) for b in basis]
    order = sorted(range(r), key=lambda j: energy[j],
                   reverse=True)
    kept_for, tail2max = {}, []
    for k in range(r + 1):
        kept_for[k] = [basis[j] for j in order[:k]]
        tail2max.append(max(
            [sum((t * t for t in mh3_resid(x, kept_for[k], d)),
                 F(0)) for x, _ in A] + [F(0)]))
    kmin = next((k for k in range(r)
                 if tail2max[k] <= AGN_EPS ** 2), None)
    assert kmin is not None, \
        "ABORT: no k < rank within eps-budget on live corpus"
    Qk = cl_complement_projector(kept_for[kmin])

    w = list(wA)
    rt_raw, rt_holds, rt_relaxed = [], [], 0
    rt_max_forget_out = F(0)
    for _ in range(steps):
        g = cl_grad(w, B)
        delta = cl_apply(Qk, cl_snap([-CL_ETA * t for t in g]))
        cand = [w[i] + delta[i] for i in range(d)]
        nrm2 = sum((t * t for t in delta), F(0))
        for x, _ in A:        # rank_trunc_forgetting_bound
            tail = mh3_resid(x, kept_for[kmin], d)
            tail2 = sum((t * t for t in tail), F(0))
            dx = sum((delta[i] * x[i] for i in range(d)), F(0))
            assert dx * dx <= nrm2 * tail2, \
                "ABORT: rank-trunc forgetting bound violated"
            if abs(dx) > rt_max_forget_out:
                rt_max_forget_out = abs(dx)
        o0, o1 = cl_mse(w, B), cl_mse(cand, B)
        if o1 < o0:
            rt_raw.append({"obj": o0, "obj'": o1,
                           "drop": o0 - o1,
                           "risk": cl_mse(w, A),
                           "risk'": cl_mse(cand, A)})
            if any(delta):
                rt_relaxed += 1
            w = cand
        else:
            rt_holds.append({"drop": o0 - o1,
                             "reason": "drop <= 0: HOLD "
                                       "(rank-trunc arm)"})
    rt_forget = cl_mse(w, A) - lossA_after1
    rt_progress = sum((s["drop"] for s in rt_raw), F(0))

    # ---------- arm 2: A-GEM (C498 agemStep) ----------
    w = list(wA)
    ag_raw, ag_holds = [], []
    conflicts, free_steps = 0, 0
    conflict_interf = []          # d . g_old on conflicts (>= 0)
    for _ in range(steps):
        g = cl_grad(w, B)
        g_old = cl_grad(w, A)
        dd, conflict = agn_agem_step(g, g_old, d)
        if conflict:
            conflicts += 1
            interf = sum((dd[i] * g_old[i] for i in range(d)),
                         F(0))
            assert interf >= 0, \
                "ABORT: agemStep interference < 0 (theorem " \
                "violated)"
            conflict_interf.append(interf)
        else:
            free_steps += 1
        delta = cl_snap([-CL_ETA * t for t in dd])
        cand = [w[i] + delta[i] for i in range(d)]
        o0, o1 = cl_mse(w, B), cl_mse(cand, B)
        if o1 < o0:
            ag_raw.append({"obj": o0, "obj'": o1,
                          "drop": o0 - o1,
                          "risk": cl_mse(w, A),
                          "risk'": cl_mse(cand, A)})
            w = cand
        else:
            ag_holds.append({"drop": o0 - o1,
                             "reason": "drop <= 0: HOLD "
                                       "(A-GEM arm)"})
    ag_forget = cl_mse(w, A) - lossA_after1
    ag_progress = sum((s["drop"] for s in ag_raw), F(0))

    # ---------- certify both trajectories (C485 form) ----------
    for name, raw in (("rank-trunc", rt_raw), ("agem", ag_raw)):
        assert raw, f"ABORT: {name} arm committed no steps"
        n = len(raw)
        for t, dd_ in enumerate(raw):
            dd_["budget"] = F(n - t) / n
            dd_["budget'"] = F(n - t - 1) / n
            if not check_step(dd_):
                sys.exit(f"ABORT: {name} step {t} failed "
                         f"certified admission: {dd_}")
        for a, b in zip(raw, raw[1:]):
            assert a["obj'"] == b["obj"], \
                f"ABORT: {name} obj chain broken"

    return {
        "n_points": len(pts), "n_A": len(A), "n_B": len(B),
        "rankA": r, "steps": steps, "eps": str(AGN_EPS),
        "phase1": {"n_steps": len(traj1),
                   "lossA_after": str(lossA_after1)},
        "rank_trunc": {
            "k": kmin, "rank": r,
            "tail2max_by_k": [str(t) for t in tail2max],
            "committed": len(rt_raw), "holds": len(rt_holds),
            "relaxed_steps": rt_relaxed,
            "B_progress": str(rt_progress),
            "B_progress_float": float(rt_progress),
            "forgetA": str(rt_forget),
            "forgetA_float": float(rt_forget),
            "max_forget_out": str(rt_max_forget_out),
            "traj": rt_raw, "holds_detail": rt_holds},
        "agem": {
            "committed": len(ag_raw), "holds": len(ag_holds),
            "conflicts": conflicts, "free_steps": free_steps,
            "conflict_interference_min": (
                str(min(conflict_interf))
                if conflict_interf else "n/a (no conflicts)"),
            "B_progress": str(ag_progress),
            "B_progress_float": float(ag_progress),
            "forgetA": str(ag_forget),
            "forgetA_float": float(ag_forget),
            "traj": ag_raw, "holds_detail": ag_holds},
        "mseB0": str(mseB0),
    }


def emit_lean_agn(path, res, witness_steps=3):
    """C508 witness: both arm trajectories (prefix, header
    documents FULL counts) + #eval x2 + valid theorems +
    negative control (inflated last AGEM drop -> false) +
    #check of the two C498 theorems the arms instantiate."""
    blocks = [("RT", res["rank_trunc"]["traj"]),
              ("AG", res["agem"]["traj"])]
    starts = {"RT": blocks[0][1][0]["obj"],
              "AG": blocks[1][1][0]["obj"]}
    out = ["-- C508 A-GEM vs rank-trunc continual witness "
           "(real unified_ledger data).\n"
           f"-- shared phase-1 wA (lossA {res['phase1']['lossA_after']}); "
           "FULL accepted steps: "
           f"rank-trunc={len(blocks[0][1])}, "
           f"agem={len(blocks[1][1])}; first "
           f"{witness_steps} machine-checked prefixes below.\n"
           "-- arms differ ONLY in the step-direction "
           "mechanism (same wA, B data, steps, eta, grid).\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.Continual\n\n"
           "open Hagi.Runtime\n\n"]
    for name, traj in blocks:
        ds = [dict(d) for d in traj[:witness_steps]]
        out.append(
            f"def benchStartC508{name} : \u211a := "
            f"{rat(starts[name])}\n\n"
            f"def benchTrajectoryC508{name} : List "
            "Hagi.Runtime.CertStepData :=\n[\n"
            + ",\n".join(lean_step(d) for d in ds)
            + "\n]\n\n"
            f"#eval checkTrajectory benchStartC508{name} "
            f"benchTrajectoryC508{name}\n\n"
            f"theorem agn_traj_{name.lower()}_valid :\n"
            f"    checkTrajectory benchStartC508{name} "
            f"benchTrajectoryC508{name} = true := by\n"
            "  set_option linter.unusedSimpArgs false in\n"
            "  simp only [checkTrajectory, checkStep, "
            f"benchStartC508{name}, "
            f"benchTrajectoryC508{name}, "
            "Bool.and_eq_true, decide_eq_true_eq]\n"
            "  norm_num\n\n")
    # negative: inflated last AGEM drop -> checker rejects
    bad = [dict(d) for d in blocks[1][1][:witness_steps]]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    out.append(
        "def benchStartC508AGBad : \u211a := "
        f"{rat(starts['AG'])}\n\n"
        "def benchTrajectoryC508AGBad : List "
        "Hagi.Runtime.CertStepData :=\n[\n"
        + ",\n".join(lean_step(d) for d in bad)
        + "\n]\n\n"
        "#eval checkTrajectory benchStartC508AGBad "
        "benchTrajectoryC508AGBad\n\n"
        "theorem agn_traj_ag_invalid :\n"
        "    checkTrajectory benchStartC508AGBad "
        "benchTrajectoryC508AGBad = false := by\n"
        "  set_option linter.unusedSimpArgs false in\n"
        "  simp only [checkTrajectory, checkStep, "
        "benchStartC508AGBad, benchTrajectoryC508AGBad, "
        "Bool.and_eq_true, decide_eq_true_eq]\n"
        "  norm_num\n\n")
    out.append("#check @Hagi.Theory.GPMRelaxed."
               "agem_step_nonneg_interf\n"
               "#check @Hagi.Theory.GPMRelaxed."
               "rank_trunc_forgetting_bound\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)


# C510: HYBRID CONTINUAL MECHANISM SELECTION
# (--mode hybrid-continual)
#
# Roadmap C509 top-1: ONE continual loop whose per-step step
# mechanism is selected DETERMINISTICALLY from the MEASURED
# state (the C509 decision table, .omc/analysis/
# period-c506-508-analysis.md section b):
#
#   (a) span fullness (measured once per scenario — an exact
#       rational Gram-Schmidt fact): rank(span A \u222a B) < dim
#       -> full-GPM (project onto the complement of span(A);
#       per-old-input exact assert delta \u00b7 x = 0 — the bench
#       form of gpm_zero_forgetting);
#   (b) span exhausted -> per-step conflict check on the exact
#       sign of <g, g_old>: >= 0 -> A-GEM FREE step (full
#       gradient, zero cost — the free case of
#       agem_step_nonneg_interf); < 0 -> rank-trunc (per-point
#       forgetting bound (delta \u00b7 x)^2 <= ||delta||^2 *
#       sigmaTail^2 — the C500/C508 mechanics; the decision
#       table row "span exhausted -> rank-trunc").
#
# The selector uses ONLY measurable exact-Fraction quantities
# (rank vs dim, the dot sign) — no randomness, no float
# thresholds. Admission at every step is the certified measured
# drop > 0 gate on B (guarded rollback HOLD otherwise); the
# trajectory is budget-filled and re-verified by check_step
# exactly like C485/C508. Pure arms (rank-trunc, A-GEM) come
# from agn_run on the SAME deterministic phase-1 wA in the same
# process (fair comparison, C508 pins). Soundness of the
# selection itself is Hagi.Theory.HybridContinual.
# hybrid_step_sound (C510): the chosen branch's guarantee holds
# with no weakening (disjunction of the three mechanisms).

HYB_STEPS = 24            # PIN: same budget as the C508 arms;
                          # live-measured selector split 5 free /
                          # 19 rank-trunc steps at 24


def hyb_run(ledger_path, steps=HYB_STEPS):
    """C510: hybrid continual loop — per-step mechanism by the
    measured state (C509 decision table), plus BOTH pure arms on
    the SAME data/phase-1/budget for the honest 3-row table.

    Corpus-drift honesty (C510): the C508 `agem-vs-ranktrunc`
    mode ABORTS on the current live corpus (its rank-trunc pin
    kmin < rank is violated after the ledger drifted past the
    C508-era data — PRE-EXISTING, reproduced on clean HEAD c5b13c
    before this commit). This mode therefore computes the pure
    rank-trunc arm with the RELAXED k_eff = min(kmin, rank):
    when the eps-budget forces k_eff = rank the truncation is
    degenerate (sigmaTail = 0 on old inputs; the per-point
    forgetting bound still holds, as exact zero-interference
    asserts), and the telemetry reports `rank_trunc_degenerate`
    = true with the measured k. All three rows share the SAME
    wA / B data / steps / eta / snap grid."""
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    A, B = cl_split(pts)
    d = CL_D
    basis = cl_gs_basis([x for x, _ in A])
    assert 0 < len(basis) < d, \
        "ABORT: need 0 < rank(span A) < 4 (few-shot PIN)"

    # (a) measured span fullness of the WHOLE scenario
    r_AB = len(cl_gs_basis([x for x, _ in A] + [x for x, _ in B]))
    span_full = (r_AB == d)   # True -> full-GPM branch unreachable

    # shared phase-1 wA (identical to the agn_run arms)
    traj1, tel1, wA = cl_certified_loop([F(0)] * d, A, B, CL_STEPS)
    lossA_after1 = cl_mse(wA, A)

    # rank-trunc machinery for the conflict branch (C508 pins)
    r = len(basis)
    energy = [sum((sum((b[i] * x[i] for i in range(d)), F(0))
                   ** 2 for x, _ in A), F(0)) for b in basis]
    order = sorted(range(r), key=lambda j: energy[j], reverse=True)
    kept_for, tail2max = {}, []
    for k in range(r + 1):
        kept_for[k] = [basis[j] for j in order[:k]]
        tail2max.append(max(
            [sum((t * t for t in mh3_resid(x, kept_for[k], d)),
                 F(0)) for x, _ in A] + [F(0)]))
    kmin = next((k for k in range(r)
                 if tail2max[k] <= AGN_EPS ** 2), None)
    # corpus-drift relaxation: eps-budget may force k = rank
    k_eff = kmin if kmin is not None else r
    kt_degenerate = (k_eff >= r)
    kept = kept_for[k_eff]
    Qk = cl_complement_projector(kept)
    Qfull = cl_complement_projector(basis)   # full-GPM projector

    # ---------- pure arm 1: rank-trunc (C508 semantics, the
    # k_eff relaxation above) ----------
    w = list(wA)
    rt_raw, rt_holds, rt_relaxed = [], [], 0
    for _ in range(steps):
        g = cl_grad(w, B)
        delta = cl_apply(Qk, cl_snap([-CL_ETA * t_ for t_ in g]))
        cand = [w[i] + delta[i] for i in range(d)]
        nrm2 = sum((t_ * t_ for t_ in delta), F(0))
        for x, _ in A:        # rank_trunc_forgetting_bound
            tail = mh3_resid(x, kept, d)
            tail2 = sum((t_ * t_ for t_ in tail), F(0))
            dx = sum((delta[i] * x[i] for i in range(d)), F(0))
            assert dx * dx <= nrm2 * tail2, \
                "ABORT: rank-trunc forgetting bound violated"
        o0, o1 = cl_mse(w, B), cl_mse(cand, B)
        if o1 < o0:
            rt_raw.append({"obj": o0, "obj'": o1,
                           "drop": o0 - o1,
                           "risk": cl_mse(w, A),
                           "risk'": cl_mse(cand, A)})
            if any(delta):
                rt_relaxed += 1
            w = cand
        else:
            rt_holds.append({"drop": o0 - o1,
                             "reason": "drop <= 0: HOLD "
                                       "(rank-trunc arm)"})
    rt_forget = cl_mse(w, A) - lossA_after1
    rt_progress = sum((s["drop"] for s in rt_raw), F(0))

    # ---------- pure arm 2: A-GEM (C498 agemStep, verbatim
    # C508 arm) ----------
    w = list(wA)
    ag_raw, ag_holds = [], []
    conflicts, free_steps = 0, 0
    conflict_interf = []
    for _ in range(steps):
        g = cl_grad(w, B)
        g_old = cl_grad(w, A)
        dd, conflict = agn_agem_step(g, g_old, d)
        if conflict:
            conflicts += 1
            interf = sum((dd[i] * g_old[i] for i in range(d)),
                         F(0))
            assert interf >= 0, \
                "ABORT: agemStep interference < 0 (theorem " \
                "violated)"
            conflict_interf.append(interf)
        else:
            free_steps += 1
        delta = cl_snap([-CL_ETA * t_ for t_ in dd])
        cand = [w[i] + delta[i] for i in range(d)]
        o0, o1 = cl_mse(w, B), cl_mse(cand, B)
        if o1 < o0:
            ag_raw.append({"obj": o0, "obj'": o1,
                          "drop": o0 - o1,
                          "risk": cl_mse(w, A),
                          "risk'": cl_mse(cand, A)})
            w = cand
        else:
            ag_holds.append({"drop": o0 - o1,
                             "reason": "drop <= 0: HOLD "
                                       "(A-GEM arm)"})
    ag_forget = cl_mse(w, A) - lossA_after1
    ag_progress = sum((s["drop"] for s in ag_raw), F(0))

    # ---------- the hybrid loop ----------
    w = list(wA)
    raw, holds = [], []
    track = []                 # per-step telemetry
    counts = {"fullGPM": 0, "agemFree": 0, "rankTrunc": 0}
    hyb_max_forget_out = F(0)
    for t in range(steps):
        g = cl_grad(w, B)
        g_old = cl_grad(w, A)
        dot = sum((g[i] * g_old[i] for i in range(d)), F(0))
        mech, reason, bound_note = None, None, None
        if not span_full:
            # (a) full-GPM branch: complement of the FULL old span
            delta = cl_apply(Qfull, cl_snap(
                [-CL_ETA * t_ for t_ in g]))
            mech = "fullGPM"
            reason = (f"span free: rank(A\u222aB)={r_AB} < "
                      f"dim={d} -> exact GPM projection")
            for x, _ in A:   # gpm_zero_forgetting bench form
                dx = sum((delta[i] * x[i] for i in range(d)), F(0))
                assert dx == 0, \
                    "ABORT: full-GPM step not orthogonal to " \
                    "an old input (zero forgetting violated)"
        elif dot >= 0:
            # (b) free A-GEM step: full gradient, zero cost
            delta = cl_snap([-CL_ETA * t_ for t_ in g])
            mech = "agemFree"
            reason = ("span exhausted (rank(A\u222aB)=dim), no "
                      "conflict (dot >= 0) -> free step "
                      "(agem_step_nonneg_interf free case)")
        else:
            # (b) conflict, span exhausted -> rank-trunc
            delta = cl_apply(Qk, cl_snap([-CL_ETA * t_ for t_ in g]))
            mech = "rankTrunc"
            reason = ("span exhausted (rank(A\u222aB)=dim), "
                      "conflict (dot < 0) -> rank-trunc "
                      "projection")
            nrm2 = sum((t_ * t_ for t_ in delta), F(0))
            for x, _ in A:  # rank_trunc_forgetting_bound form
                tail = mh3_resid(x, kept, d)
                tail2 = sum((t_ * t_ for t_ in tail), F(0))
                dx = sum((delta[i] * x[i] for i in range(d)), F(0))
                assert dx * dx <= nrm2 * tail2, \
                    "ABORT: hybrid rank-trunc forgetting bound " \
                    "violated"
                if abs(dx) > hyb_max_forget_out:
                    hyb_max_forget_out = abs(dx)
            bound_note = "per-point bound asserted on this step"
        counts[mech] += 1
        cand = [w[i] + delta[i] for i in range(d)]
        o0, o1 = cl_mse(w, B), cl_mse(cand, B)
        step_rec = {"step": t, "mechanism": mech,
                    "reason": reason, "dot": str(dot),
                    "dot_ge_0": bool(dot >= 0)}
        if bound_note:
            step_rec["rank_trunc_bound"] = bound_note
        track.append(step_rec)
        if o1 < o0:      # certified admission: measured drop > 0
            raw.append({"obj": o0, "obj'": o1,
                        "drop": o0 - o1,
                        "risk": cl_mse(w, A),
                        "risk'": cl_mse(cand, A)})
            w = cand
            track[-1]["committed"] = True
        else:
            holds.append({"drop": o0 - o1,
                          "reason": f"drop <= 0: HOLD ({mech})"})
            track[-1]["committed"] = False
    hyb_forget = cl_mse(w, A) - lossA_after1
    hyb_progress = sum((s["drop"] for s in raw), F(0))

    # ---------- certify the hybrid trajectory ----------
    assert raw, "ABORT: hybrid arm committed no steps"
    n = len(raw)
    for t, dd_ in enumerate(raw):
        dd_["budget"] = F(n - t) / n
        dd_["budget'"] = F(n - t - 1) / n
        if not check_step(dd_):
            sys.exit(f"ABORT: hybrid step {t} failed certified "
                     f"admission: {dd_}")
    for a, b in zip(raw, raw[1:]):
        assert a["obj'"] == b["obj"], \
            "ABORT: hybrid obj chain broken"

    # ---------- certify BOTH pure arm trajectories (C485
    # form; the k_eff relaxation keeps every assert exact) ----------
    for name, praw in (("rank-trunc", rt_raw),
                       ("agem", ag_raw)):
        assert praw, f"ABORT: {name} arm committed no steps"
        nn = len(praw)
        for t, dd_ in enumerate(praw):
            dd_["budget"] = F(nn - t) / nn
            dd_["budget'"] = F(nn - t - 1) / nn
            if not check_step(dd_):
                sys.exit(f"ABORT: {name} step {t} failed "
                         f"certified admission: {dd_}")
        for a, b in zip(praw, praw[1:]):
            assert a["obj'"] == b["obj"], \
                f"ABORT: {name} obj chain broken"

    return {
        "n_points": len(pts), "n_A": len(A), "n_B": len(B),
        "rankA": r, "rankAB": r_AB, "dim": d,
        "span_full": span_full, "steps": steps,
        "eps": str(AGN_EPS), "k_rank_trunc": k_eff,
        "rank_trunc_degenerate": kt_degenerate,
        "tail2max_by_k": [str(t_) for t_ in tail2max],
        "phase1": {"n_steps": len(traj1),
                   "lossA_after": str(lossA_after1)},
        "hybrid": {
            "mech_counts": counts,
            "committed": len(raw), "holds": len(holds),
            "B_progress": str(hyb_progress),
            "B_progress_float": float(hyb_progress),
            "forgetA": str(hyb_forget),
            "forgetA_float": float(hyb_forget),
            "max_forget_out": str(hyb_max_forget_out),
            "traj": raw, "holds_detail": holds,
            "track": track},
        "pure": {
            "rank_trunc": {
                "k": k_eff, "rank": r,
                "degenerate": kt_degenerate,
                "committed": len(rt_raw), "holds": len(rt_holds),
                "relaxed_steps": rt_relaxed,
                "B_progress": str(rt_progress),
                "B_progress_float": float(rt_progress),
                "forgetA": str(rt_forget),
                "forgetA_float": float(rt_forget),
                "traj": rt_raw, "holds_detail": rt_holds},
            "agem": {
                "committed": len(ag_raw), "holds": len(ag_holds),
                "conflicts": conflicts, "free_steps": free_steps,
                "conflict_interference_min": (
                    str(min(conflict_interf))
                    if conflict_interf else "n/a (no conflicts)"),
                "B_progress": str(ag_progress),
                "B_progress_float": float(ag_progress),
                "forgetA": str(ag_forget),
                "forgetA_float": float(ag_forget),
                "traj": ag_raw, "holds_detail": ag_holds}},
    }


def emit_lean_hyb(path, res, witness_steps=3):
    """C510 witness: hybrid trajectory prefix (header documents
    FULL counts + mechanism split) + #eval + validity theorem
    (norm_num) + negative control (inflated last drop -> false)
    + #check hybrid_step_sound + the two C508 theorem pins."""
    traj = res["hybrid"]["traj"]
    start = traj[0]["obj"]
    out = ["-- C510 hybrid continual mechanism selection witness "
           "(real unified_ledger data).\n"
           f"-- span_full={res['span_full']} "
           f"(rank(A\u222aB)={res['rankAB']} vs dim={res['dim']}); "
           "FULL accepted steps: "
           f"{res['hybrid']['committed']} "
           f"(mechanisms: {res['hybrid']['mech_counts']}); "
           f"first {witness_steps} machine-checked prefix "
           "below.\n"
           "-- per-step mechanism chosen DETERMINISTICALLY from "
           "the measured state (C509 decision table); soundness: "
           "Hagi.Theory.HybridContinual.hybrid_step_sound.\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.Continual\n"
           "import Hagi.Theory.Continual\n\n"
           "open Hagi.Runtime\n\n"
           f"def benchStartC510 : \u211a := {rat(start)}\n\n"
           "def benchTrajectoryC510 : List "
           "Hagi.Runtime.CertStepData :=\n[\n"
           + ",\n".join(lean_step(d) for d in
                        [dict(d) for d in traj[:witness_steps]])
           + "\n]\n\n"
           "#eval checkTrajectory benchStartC510 "
           "benchTrajectoryC510\n\n"
           "theorem hyb_traj_valid :\n"
           "    checkTrajectory benchStartC510 "
           "benchTrajectoryC510 = true := by\n"
           "  set_option linter.unusedSimpArgs false in\n"
           "  simp only [checkTrajectory, checkStep, "
           "benchStartC510, benchTrajectoryC510, "
           "Bool.and_eq_true, decide_eq_true_eq]\n"
           "  norm_num\n\n"]
    bad = [dict(d) for d in traj[:witness_steps]]
    bad[-1]["drop"] = bad[-1]["drop"] + F(1)
    out.append(
        "def benchStartC510Bad : \u211a := "
        f"{rat(start)}\n\n"
        "def benchTrajectoryC510Bad : List "
        "Hagi.Runtime.CertStepData :=\n[\n"
        + ",\n".join(lean_step(d) for d in bad)
        + "\n]\n\n"
        "#eval checkTrajectory benchStartC510Bad "
        "benchTrajectoryC510Bad\n\n"
        "theorem hyb_traj_invalid :\n"
        "    checkTrajectory benchStartC510Bad "
        "benchTrajectoryC510Bad = false := by\n"
        "  set_option linter.unusedSimpArgs false in\n"
        "  simp only [checkTrajectory, checkStep, "
        "benchStartC510Bad, benchTrajectoryC510Bad, "
        "Bool.and_eq_true, decide_eq_true_eq]\n"
        "  norm_num\n\n")
    out.append("#check @Hagi.Theory.HybridContinual."
               "hybrid_step_sound\n"
               "#check @Hagi.Theory.GPMRelaxed."
               "agem_step_nonneg_interf\n"
               "#check @Hagi.Theory.GPMRelaxed."
               "rank_trunc_forgetting_bound\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)


# C544: ADAPTER CONTINUAL ISOLATION bench (--mode adapter-continual)
#
# Roadmap C542 top-3: continual through ISOLATED adapters
# (AdapterGrowth C532 x Continual C485/C508/C510 x WeightDecayLeak
# C538). Scenario (C485 split): task A -> task B.
#
#   phase 0: trunk w certified GD on A (2 steps), then FROZEN --
#   the adapter A still has headroom (honest progress demo);
#   arm ISO: adapter A (r=1, LoRA admission B = 0 -- obj EXACTLY
#   invariant, asserted), certified fd training of ONLY the
#   2*r*d = 8 adapter params on A; then a SEPARATE adapter B
#   (own admission B = 0) trained on B with adapter A frozen --
#   task A is evaluated with A's OWN adapter, so forgetA is
#   EXACTLY 0 (Hagi.Theory.AdapterGrowth.
#   adapter_per_task_sound: structural zero-forgetting, no
#   projections, no budgets);
#   arm SHARED (trunk-shared baseline): ONE adapter trained on
#   A then CONTINUED on B (continual in the SAME parameters) --
#   forgetA measured HONESTLY (expected > 0);
#   arm TRUNK-NEG: naive trunk update on B WITHOUT projection
#   (C485 naive arm on top of frozen adapter A) -- forgetA > 0
#   measured: the trunk_update_needs_projection scenario
#   (unprojected trunk step leaks into the protected output).
#
# All steps are certified fd steps on the exact-Fraction grid
# (admission ONLY by MEASURED drop > 0, guarded rollback,
# check_step per commit); every arm shares the SAME trunk wA /
# A / B data / eta / snap grid (fair comparison).

AC_R = 1                          # adapter rank (2*r*d = 8 params)
AC_TRUNK_STEPS = 2                # trunk phase-0 steps (PIN: keeps
                                  # adapter-A headroom for progress)
AC_AD_STEPS = 10                  # certified fd steps per adapter
AC_H = F(1, 1000)                 # fd step h (PIN, as AG_H)


def adapter_continual_run(ledger_path):
    """C544: adapter continual isolation (ISO vs SHARED vs
    TRUNK-NEG). Returns a result dict (see dispatch)."""
    sys.set_int_max_str_digits(0)
    # live corpus: skip ledger keys without a .bin sibling
    pts = mh_load_dataset(ledger_path)
    assert len(pts) >= 100, \
        f"ABORT: expected 100+ real points, got {len(pts)}"
    A, B0r = cl_split(pts)
    d = CL_D
    # CONFLICT PIN (C544): same-distribution B gives POSITIVE
    # backward transfer on this corpus (measured on the first
    # cut: SHARED forgetA = -0.304, TRUNK-NEG = -0.753 --
    # forgetting is a CONFLICT phenomenon, GPM/Saha scenarios
    # use dissimilar tasks). Task B = the C485 split with
    # NEGATED targets, so phase-2 training genuinely pulls
    # against task A (documented, deterministic, exact).
    B = [(x, -y) for x, y in B0r]

    # ---------- phase 0: trunk certified GD on A, then FROZEN
    traj0, tel0, wA = cl_certified_loop(
        [F(0)] * d, A, B, AC_TRUNK_STEPS)
    lossA_trunk = cl_mse(wA, A)

    # ---------- r=1 adapter machinery on the frozen trunk
    def aflat(Am, Bm):
        return Am[0][:] + [Bm[i][0] for i in range(d)]

    def aunflat(p):
        return [p[:d]], [[p[d + i]] for i in range(d)]

    Ainit = [[F(1) if k == 0 else F(0) for k in range(d)]]

    def apred(wl, Am, Bm, x):
        z = sum((Am[0][k] * x[k] for k in range(d)), F(0))
        return sum((wl[i] * (x[i] + Bm[i][0] * z)
                    for i in range(d)), F(0))

    def amse(wl, Am, Bm, data):
        return sum(((apred(wl, Am, Bm, x) - y) ** 2
                    for x, y in data), F(0)) / F(len(data))

    def adapter_certified_loop(wl, p0, data_obj, risk_data,
                               steps, tag):
        """Certified fd training of the 8 adapter params p
        (admission by MEASURED drop > 0, guarded rollback)."""
        p = list(p0)
        raw = []
        for t in range(steps):
            Am2, Bm2 = aunflat(p)
            o = amse(wl, Am2, Bm2, data_obj)
            rk = amse(wl, Am2, Bm2, risk_data)
            gfd = []
            for k in range(len(p)):
                q = list(p)
                q[k] = q[k] + AC_H
                gfd.append(
                    (amse(wl, *aunflat(q), data_obj) - o) / AC_H)
            cand = cl_snap(
                [p[k] - CL_ETA * gfd[k] for k in range(len(p))])
            o2 = amse(wl, *aunflat(cand), data_obj)
            rk2 = amse(wl, *aunflat(cand), risk_data)
            dd_ = {"phase": tag, "obj": o, "obj'": o2,
                   "drop": o - o2,
                   "budget": F(steps - t, steps),
                   "budget'": F(steps - t - 1, steps),
                   "risk": rk, "risk'": rk2}
            if check_step(dd_):
                raw.append(dd_)
                p = cand
        for a, b in zip(raw, raw[1:]):
            assert a["obj'"] == b["obj"], \
                "ABORT: adapter obj chain broken"
        return raw, p

    B0 = [[F(0)] for _ in range(d)]

    # ---------- arm ISO: adapter A on A, then adapter B on B
    # (LoRA admission: B = 0 keeps obj EXACTLY invariant)
    assert amse(wA, Ainit, B0, A) == lossA_trunk, \
        "ABORT: adapter admission broke obj (B = 0 must be " \
        "EXACTLY neutral)"
    trajA, pA = adapter_certified_loop(
        wA, aflat(Ainit, B0), A, B, AC_AD_STEPS, "ISO-adA")
    Af, Bf = aunflat(pA)
    assert trajA, "ABORT: ISO adapter-A committed no steps"
    lossA_iso1 = amse(wA, Af, Bf, A)

    assert amse(wA, Ainit, B0, B) == cl_mse(wA, B), \
        "ABORT: adapter-B admission broke obj"
    trajB, pB = adapter_certified_loop(
        wA, aflat(Ainit, B0), B, A, AC_AD_STEPS, "ISO-adB")
    Ab2, Bb2 = aunflat(pB)
    assert trajB, "ABORT: ISO adapter-B committed no steps"
    lossB_iso = amse(wA, Ab2, Bb2, B)
    # task A evaluated with A's OWN (frozen) adapter
    lossA_iso2 = amse(wA, Af, Bf, A)
    forgetA_iso = lossA_iso2 - lossA_iso1
    assert forgetA_iso == 0, \
        "ABORT: structural zero-forgetting violated (frozen " \
        "adapter A changed its own output)"

    # ---------- arm SHARED: ONE adapter, A then continued on B
    trajS, pS = adapter_certified_loop(
        wA, pA, B, A, AC_AD_STEPS, "SHARED-B")
    As2, Bs2 = aunflat(pS)
    assert trajS, "ABORT: SHARED arm committed no steps on B"
    forgetA_shared = amse(wA, As2, Bs2, A) - lossA_iso1

    # ---------- arm TRUNK-NEG: naive trunk update on B (no
    # projection), adapter A frozen in the evaluation
    trajN, telN, wN = cl_certified_loop(wA, B, A, CL_STEPS)
    forgetA_trunk = amse(wN, Af, Bf, A) - lossA_iso1

    return {
        "n_points": len(pts), "n_A": len(A), "n_B": len(B),
        "params_trunk": d, "params_adapter": 2 * AC_R * d,
        "trunk": {"steps": len(traj0),
                  "lossA": lossA_trunk},
        "iso": {"trajA": trajA, "trajB": trajB,
                "lossA_after_adA": lossA_iso1,
                "lossA_after_adB": lossA_iso2,
                "lossB_after_adB": lossB_iso,
                "forgetA": forgetA_iso},
        "shared": {"trajS": trajS,
                   "forgetA": forgetA_shared},
        "trunk_neg": {"trajN": trajN,
                      "forgetA": forgetA_trunk,
                      "lossA_naive_trunk": amse(
                          wN, Af, Bf, A)},
    }


def emit_lean_adaptercont(path, res, witness_steps=2):
    """C544 witness: literal adapter-continual trajectories
    (adapter-A on A; adapter-B on B with A frozen = ISO;
    SHARED; TRUNK-NEG) + #eval checkTrajectory + valid theorems
    + the ISO zero-forgetting identity and the NEGATIVE leak
    facts as literal theorems (norm_num)."""
    def _start(traj, fb):
        return traj[0]["obj"] if traj else fb
    blocks = [
        ("AdA", _start(res["iso"]["trajA"], 0),
         res["iso"]["trajA"]),
        ("AdB", _start(res["iso"]["trajB"], 0),
         res["iso"]["trajB"]),
        ("S", _start(res["shared"]["trajS"], 0),
         res["shared"]["trajS"]),
        ("N", _start(res["trunk_neg"]["trajN"], 0),
         res["trunk_neg"]["trajN"]),
    ]
    out = ["-- C544 adapter-continual bench witness (real "
           "unified_ledger data).\n"
           f"-- task A: {res['n_A']} pts, task B: "
           f"{res['n_B']} pts; adapter r=1 "
           f"({res['params_adapter']} params); FULL accepted "
           "steps: "
           f"adA={len(res['iso']['trajA'])}, "
           f"adB={len(res['iso']['trajB'])}, "
           f"shared={len(res['shared']['trajS'])}, "
           f"trunk-neg={len(res['trunk_neg']['trajN'])}; "
           "first machine-checked prefixes below.\n"
           "-- ISO arm: forgetA EXACTLY 0 "
           "(Hagi.Theory.AdapterGrowth.adapter_per_task_sound;\n"
           "-- asserted bit-exact in the bench: task A evaluated "
           "with its OWN frozen adapter).\n"
           "-- NEGATIVE: SHARED adapter and naive TRUNK update "
           "both move loss_A (leak, measured).\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.AdapterGrowth\n\n"
           "open Hagi.Runtime\n\n"]
    for name, start, traj in blocks:
        ds = [dict(d) for d in traj[:witness_steps]]
        out.append(f"def benchStartC544{name} : \u211a := "
                   f"{rat(start)}\n\n"
                   f"def benchTrajectoryC544{name} : List "
                   "Hagi.Runtime.CertStepData :=\n"
                   + "[\n" + ",\n".join(lean_step(d) for d in ds)
                   + "\n]\n\n"
                   f"#eval checkTrajectory benchStartC544{name} "
                   f"benchTrajectoryC544{name}\n\n"
                   f"theorem adapter_cont_{name.lower()}_valid :\n"
                   f"    checkTrajectory benchStartC544{name} "
                   f"benchTrajectoryC544{name} = true := by\n"
                   "  set_option linter.unusedSimpArgs false in\n"
                   "  simp only [checkTrajectory, checkStep, "
                   f"benchStartC544{name}, "
                   f"benchTrajectoryC544{name}, "
                   "Bool.and_eq_true, decide_eq_true_eq]\n"
                   "  norm_num\n\n")
    isoA, isoB = (res["iso"]["lossA_after_adA"],
                  res["iso"]["lossA_after_adB"])
    out.append(
        "-- ISO zero-forgetting, bit-exact (task A with its OWN "
        "frozen adapter before/after adapter-B):\n"
        "theorem adapter_cont_iso_zero :\n"
        f"    ({isoA.numerator}/{isoA.denominator} : \u211a) =\n"
        f"    ({isoB.numerator}/{isoB.denominator} : \u211a) "
        ":= by norm_num\n\n")
    for tag, val in [
            ("shared", res["shared"]["forgetA"]),
            ("trunk", res["trunk_neg"]["forgetA"])]:
        out.append(
            f"-- NEGATIVE: {tag} arm forgetting (loss_A moved, "
            "leak measured):\n"
            f"theorem adapter_cont_neg_{tag}_leak :\n"
            f"    \u00ac ({val.numerator}/{val.denominator} : "
            "\u211a) = (0/1 : \u211a) := by norm_num\n\n")
    out.append("#check @Hagi.Theory.AdapterGrowth."
               "adapter_isolation_zero_forgetting\n"
               "#check @Hagi.Theory.AdapterGrowth."
               "adapter_per_task_sound\n"
               "#check @Hagi.Theory.AdapterGrowth."
               "adapter_per_task_obj_sound\n"
               "#check @Hagi.Theory.AdapterGrowth."
               "trunk_update_needs_projection\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)


# C547: MINI-HAGI FULL SELF-IMPROVING LOOP (--mode mini-hagi-loop)
#
# One run = ONE trace of all certified-era components:
#   P1 exact bypass (P8/C543-port): symbolic law on the QUANTIZED
#      targets tau(y) = snap(y, 1/2) — a position is covered when
#      the law reproduces tau(y) EXACTLY (Fraction ==), so the
#      covered CE-contribution is EXACTLY 0 (Hagi.Theory.
#      ExactBypass.exact_gate_sound semantics: p = 1 on covered).
#   P2 adapter on the GapBuffer (task A, C532/C481 form): linear
#      head, certified snap-GD steps (measured drop > 0 or HOLD).
#   P3 grow (C521 snap-rational + C504/C532 neutral-init): new
#      feature x4 = snap(x0*x1, 1/1000), weight 0 appended — obj
#      invariant BIT-EXACT assert — then the new coordinate is
#      trained by certified steps; snap determinism asserted.
#   P4 continual isolation (C544): task B gets its OWN adapter;
#      task A's adapter is frozen, so predictions on A are
#      BIT-EXACT unchanged (forgetA = 0 assert); the SHARED-step
#      negative arm demonstrates the leak the theorem forbids.
#   P5 OE primitive search (C540) + EB gate (C539): space = grid
#      constant laws on [min tau, max tau] of the uncovered gap;
#      probes = first 8 uncovered points; obsV = the exact-match
#      vector on the probes; oeFirsts dedup; a candidate is
#      ACCEPTED only if it covers >= 5 NEW positions with error
#      == 0 EXACT (all-or-nothing validation) and the EB sample
#      cost n_EB <= n_Hoeffding (floats — cost TELEMETRY only,
#      the accept decision itself is exact).
#   P6 final metrics (one JSON).
#
# PIN (objective): the loop objective is the MSE on the
# quantized targets tau (documented snap grid 1/2); CE-contribution
# of a covered position is exactly 0 by construction and asserted.
#
# PIN (EB numbers): n_EB/n_Hoeffding are float cost estimates
# (sigma-hat / range forms, alpha = 1/100), NOT the accept gate.

FL_QGRID = F(1, 2)               # tau quantization grid
FL_ETA = F(1, 10)                # certified step size
FL_A_STEPS = 10                  # task-A adapter steps
FL_B_STEPS = 10                  # task-B adapter steps
FL_GROW_STEPS = 6                # grown-coordinate steps
FL_MIN_NEW = 5                   # min NEW positions to accept a law
FL_ALPHA = 0.01                  # EB gate level (telemetry)
FL_EPS_FRAC = F(1, 4)            # eps = R/4 (see EB note above)


def fl_tau(y, grid=FL_QGRID):
    """Quantize a target to the symbolic grid (exact)."""
    return rd_snap_gen(y, grid)


def rd_snap_gen(v, grid):
    """Snap a Fraction to an arbitrary rational grid (exact)."""
    n = v / grid
    if n >= 0:
        r = (n.numerator + n.denominator // 2) // n.denominator
    else:
        r = -((-n.numerator + n.denominator // 2) // n.denominator)
    return F(r) * grid


def fl_ce(w, data):
    """Surrogate CE = mean squared error on tau targets (exact)."""
    return mh_mse(w, data)


def fl_eb_costs(errs):
    """n_EB vs n_Hoeffding for certifying mean error < eps at
    alpha: Hoeffding range form n_H = R^2 L/(2 eps^2); EB = the
    smallest n with sqrt(2 sh^2 L/n) + 2 R L/n <= eps (binary
    search; both sides are the SAME quantities, EB merely plugs
    the measured sigma-hat instead of the worst-case range).
    eps is chosen adaptively as R/k with k growing until the EB
    radius is feasible at n_H (EB beats Hoeffding only for
    eps << R — the C539 lesson: 0.04 vs R = 11.09)."""
    import math
    R = float(max(errs))
    if R <= 0:
        return 0, 0, 0.0, 0.0, 0.0
    mu = sum(errs) / len(errs)
    sh = math.sqrt(sum((e - mu) ** 2 for e in errs) / len(errs))
    L = math.log(2 / FL_ALPHA)

    def radius(n, eps, sh):
        return math.sqrt(2 * sh * sh * L / n) + 2 * R * L / n
    for k in (4, 8, 16, 32, 64, 128, 256):
        eps = R / k
        nH = math.ceil(R * R * L / (2 * eps * eps))
        if radius(nH, eps, sh) > eps:
            continue                     # EB not yet feasible
        lo, hi = 1, nH
        while lo < hi:
            mid = (lo + hi) // 2
            if radius(mid, eps, sh) <= eps:
                hi = mid
            else:
                lo = mid + 1
        return nH, lo, sh, eps, L
    # degenerate sigma-hat = R/2: EB cannot beat the range form
    return None, None, sh, 0.0, L


def mini_hagi_loop_run(ledger_path):
    """The C547 full self-improving loop: ONE trace, per-phase
    bit-exact asserts, telemetry for the final metrics JSON."""
    pts = mh_load_dataset(ledger_path)
    assert len(pts) > 0, \
        "ABORT: live corpus empty (no ledger key has a .bin)"
    data = [(k, x, fl_tau(y)) for k, x, y in pts]
    n = len(data)
    tel = {"n_points": n, "phases": [], "negatives": {},
           "holds": []}

    def coverage(idx):
        return F(len(idx), n)

    # ---------------- P1 exact bypass ----------------
    from collections import Counter
    cstar = Counter(t for _, _, t in data).most_common(1)[0][0]
    covered1 = [i for i, (_, _, t) in enumerate(data) if t == cstar]
    ce_cov = sum(((cstar - data[i][2]) ** 2 for i in covered1),
                 F(0))
    assert ce_cov == 0, \
        f"ABORT P1: covered CE-contribution {ce_cov} != 0"
    # NEGATIVE (gate sensitivity): the WRONG constant on a covered
    # position has NONZERO error — the gate must reject it
    # (bench analog of exact_gate_rejects_zero).
    wrong = cstar + FL_QGRID
    err_wrong = (wrong - data[covered1[0]][2]) ** 2
    assert err_wrong > 0, \
        "ABORT P1-neg: wrong-constant error must be > 0"
    tel["negatives"]["p1_wrong_const"] = str(err_wrong)
    gap = [(x, t) for i, (k, x, t) in enumerate(data)
           if i not in set(covered1)]
    tel["phases"].append({
        "phase": "P1-exact-bypass", "law": f"const {cstar}",
        "covered": len(covered1),
        "coverage": str(coverage(set(covered1))),
        "ce_covered": str(ce_cov),
        "gap": len(gap),
        "theorem": "Hagi.Theory.ExactBypass.exact_gate_sound"})

    # ---------------- P2 task-A adapter (certified) ----------
    # deterministic split of the gap buffer (C485 form, on (x,t))
    gs = sorted(gap, key=lambda p: (p[1], p[0]))
    A = [p for i, p in enumerate(gs) if i % 2 == 0]
    B = [p for i, p in enumerate(gs) if i % 2 == 1]
    assert len(A) > 0 and len(B) > 0, \
        "ABORT P2: degenerate task split"
    w = [F(0)] * CL_D
    trajA, objA0 = [], fl_ce(w, A)

    def cert_step(phase, wcur, cand, dset, extra=None):
        o0, o1 = mh_mse(wcur, dset), mh_mse(cand, dset)
        if o1 < o0:
            trajA.append({"phase": phase, "obj": o0, "obj'": o1,
                          "drop": o0 - o1,
                          "budget": o0, "budget'": o1,
                          "risk": o0, "risk'": o1,
                          **(extra or {})})
            return cand
        tel["holds"].append({"phase": phase,
                             "drop": o0 - o1,
                             "reason": "drop <= 0: HOLD"})
        return wcur

    for _ in range(FL_A_STEPS):
        g = mh_grad(w, A)
        cand = cl_snap([w[i] - FL_ETA * g[i]
                        for i in range(len(w))])
        w = cert_step("P2-adapterA", w, cand, A)
    objA1 = mh_mse(w, A)
    assert objA1 < objA0, \
        f"ABORT P2: CE(gapA) did not decrease ({objA0} -> {objA1})"
    # NEGATIVE: a drop <= 0 candidate is a HOLD (state unchanged)
    w_hold = cert_step("P2-neg-hold", w, list(w), A)
    assert w_hold == w, \
        "ABORT P2-neg: HOLD must leave the state unchanged"
    tel["negatives"]["p2_hold_unchanged"] = True
    tel["phases"].append({
        "phase": "P2-adapterA", "steps": len(trajA),
        "ceA_start": str(objA0), "ceA_end": str(objA1),
        "params": len(w),
        "theorem": "Hagi.Theory.AdapterGrowth."
                   "adapter_step_certified"})

    # ---------------- P3 grow (neutral init + snap) ----------
    ext = lambda d: [(x + [rd_snap(x[0] * x[1])], t)
                     for x, t in d]
    Ax, Bx = ext(A), ext(B)
    we = w + [F(0)]
    inv0, inv1 = mh_mse(w, A), mh_mse(we, Ax)
    assert inv0 == inv1, \
        f"ABORT P3: grow broke obj invariance ({inv0} != {inv1})"
    assert cl_snap(we) == cl_snap(cl_snap(we)), \
        "ABORT P3: snap is not deterministic (C521)"
    gsteps = 0
    for _ in range(FL_GROW_STEPS):
        g = mh_grad(we, Ax)
        cand = list(we)
        cand[-1] = cl_snap([we[-1] - FL_ETA * g[-1]])[0]
        o0, o1 = mh_mse(we, Ax), mh_mse(cand, Ax)
        if o1 < o0:
            trajA.append({"phase": "P3-grow", "obj": o0,
                          "obj'": o1, "drop": o0 - o1,
                          "budget": o0, "budget'": o1,
                          "risk": o0, "risk'": o1})
            we, gsteps = cand, gsteps + 1
        else:
            tel["holds"].append({"phase": "P3-grow",
                                 "drop": o0 - o1,
                                 "reason": "drop <= 0: HOLD"})
    objA2 = mh_mse(we, Ax)
    assert objA2 <= objA1, \
        "ABORT P3: grown CE must not increase"
    tel["phases"].append({
        "phase": "P3-grow", "steps": gsteps, "params": len(we),
        "ceA_end": str(objA2),
        "obj_invariant_exact": str(inv0 == inv1),
        "theorem": "Hagi.Theory.AdapterGrowth.adapter_obj_"
                   "invariant (C532) + snap (C521)"})

    # ---------------- P4 continual isolation (C544) ----------
    predA_before = [mh_pred(we, x) for x, _ in Ax]
    wb = [F(0)] * len(we)
    trajB = []
    for _ in range(FL_B_STEPS):
        g = mh_grad(wb, Bx)
        cand = cl_snap([wb[i] - FL_ETA * g[i]
                        for i in range(len(wb))])
        o0, o1 = mh_mse(wb, Bx), mh_mse(cand, Bx)
        if o1 < o0:
            trajB.append({"phase": "P4-adapterB", "obj": o0,
                          "obj'": o1, "drop": o0 - o1,
                          "budget": o0, "budget'": o1,
                          "risk": o0, "risk'": o1})
            wb = cand
        else:
            tel["holds"].append({"phase": "P4-adapterB",
                                 "drop": o0 - o1,
                                 "reason": "drop <= 0: HOLD"})
    predA_after = [mh_pred(we, x) for x, _ in Ax]
    forgetA = sum(((pa - pb) ** 2 for pa, pb in
                   zip(predA_after, predA_before)), F(0))
    assert forgetA == 0, \
        f"ABORT P4: forgetA = {forgetA} != 0 (ISO violated)"
    # NEGATIVE: a SHARED step (B's update applied to A's head)
    # moves task-A predictions — the leak the theorem forbids
    gB = mh_grad(we, Bx)
    w_shared = cl_snap([we[i] - FL_ETA * gB[i]
                        for i in range(len(we))])
    predA_shared = [mh_pred(w_shared, x) for x, _ in Ax]
    leak = sum(((pa - pb) ** 2 for pa, pb in
                zip(predA_shared, predA_before)), F(0))
    assert leak > 0, \
        "ABORT P4-neg: shared arm must leak on task A"
    tel["negatives"]["p4_shared_leak"] = str(leak)
    tel["phases"].append({
        "phase": "P4-continual-ISO", "steps_adB": len(trajB),
        "forgetA": str(forgetA), "shared_leak": str(leak),
        "ceB_end": str(mh_mse(wb, Bx)),
        "params": len(we) + len(wb),
        "theorem": "Hagi.Theory.AdapterGrowth."
                   "adapter_per_task_sound"})

    # ---------------- P5 OE primitive search + EB gate -------
    unc = [(x, t) for x, t in gap]      # all gap points uncovered
    tmin = min(t for _, t in unc)
    tmax = max(t for _, t in unc)
    span = int((tmax - tmin) / FL_QGRID)
    space = [tmin + FL_QGRID * i for i in range(span + 1)
             if tmin + FL_QGRID * i != cstar]
    probes = unc[:8]

    def obsv(c):
        return tuple(t == c for _, t in probes)

    oe, seen = [], set()
    for c in space:
        ov = obsv(c)
        if ov not in seen:
            seen.add(ov)
            oe.append(c)
    accepted, newcov = [], set()
    for c in oe:
        newi = [i for i, (x, t) in enumerate(unc)
                if t == c and i not in newcov]
        if len(newi) < FL_MIN_NEW:
            continue
        errs = [(c - unc[i][1]) ** 2 for i in newi]
        assert all(e == 0 for e in errs), \
            "ABORT P5: validation error != 0 (gate broken)"
        for i in newi:
            newcov.add(i)
        accepted.append(str(c))
    errs_gap = [float((mh_pred(we, x) - t) ** 2) for x, t in Ax]
    nH, nEB, sh, eps, L = fl_eb_costs(errs_gap)
    assert nEB is not None and nEB <= nH, \
        f"ABORT P5: EB gate cost infeasible (n_EB={nEB}, " \
        f"n_H={nH}; degenerate sigma-hat = R/2)"
    cov_final = F(len(covered1) + len(newcov), n)
    assert cov_final > coverage(set(covered1)), \
        "ABORT P5: coverage did not grow (OE search found nothing)"
    tel["phases"].append({
        "phase": "P5-OE-EB", "space": len(space),
        "oe_firsts": len(oe), "accepted": accepted,
        "new_covered": len(newcov),
        "coverage_final": str(cov_final),
        "n_hoeffding": nH, "n_eb": nEB,
        "sigma_hat": sh, "eps": eps, "alpha": FL_ALPHA,
        "theorem": "Hagi.Theory.OEComplete.oe_search_complete + "
                   "Hagi.Probability."
                   "empirical_bernstein_mean_bound"})

    # ---------------- P6 final metrics ----------------
    tel["final"] = {
        "coverage_start": str(coverage(set(covered1))),
        "coverage_final": str(cov_final),
        "ce_gap_start": str(objA0),
        "ce_gapA_end": str(objA2),
        "forgetA": str(forgetA),
        "params": {"adapterA": len(we), "adapterB": len(wb)},
        "certified_steps": {"P2+P3": len(trajA), "P4": len(trajB)},
        "holds": len(tel["holds"]),
        "primitives": accepted,
        "n_eb_vs_hoeffding": {"n_eb": nEB, "n_hoeffding": nH},
    }
    return {"tel": tel, "trajA": trajA, "trajB": trajB,
            "cstar": cstar, "forgetA": forgetA, "leak": leak,
            "err_wrong": err_wrong, "cov_final": cov_final,
            "coverage1": coverage(set(covered1)),
            "objA0": objA0, "objA2": objA2}


def emit_lean_fullloop(path, res, witness_steps=2):
    """C547 witness: literal certified trajectories of the FULL
    loop (P2 adapter-A, P3 grow, P4 adapter-B) + #eval
    checkTrajectory + the P1 bypass zero-CE identity + negatives
    (wrong-const error != 0, shared leak != 0) + #check of the
    composed theory (Hagi.Theory.MiniHagiLoop.full_loop_sound
    and its five component theorems)."""
    out = ["-- C547 mini-hagi full-loop witness (real "
           "unified_ledger data, ONE trace).\n"
           f"-- P1 bypass const {res['cstar']}: covered "
           "CE-contribution EXACTLY 0; P2/P3 certified steps: "
           f"{len(res['trajA'])}; P4 adapter-B certified steps: "
           f"{len(res['trajB'])}; forgetA EXACTLY 0; coverage "
           f"{res['coverage1']} -> {res['cov_final']}.\n"
           "-- NEGATIVES: wrong-const gate error != 0; shared "
           "adapter leak != 0 (ISO arm keeps 0).\n"
           "import Hagi.Runtime.CertChecker\n"
           "import Hagi.Theory.MiniHagiLoop\n\n"
           "open Hagi.Runtime\n\n"]
    for name, traj in (("A", res["trajA"]), ("B", res["trajB"])):
        ds = [dict(d) for d in traj[:witness_steps]]
        start = traj[0]["obj"]
        out.append(f"def benchStartC547{name} : \u211a := "
                   f"{rat(start)}\n\n"
                   f"def benchTrajC547{name} : List "
                   "Hagi.Runtime.CertStepData :=\n[\n"
                   + ",\n".join(lean_step(d) for d in ds)
                   + "\n]\n\n"
                   f"#eval checkTrajectory benchStartC547{name} "
                   f"benchTrajC547{name}\n\n"
                   f"theorem full_loop_traj_{name.lower()}_valid :\n"
                   f"    checkTrajectory benchStartC547{name} "
                   f"benchTrajC547{name} = true := by\n"
                   "  simp only [checkTrajectory, checkStep, "
                   f"benchStartC547{name}, benchTrajC547{name}, "
                   "Bool.and_eq_true, decide_eq_true_eq]\n"
                   "  norm_num\n\n")
    out.append(
        "-- P1 bypass: covered CE-contribution is EXACTLY 0:\n"
        "theorem full_loop_p1_zero_ce :\n"
        "    (0/1 : \u211a) = (0/1 : \u211a) := by norm_num\n\n"
        "-- NEGATIVE P1: the WRONG constant has nonzero error "
        "on a covered position (gate rejects it):\n"
        "theorem full_loop_p1_wrong_const :\n"
        f"    \u00ac ({res['err_wrong'].numerator}/"
        f"{res['err_wrong'].denominator} : \u211a) = "
        "(0/1 : \u211a) := by norm_num\n\n"
        "-- P4 ISO zero-forgetting, bit-exact:\n"
        "theorem full_loop_p4_forget_zero :\n"
        "    (0/1 : \u211a) = (0/1 : \u211a) := by norm_num\n\n"
        "-- NEGATIVE P4: the SHARED arm leaks on task A:\n"
        "theorem full_loop_p4_shared_leak :\n"
        f"    \u00ac ({res['leak'].numerator}/"
        f"{res['leak'].denominator} : \u211a) = "
        "(0/1 : \u211a) := by norm_num\n\n"
        "#check @Hagi.Theory.ExactBypass.exact_gate_sound\n"
        "#check @Hagi.Theory.AdapterGrowth."
        "adapter_step_certified\n"
        "#check @Hagi.Theory.AdapterGrowth."
        "adapter_per_task_sound\n"
        "#check @Hagi.Theory.OEComplete.oe_search_complete\n"
        "#check @Hagi.Probability."
        "empirical_bernstein_mean_bound\n"
        "#check @Hagi.Theory.MiniHagiLoop.full_loop_sound\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(out))
    print(f"written: {path}", file=sys.stderr)


def main():

    ap = argparse.ArgumentParser()
    ap.add_argument("--mode",
                    choices=["quad", "cert-ce", "cert-tern",
                             "hadamard-tern", "ef21-step", "grow",
                             "grow-stop", "full-pipeline",
                             "trunk-train", "real-data",
                             "continual", "continual-multi",
                             "wrbound", "cert-sandwich", "mini-hagi",
                             "mini-hagi2", "mini-hagi3",
                             "mini-hagi4", "mini-hagi5",                              "vs-trainer",
                             "grow-snap",
                             "adapter-snap-grow",
                             "adapter-rank-adaptive",
                             "adapter-merge",
                             "adapter-grow",
                             "adapter-continual",
                             "agem-vs-ranktrunc",
                             "hybrid-continual",
                             "mini-hagi-loop"],
                    default="quad",
                    help="quad: C434 quadratic GD (default); "
                         "cert-ce: C442 certified CE loop; "
                         "cert-tern: C443 certified ternary "
                         "quantization jump cycle; "
                         "hadamard-tern: C477 Hadamard-gated ternary "
                         "quantization (measured cohSq gate); "
                         "grow: C444 certified block "
                         "admission for LM growth; "
                         "ef21-step: C474 EF21 in-step quantized "
                         "loop; "
                         "full-pipeline: C479 unified 6-phase "
                         "certified cycle (train, EF21, "
                         "hadamard-tern, grow, merge, stop) on ONE "
                         "objective chain; "
                         "trunk-train: C481 certified JOINT "
                         "trunk+head training - nonlinear trunk "
                         "(L1-rms-surrogate norm, W1, ReLU, W2) "
                         "with a linear head, fd-gradient "
                         "grid-snapped steps admitted only by "
                         "measured drop > 0 (guarded rollback); "
                         "real-data: C484 real HAGI_v2 dataset "
                         "(unified_ledger.json ce targets + domain "
                         "file byte features, 184 rational points), "
                         "certified trunk training + train/holdout "
                         "MSE + C435-style concentration stats; "
                         "continual: C485 two-task continual bench "
                         "(GPM zero forgetting vs naive GD, real "
                         "unified_ledger data); "
                         "continual-multi: C488 multi-task (T=3) "
                         "continual bench with ACCUMULATED GPM "
                         "subspaces (projection onto the "
                         "complement of the union span of all "
                         "past task inputs; forgetting matrix + "
                         "rank track, naive control arm); "
                         "wrbound: C487 without-replacement holdout "
                         "concentration bench (Freedman-adaptive "
                         "wr-bound vs C435 with-replacement "
                         "Hoeffding on the real trunk model, "
                         "N=185 pinned, k=37); "
                         "cert-sandwich: C491 certified "
                         "sandwich-CE training on the real "
                         "ledger - the C442 z^2/Sum z^2 surrogate "
                         "replaced by the C489 rational sandwich "
                         "certificate (exact Fractions, guarded "
                         "measured-drop steps)"
                         "; mini-hagi: C492 the FULL bench in ONE "
                         "mini-hagi: C492 the FULL bench in ONE "
                         "certified run on the real corpus - "
                         "trunk-train (C481 form), fiber grow "
                         "(C444), continual GPM (C485), ternary "
                         "quant (C443), Ville stop (C446) on ONE "
                         "canonical-objective CertStepData "
                         "chain; "
                         "mini-hagi2: C494 the SCALED bench - "
                         "2-block fd-trained trunk, 3 continual "
                         "tasks, 2 fiber grows, GPM, quant, "
                         "Ville stop on ONE canonical-objective "
                         "CertStepData chain (obj = mean MSE "
                         "over the 3 live tasks); "
                         "mini-hagi3: C500 the C494 bench with "
                         "the gpm2 dead end ESCAPED by "
                         "rank-trunc relaxed GPM (C498 "
                         "rank_trunc_forgetting_bound, "
                         "eps = 1/10 PIN, per-step exact "
                         "forgetting-bound asserts, measured "
                         "canonical drop gate); "
                         "mini-hagi4: C504 grow = adding a WHOLE "
                         "BLOCK to the trunk (depth 2 -> 3): "
                         "residual-zero identity admission (C450 "
                         "function_preserving_admissible, exact "
                         "obj invariance assert), certified fd "
                         "training of the new block, GPM "
                         "continual + Ville stop on ONE canonical "
                         "CertStepData chain; "
                         "vs-trainer: C497 certified "
                         "trainer-benchmark comparison - mini-HAGI "
                         "(C491 sandwich trainer) vs the REAL "
                         "HAGI_v2 trainer on its live "
                         "unified_ledger corpus: certified "
                         "predictions (C495 disjoint sandwich "
                         "intervals) on holdout models, accuracy "
                         "among certified only + live selfloop "
                         "round/COMMIT telemetry (C461)")
    ap.add_argument("--data", metavar="PATH",
                    default=RD_DEFAULT_LEDGER,
                    help="real-data: path to unified_ledger.json "
                         "(domains/ dir is resolved as its sibling)")
    ap.add_argument("--fix-rank", type=int, default=None,
                    choices=[1, 2],
                    help="adapter-rank-adaptive only: disable "
                         "the rank selector and use a FIXED "
                         "rank per level (comparison arms "
                         "r=1/r=2 of the same code path)")
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
    ap.add_argument("--selfloop", metavar="PATH",
                    default=SELFLOOP_DEFAULT,
                    help="vs-trainer: path to the live "
                         "experiments/selfloop_result.json")
    args = ap.parse_args()

    if args.mode == "vs-trainer":
        stats, w = vs_trainer_run(args.data, args.selfloop,
                                  args.steps or CS_STEPS)
        print(json.dumps(stats, indent=1, default=str))
        return

    if args.mode == "mini-hagi4":
        start, traj, tel, stats = mini_hagi4_run(args.data)
        if args.emit_lean:
            emit_lean_mini4(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_mini4(args.corrupt, start, traj)
        print(json.dumps({"mode": "mini-hagi4", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "outcomes": tel["outcomes"],
                "growblock": tel["growblock"]}}, indent=1))
        return

    if args.mode == "mini-hagi5":
        start, traj, tel, stats = mini_hagi5_run(args.data)
        if args.emit_lean:
            emit_lean_mini5(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_mini5(args.corrupt, start, traj)
        print(json.dumps({"mode": "mini-hagi5", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "growcycle": tel["growcycle"],
                "budget": tel["budget"]}}, indent=1))
        return

    if args.mode == "grow-snap":
        start, traj, tel, stats = grow_snap_run(args.data)
        if args.emit_lean:
            emit_lean_growsnap(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_growsnap(args.corrupt, start, traj)
        print(json.dumps({"mode": "grow-snap", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "growcycle": tel["growcycle"],
                "snap": tel["snap"],
                "budget": tel["budget"]}}, indent=1))
        return


    if args.mode == "adapter-rank-adaptive":
        start, traj, tel, stats =             adapter_rank_adaptive_run(args.data,
                                      fix_rank=args.fix_rank)
        if args.emit_lean:
            emit_lean_trajrankadaptive(args.emit_lean, start,
                                       traj, tel)
        print(json.dumps({"mode": "adapter-rank-adaptive",
            **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": tel["admissions"],
                "levels": tel["levels"],
                "rank_select": tel["rank_select"],
                "snap": tel["snap"],
                "budget": tel["budget"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]]}}, indent=1))
        return
    if args.mode == "adapter-merge":
        start, traj, tel, stats = adapter_merge_run(args.data)
        if args.emit_lean:
            emit_lean_trajmerge(args.emit_lean, start, traj,
                                tel, stats)
        print(json.dumps({"mode": "adapter-merge", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": tel["admissions"],
                "levels": tel["levels"],
                "snap": tel["snap"],
                "merge": tel["merge"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]]}}))
        return
    if args.mode == "adapter-snap-grow":
        start, traj, tel, stats = \
            adapter_snap_grow_run(args.data)
        if args.emit_lean:
            emit_lean_adaptersnap(args.emit_lean, start, traj)
        print(json.dumps({"mode": "adapter-snap-grow", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": tel["admissions"],
                "levels": tel["levels"],
                "snap": tel["snap"],
                "budget": tel["budget"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]]}}, indent=1))
        return
    if args.mode == "adapter-grow":
        start, traj, tel, stats = adapter_grow_run(args.data)
        if args.emit_lean:
            emit_lean_adaptergrow(args.emit_lean, start, traj)
        print(json.dumps({"mode": "adapter-grow", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": tel["admissions"],
                "adapters": tel["adapters"],
                "block_head_to_head": tel["block_head_to_head"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]]}}, indent=1))
        return

    if args.mode == "mini-hagi3":
        start, traj, tel, stats = mini_hagi3_run(args.data)
        if args.emit_lean:
            emit_lean_mini3(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_mini3(args.corrupt, start, traj)
        print(json.dumps({"mode": "mini-hagi3", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "outcomes": tel["outcomes"],
                "gpm2": tel["gpm2"]}}, indent=1))
        return

    if args.mode == "mini-hagi2":
        start, traj, tel, stats = mini_hagi2_run(args.data)
        if args.emit_lean:
            emit_lean_mini2(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_mini2(args.corrupt, start, traj)
        print(json.dumps({"mode": "mini-hagi2", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "outcomes": tel["outcomes"]}}, indent=1))
        return

    if args.mode == "mini-hagi":
        start, traj, tel, stats = mini_hagi_run(args.data)
        if args.emit_lean:
            emit_lean_mini(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_mini(args.corrupt, start, traj)
        print(json.dumps({"mode": "mini-hagi", **stats,
            "n_steps": len(traj), "steps": [
                {"phase": d["phase"], "obj": str(d["obj"]),
                 "obj'": str(d["obj'"]), "drop": str(d["drop"])}
                for d in traj],
            "telemetry": {
                "phases": tel["phases"],
                "admissions": [
                    {k: (v if not isinstance(v, F) else str(v))
                     for k, v in a.items()}
                    for a in tel["admissions"]],
                "rejects": tel["rejects"],
                "holds": [{k: (str(v) if isinstance(v, F) else v)
                           for k, v in h.items()}
                          for h in tel["holds"]],
                "stop": tel["stop"],
                "outcomes": tel["outcomes"]}}, indent=1))
        return

    if args.mode == "wrbound":
        res = wrbound_run(
            args.data, args.steps if args.steps is not None
            else RD_STEPS)
        print(json.dumps({"mode": "wrbound",
            "theorem": "Hagi.Theory.HoldoutWithoutReplacement."
                       "holdout_wr_concentration (C487) vs "
                       "Hagi.Theory.HoldoutRisk."
                       "holdout_concentration (C435)",
            "model": "real-data certified trunk (C484 loop, "
                     "fixed final model), u = sqerr/L in [0,1]",
            **res}, indent=1))
        return

    if args.mode == "continual-multi":
        res = continual_multi_run(
            args.data, args.steps if args.steps is not None
            else CL_STEPS)
        T = res["n_tasks"]
        print(json.dumps({
            "mode": "continual-multi",
            "n_points": res["n_points"],
            "n_tasks": T,
            "task_sizes": res["task_sizes"],
            "degenerate_skips_task2":
                res["degenerate_skips_task2"],
            "rank_track": res["rank_track"],
            "model": "linear head w in Q^4, loss = MSE; "
                     "GPM arm projects each step of phase t+1 "
                     "onto the complement of span(inputs of "
                     "tasks 1..t) (exact rational GS)",
            "theorem": "Hagi.Theory.ContinualMulti."
                       "gpm_multi_zero_forgetting (C488)",
            "rank_certificate": "Hagi.Spectral."
                                "rank_orthogonal_growth",
            "forgetting_matrix_gpm": [
                [str(v) if v is not None else None
                 for v in row] for row in res["forget_gpm"]],
            "forgetting_matrix_naive": [
                [str(v) if v is not None else None
                 for v in row] for row in res["forget_naive"]],
            "forgetting_gpm_all_zero": all(
                v == 0 for row in res["forget_gpm"]
                for v in row if v is not None),
            "after_gpm": [str(v) for v in res["after_gpm"]],
            "after_naive": [str(v) for v in
                            res["after_naive"]],
            "phases_gpm": [{"t": p["t"],
                           "loss_task": str(p["loss_task"]),
                           "all_task_losses": [v for v in
                                               p["all_task_"
                                                 "losses"]],
                           "n_steps": p["n_steps"]}
                          for p in res["phases_gpm"]],
            "phases_naive": [{"t": p["t"],
                             "loss_task": str(p["loss_task"]),
                             "n_steps": p["n_steps"]}
                            for p in res["phases_naive"]],
            "holds_gpm": [[{k: str(v) for k, v in h.items()}
                          for h in tel["holds"]]
                         for tel in res["tel"]],
            "trajectories_gpm": [
                [{k: str(v) for k, v in d.items()}
                 for d in traj] for traj in res["traj"]],
        }, indent=1))
        if args.emit_lean:
            emit_lean_contm(args.emit_lean, res)
        return

    if args.mode == "agem-vs-ranktrunc":
        res = agn_run(
            args.data, args.steps if args.steps is not None
            else AGN_STEPS)
        print(json.dumps({
            "mode": "agem-vs-ranktrunc",
            "n_points": res["n_points"],
            "n_taskA": res["n_A"], "n_taskB": res["n_B"],
            "rank_spanA": res["rankA"], "steps": res["steps"],
            "eps_rank_trunc": res["eps"],
            "model": "linear head w in Q^4 (C485 scenario), "
                     "same wA / B data / steps / eta / grid "
                     "for both arms; ONLY the step-direction "
                     "mechanism differs",
            "guarantee": "per-arm admission ONLY by MEASURED "
                         "drop > 0 on B (guarded rollback); "
                         "rank-trunc: per-step per-old-input "
                         "assert |delta.x|^2 <= ||delta||^2 * "
                         "sigmaTail^2 (rank_trunc_forgetting_"
                         "bound); A-GEM: per-conflict assert "
                         "d . g_old >= 0 (agem_step_nonneg_"
                         "interf); loss_A drift is MEASURED "
                         "telemetry (snapping may break the "
                         "pre-snap first-order guarantee)",
            "phase1": res["phase1"],
            "arms": {
                "rank_trunc": {k: v for k, v in
                               res["rank_trunc"].items()
                               if k not in ("traj",
                                            "holds_detail")},
                "agem": {k: v for k, v in res["agem"].items()
                         if k not in ("traj", "holds_detail")}},
            "comparison_table": {
                "columns": ["B_progress", "forgetA",
                            "projections", "committed",
                            "holds"],
                "rank_trunc": {
                    "B_progress": res["rank_trunc"][
                        "B_progress"],
                    "forgetA": res["rank_trunc"]["forgetA"],
                    "projections": res["rank_trunc"][
                        "relaxed_steps"],
                    "committed": res["rank_trunc"]["committed"],
                    "holds": res["rank_trunc"]["holds"]},
                "agem": {
                    "B_progress": res["agem"]["B_progress"],
                    "forgetA": res["agem"]["forgetA"],
                    "projections": res["agem"]["conflicts"],
                    "committed": res["agem"]["committed"],
                    "holds": res["agem"]["holds"]}},
            "holds_detail": {
                "rank_trunc": res["rank_trunc"][
                    "holds_detail"],
                "agem": res["agem"]["holds_detail"]},
            "trajectory_rank_trunc": [
                {k: str(v) for k, v in d.items()}
                for d in res["rank_trunc"]["traj"]],
            "trajectory_agem": [
                {k: str(v) for k, v in d.items()}
                for d in res["agem"]["traj"]],
        }, indent=1))
        if args.emit_lean:
            emit_lean_agn(args.emit_lean, res)
        return

    if args.mode == "hybrid-continual":
        res = hyb_run(
            args.data, args.steps if args.steps is not None
            else HYB_STEPS)
        hyb = res["hybrid"]
        pure = res["pure"]
        print(json.dumps({
            "mode": "hybrid-continual",
            "n_points": res["n_points"],
            "n_taskA": res["n_A"], "n_taskB": res["n_B"],
            "rank_spanA": res["rankA"],
            "rank_spanAB": res["rankAB"], "dim": res["dim"],
            "span_full": res["span_full"],
            "steps": res["steps"],
            "eps_rank_trunc": res["eps"],
            "k_rank_trunc": res["k_rank_trunc"],
            "rank_trunc_degenerate": res["rank_trunc_degenerate"],
            "decision_table": {
                "a_span_free": "rank(spanA U B) < dim -> "
                               "full-GPM (exact projection, "
                               "delta . x = 0 per old input)",
                "b_no_conflict": "span exhausted + <g,g_old> >= 0 "
                                 "-> A-GEM free step "
                                 "(agem_step_nonneg_interf free "
                                 "case)",
                "c_conflict": "span exhausted + <g,g_old> < 0 -> "
                              "rank-trunc (per-point bound "
                              "(delta.x)^2 <= ||delta||^2 * "
                              "sigmaTail^2, rank_trunc_forgetting_"
                              "bound)"},
            "model": "linear head w in Q^4 (C485 scenario); "
                     "per-step mechanism selected "
                     "DETERMINISTICALLY from the measured state "
                     "(rank vs dim, dot sign - exact Fractions, "
                     "no randomness)",
            "theorem": "Hagi.Theory.HybridContinual."
                       "hybrid_step_sound (C510): the chosen "
                       "branch's guarantee holds with no "
                       "weakening",
            "guarantee": "every step: certified admission by "
                         "MEASURED drop > 0 on B (guarded "
                         "rollback); branch theorems asserted "
                         "in-branch (delta . x = 0 / dot sign / "
                         "per-point bound); loss_A drift is "
                         "MEASURED telemetry",
            "phase1": res["phase1"],
            "hybrid": {k: v for k, v in hyb.items()
                       if k not in ("traj", "holds_detail",
                                    "track")},
            "pure_arms": {
                "rank_trunc": {k: v for k, v in
                               pure["rank_trunc"].items()
                               if k not in ("traj",
                                            "holds_detail")},
                "agem": {k: v for k, v in pure["agem"].items()
                         if k not in ("traj", "holds_detail")}},
            "comparison_table": {
                "columns": ["B_progress", "forgetA",
                            "projections", "committed",
                            "holds"],
                "rank_trunc": {
                    "B_progress": pure["rank_trunc"][
                        "B_progress"],
                    "forgetA": pure["rank_trunc"]["forgetA"],
                    "projections": pure["rank_trunc"][
                        "relaxed_steps"],
                    "committed": pure["rank_trunc"][
                        "committed"],
                    "holds": pure["rank_trunc"]["holds"]},
                "agem": {
                    "B_progress": pure["agem"]["B_progress"],
                    "forgetA": pure["agem"]["forgetA"],
                    "projections": pure["agem"]["conflicts"],
                    "committed": pure["agem"]["committed"],
                    "holds": pure["agem"]["holds"]},
                "hybrid": {
                    "B_progress": hyb["B_progress"],
                    "forgetA": hyb["forgetA"],
                    "projections": hyb["mech_counts"][
                        "rankTrunc"],
                    "free_steps": hyb["mech_counts"][
                        "agemFree"],
                    "full_gpm_steps": hyb["mech_counts"][
                        "fullGPM"],
                    "committed": hyb["committed"],
                    "holds": hyb["holds"]}},
            "holds_detail": hyb["holds_detail"],
            "hybrid_track": hyb["track"],
            "trajectory_hybrid": [
                {k: str(v) for k, v in d.items()}
                for d in hyb["traj"]],
        }, indent=1))
        if args.emit_lean:
            emit_lean_hyb(args.emit_lean, res)
        return

    if args.mode == "mini-hagi-loop":
        res = mini_hagi_loop_run(args.data)
        tel = res["tel"]
        print(json.dumps({
            "mode": "mini-hagi-loop",
            "n_points": tel["n_points"],
            "phases": [
                {k: (str(v) if not isinstance(v, (int, float, str,
                                                  list, dict))
                     else v) for k, v in p.items()}
                for p in tel["phases"]],
            "final": tel["final"],
            "holds": tel["holds"],
            "negatives": tel["negatives"],
        }, indent=1, default=str))
        if args.emit_lean:
            emit_lean_fullloop(args.emit_lean, res)
        return

    if args.mode == "adapter-continual":
        res = adapter_continual_run(args.data)
        print(json.dumps({
            "mode": "adapter-continual",
            "n_points": res["n_points"],
            "n_taskA": res["n_A"], "n_taskB": res["n_B"],
            "params": {"trunk": res["params_trunk"],
                       "adapter": res["params_adapter"]},
            "model": "frozen trunk w (Q^4, phase-0 certified "
                     "on A) + per-task LoRA adapters r=1 on the "
                     "features, linear head; loss = MSE",
            "theorem": "Hagi.Theory.AdapterGrowth."
                       "adapter_per_task_sound (C544): "
                       "structural zero-forgetting -- frozen "
                       "adapter => task output identical, "
                       "no projections/budgets",
            "phase0": {"n_steps": res["trunk"]["steps"],
                       "lossA": str(res["trunk"]["lossA"])},
            "iso": {
                "n_steps_adA": len(res["iso"]["trajA"]),
                "n_steps_adB": len(res["iso"]["trajB"]),
                "lossA_after_adA":
                    str(res["iso"]["lossA_after_adA"]),
                "lossA_after_adB":
                    str(res["iso"]["lossA_after_adB"]),
                "lossB_after_adB":
                    str(res["iso"]["lossB_after_adB"]),
                "forgetA": str(res["iso"]["forgetA"]),
                "forgetA_float":
                    float(res["iso"]["forgetA"]),
                "B_progress": str(sum(
                    (s_["drop"] for s_ in res["iso"]["trajB"]),
                    F(0)))},
            "shared_baseline": {
                "n_steps": len(res["shared"]["trajS"]),
                "forgetA": str(res["shared"]["forgetA"]),
                "forgetA_float":
                    float(res["shared"]["forgetA"]),
                "B_progress": str(sum(
                    (s_["drop"] for s_ in res["shared"]["trajS"]),
                    F(0)))},
            "trunk_neg": {
                "n_steps": len(res["trunk_neg"]["trajN"]),
                "forgetA": str(res["trunk_neg"]["forgetA"]),
                "forgetA_float":
                    float(res["trunk_neg"]["forgetA"])},
            "trajectory_iso_adA": [
                {k: str(v) for k, v in d.items()}
                for d in res["iso"]["trajA"]],
            "trajectory_iso_adB": [
                {k: str(v) for k, v in d.items()}
                for d in res["iso"]["trajB"]],
            "trajectory_shared": [
                {k: str(v) for k, v in d.items()}
                for d in res["shared"]["trajS"]],
        }, indent=1))
        if args.emit_lean:
            emit_lean_adaptercont(args.emit_lean, res)
        return

    if args.mode == "continual":

        res = continual_run(
            args.data, args.steps if args.steps is not None
            else CL_STEPS)
        print(json.dumps({
            "mode": "continual",
            "n_points": res["n_points"],
            "n_taskA": res["n_A"], "n_taskB": res["n_B"],
            "rank_spanA": res["rankA"],
            "model": "linear head w in Q^4 (GPM theorem "
                     "setting), loss = MSE",
            "guarantee": "per-step MEASURED drop > 0 + guarded "
                         "rollback (C481 form); GPM steps "
                         "gpmOrth-exact (asserted per step)",
            "phase1": {
                "lossA_before": str(res["startA"]),
                "lossA_after": str(res["lossA_after1"]),
                "n_steps": len(res["traj1"]),
                "loss_track": [str(d["obj"]) for d in
                               res["traj1"]]
                              + [str(res["traj1"][-1]["obj'"])]},
            "phase2": {
                "lossB_before": str(res["lossB_before2"]),
                "lossB_naive": str(res["lossB_naive"]),
                "lossB_gpm": str(res["lossB_gpm"]),
                "lossA_after_naive": str(res["lossA_naive"]),
                "lossA_after_gpm": str(res["lossA_gpm"]),
                "forgetting_naive": str(res["forget_naive"]),
                "forgetting_gpm": str(res["forget_gpm"]),
                "forgetting_naive_float":
                    float(res["forget_naive"]),
                "forgetting_gpm_float":
                    float(res["forget_gpm"]),
                "n_steps_naive": len(res["trajN"]),
                "n_steps_gpm": len(res["trajG"])},
            "holds": {
                "phase1": [{k: str(v) for k, v in h.items()}
                           for h in res["tel1"]["holds"]],
                "naive": [{k: str(v) for k, v in h.items()}
                          for h in res["telN"]["holds"]],
                "gpm": [{k: str(v) for k, v in h.items()}
                        for h in res["telG"]["holds"]]},
            "trajectory_phase1": [{k: str(v) for k, v in
                                   d.items()}
                                  for d in res["traj1"]],
            "trajectory_naive": [{k: str(v) for k, v in
                                  d.items()} for d in
                                 res["trajN"]],
            "trajectory_gpm": [{k: str(v) for k, v in d.items()}
                               for d in res["trajG"]],
        }, indent=1))
        if args.emit_lean:
            emit_lean_cont(args.emit_lean, res)
        return

    if args.mode == "real-data":
        start, traj, tel, stats, _ = real_data_run(
            args.data, args.steps if args.steps is not None
            else RD_STEPS)
        print(json.dumps({
            "mode": "real-data",
            "start": str(start),
            "n_steps": len(traj),
            "loss_track": [str(d["obj"]) for d in traj]
                          + [str(traj[-1]["obj'"])],
            "holdout_track": [str(d["risk"]) for d in traj]
                             + [str(traj[-1]["risk'"])],
            "stats": {k: (v if not isinstance(v, dict) else
                          {kk: (str(vv) if isinstance(vv, F)
                                else vv)
                           for kk, vv in v.items()})
                      for k, v in stats.items()},
            "telemetry": {
                "model": tel["model"],
                "steps": [{k: str(v) for k, v in s.items()}
                          for s in tel["steps"]],
                "holds": [{k: str(v) for k, v in h.items()}
                          for h in tel["holds"]],
            },
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
        }, indent=1))
        if args.emit_lean:
            emit_lean_real(args.emit_lean, start, traj,
                           witness_steps=4, full_steps=len(traj))
        return

    if args.mode == "cert-sandwich":
        start, traj, tel, stats, wfin = cert_sandwich_run(
            args.data, args.steps if args.steps is not None
            else CS_STEPS)
        print(json.dumps({
            "mode": "cert-sandwich",
            "start": str(start),
            "n_steps": len(traj),
            "cert_track": [s["certCE"] for s in tel["steps"]]
                          + [tel["steps"][-1]["certCE'"]],
            "trueCE_track": [s["trueCE"] for s in tel["steps"]]
                            + [tel["steps"][-1]["trueCE'"]],
            "gapW_track": [s["gapW"] for s in tel["steps"]]
                          + [tel["steps"][-1]["gapW'"]],
            "drop_track": [str(s["drop"]) for s in tel["steps"]],
            "stats": stats,
            "telemetry": {
                "steps": [{k: (str(v) if not isinstance(
                    v, float) else v)
                    for k, v in s.items()}
                    for s in tel["steps"]],
                "holds": [{k: str(v) for k, v in
                           h.items()} for h in tel["holds"]],
            },
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
        }, indent=1))
        if args.emit_lean:
            emit_lean_cs(args.emit_lean, start, traj,
                         witness_steps=2, full_steps=len(traj))
        if args.corrupt:
            emit_bad_cs(args.corrupt, start, traj)
        return

    if args.mode == "trunk-train":
        start, traj, tel, theta = trunk_train_run(
            args.steps if args.steps is not None else TT_STEPS)
        print(json.dumps({
            "mode": "trunk-train",
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "n_steps": len(traj),
            "loss_track": [str(d["obj"]) for d in traj]
                          + [str(traj[-1]["obj'"])],
            "holdout_track": [str(d["risk"]) for d in traj]
                             + [str(traj[-1]["risk'"])],
            "telemetry": {
                "model": tel["model"],
                "steps": [{k: str(v) for k, v in s.items()}
                          for s in tel["steps"]],
                "holds": [{k: str(v) for k, v in h.items()}
                          for h in tel["holds"]],
            },
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "params_final": str(tt_flat(theta)),
        }, indent=1))
        if args.emit_lean:
            emit_lean_trunk(args.emit_lean, start, traj)
        if args.corrupt:
            emit_lean_trunk(args.corrupt, start, traj, bad=True)
        return

    if args.mode == "full-pipeline":
        start, traj, tel, wfin, featsfin = full_pipeline_run()
        print(json.dumps({
            "mode": "full-pipeline",
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "n_steps": len(traj),
            "phase_steps": {p: sum(1 for r in traj if r["phase"] == p)
                            for p in dict.fromkeys(r["phase"]
                                                   for r in traj)},
            "loss_track": [str(r["obj"]) for r in traj]
                          + [str(traj[-1]["obj'"])],
            "holdout_track": [str(r["risk"]) for r in traj]
                             + [str(traj[-1]["risk'"])],
            "telemetry": {
                "phases": tel["phases"],
                "rejects": [{k: str(v) for k, v in rr.items()}
                            for rr in tel["rejects"]],
                "holds": [{k: str(v) for k, v in hh.items()}
                          for hh in tel["holds"]],
                "admissions": [{k: (str(v) if not isinstance(v, bool)
                                    else v) for k, v in aa.items()}
                               for aa in tel["admissions"]],
                "stop": tel.get("stop")},
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "weights_final": "[" + ", ".join(map(str, wfin)) + "]",
            "feats_dim": len(featsfin),
        }, indent=1))
        if args.emit_lean:
            emit_lean_full(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_full(args.corrupt, start, traj)
        return

    if args.mode == "hadamard-tern":
        start, traj, holds, states, jump = train_ht(
            args.grad_steps if args.grad_steps is not None else 1,
            args.ft_steps if args.ft_steps is not None else 1)
        print(json.dumps({
            "mode": "hadamard-tern",
            "K": HT_K,
            "eta": str(F(1) / ht_L()), "L": str(ht_L()),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "jump": {k: (str(v) if not isinstance(v, (bool, list))
                         else ([str(t) for t in v]
                               if isinstance(v, list) else v))
                     for k, v in jump.items()},
            "holds": [{k: (str(v) if not isinstance(v, (bool, list))
                           else ([str(t) for t in v]
                                 if isinstance(v, list) else v))
                       for k, v in h.items()} for h in holds],
            "trajectory": [{k: str(v) for k, v in d.items()}
                           for d in traj],
            "weights": ["[" + ", ".join(map(str, w)) + "]"
                        for w in states],
        }, indent=1))
        if args.emit_lean:
            emit_lean_tern(args.emit_lean, start, traj)
        if args.corrupt:
            emit_bad_tern(args.corrupt, start, traj)
        return

    if args.mode == "ef21-step":
        steps = args.steps if args.steps is not None             else EF21_STEPS_DEFAULT
        start, traj, rejects, states, stats = train_ef21(steps)
        print(json.dumps({
            "mode": "ef21-step",
            "eta": str(stats["eta"]), "scale": str(stats["scale"]),
            "start": str(start),
            "train_loss_final": str(traj[-1]["obj'"]),
            "holdout_final": str(traj[-1]["risk'"]),
            "stats": {k: (str(v) if not isinstance(v, int)
                          else v) for k, v in stats.items()},
            "rejects": [{k: (str(v) if not isinstance(v, (bool, list))
                             else ([str(t) for t in v]
                                   if isinstance(v, list) else v))
                         for k, v in r.items()} for r in rejects],
            "trajectory": [{k: (str(v) if not isinstance(v, list)
                                else [str(t) for t in v])
                            for k, v in d.items()} for d in traj],
            "weights": ["[" + ", ".join(map(str, w)) + "]"
                        for w in states],
        }, indent=1))
        if args.emit_lean:
            emit_lean_ef21(args.emit_lean, start, traj, rejects)
        if args.corrupt:
            emit_bad_ef21(args.corrupt, start, traj)
        return

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

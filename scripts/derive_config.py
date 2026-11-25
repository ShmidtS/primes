#!/usr/bin/env python3
"""derive_config (C683, C684): выводимая конфигурация обучения HAGI.

no reference: формулы — теоремы primes (FQN в таблице), числовые
входы — константы кода HAGI_v2 @ca52eb4 (файл:строка у каждого).
Stdlib only, детерминирован; печатает markdown-таблицу
«параметр | код | выведено | код/выведено | источник».
Запуск: python scripts/derive_config.py
"""
import math
import sys
from fractions import Fraction

SHA = "ca52eb4"


# ---- код @SHA: факты (файл:строка) ------------------------------------
CODE = {
    "k_ctx": 8, "dim": 64, "hidden": 128, "seed": 7,          # lm.py:272-274
    "init_scale": 0.08,                                        # lm.py:279-282
    "adam_lr_guarded": 3e-3, "epochs_guarded": 30, "hold_guarded": 0.1,  # lm.py:309-310
    "steps_mini": 3000, "batch": 512, "adam_lr_mini": 1e-3,    # lm.py:380-381
    "hold_mini": 0.02, "hold_mini_floor": 256,                 # lm.py:391
    "sched_min_frac": 0.0,                                     # lm.py:404 eta_min=0
    "lr0_hybrid": 0.04, "steps_hybrid": 280,                   # core.py:1739, :1718
    "muon_scale": 0.7, "ns_iters_w1": 3,                       # core.py:1755
    "muon_ema_old": 0.85, "muon_ema_new": 0.15,                # core.py:1754
    "wd": 2e-4,                                                # core.py:1747-1748
    "adam_b1": 0.9, "adam_b2": 0.999, "adam_eps": 1e-8,        # core.py:1756-1758
    "ns_iters_gpm": 4, "gpm_lr": 0.2, "gpm_steps": 35,         # core.py:1350, :1397-1398
    "commit_eps": 1e-12,                                       # core.py:1333
    "bt_probes_cert": 13, "bt_probes_self": 9, "bt_beta": 0.5,  # lm.py:827,862; selfmodel.py:78,134,174
    "z_lcb": 2.4, "adapter_min_gain": 0.005,                   # trunk_ops.py:203; unified.py:42
    "probe_grow": 128, "c_add_mult": 10.0, "max_blocks": 2,    # unified.py:391, :404, :381
    "w_choices": (1, 2, 4, 8, 16), "w_tol": 0.01,              # lm.py:159-160
    "ingest_epochs": 200, "ingest_repeat": 2,                  # unified.py:63
    "ternary_levels": 3,                                       # lm.py:262 (−1,0,+1)
}
# γ_auto = 1/(2·trace H̄), receipt C609 (docs/paper-draft.md, C609)
GAMMA_AUTO = [("ATA", Fraction(5000000, 10470759)),
              ("TGC", Fraction(13500000, 25944901)),
              ("TGC'", Fraction(156250, 234227))]
# receipt C597: auto-k* bench (docs/paper-draft.md:1332); C623/C626: w bench
BENCH = {"snap_k": (18, 19, 20), "snap_k_trunk": 11, "legacy_k": 40,
         "n_w": 100000, "w_bench": 256, "reads": (6250, 1563, 391)}

rows = []  # (param, code, derived, ratio, source, status)


def add(p, code, der, src, status, ratio=None):
    if ratio is None:
        try:
            ratio = f"{float(code) / float(der):.4g}"
        except (TypeError, ValueError, ZeroDivisionError):
            ratio = "—"
    rows.append((p, code, der, ratio, src, status))


def ceil(x):
    return -(-x // 1)


# ---- γ* = 1/L -----------------------------------------------------------
# C684: для relu-блока по W1 доказаны ДВЕ константы (FirstLayerLip.lean):
#   липшицевость ФУНКЦИИ  Lfun = 2·‖wo‖_F·‖x‖₂  (w1CE_lipschitz_param, глобально);
#   гладкость ГРАДИЕНТА    S    = ‖wo‖_F²·‖x‖₂²  (w1CE_descent_lemma, внутри
#   области активации) ⇒ γ* = 1/S, drop = ‖D‖²/(2S) (w1CE_optimal_step_drop).
# ‖wo‖_F и ‖x‖₂ код не логирует ⇒ число только на WITNESS-входах (не код):
# .tmp/C684/traj.lean — x=(1,2), wo=[[1,0],[0,2],[1,1]]: Σwo²=7, Σx²=5.
WIT_WO2, WIT_X2 = 7, 5
add("γ (guarded Adam lr)", CODE["adam_lr_guarded"],
    "γ* = 1/S_batch (mean: B/S_batch), S_batch = ‖wo‖_F²·Σ_t‖x t‖₂² — FirstLayerLipBatch; DERIVED-формула; число — HONEST-GAP до телеметрии PROPOSAL #11",
    "w1BatchCE_optimal_step_drop FirstLayerLipBatch.lean:218; nl_drop_optimal NegativeTransfer.lean:481",
    "HONEST-GAP", "—")
add("S (W1 smoothness) witness", "—", f"{WIT_WO2}·{WIT_X2} = {WIT_WO2 * WIT_X2}",
    "w1CE_descent_lemma FirstLayerLip.lean:258 (witness, не код)", "BOUNDED", "—")
add("γ* = 1/S witness (W1, plain GD)", "—", f"1/{WIT_WO2 * WIT_X2} = {1 / (WIT_WO2 * WIT_X2):.4f}",
    "w1CE_optimal_step_drop :392 (witness, не код)", "BOUNDED", "—")
# C685: батч-версия (FirstLayerLipBatch.lean): S_batch = ‖wo‖_F²·Σ_t‖x t‖₂²,
#   γ*_batch = 1/S_batch; mean (lm.py:299): S_mean = S_batch/B, γ*_mean = B/S_batch.
#   Число — HONEST-GAP до телеметрии PROPOSAL #11; входы ниже — witness (.tmp/C685/traj.lean).
def gamma_star_batch(wo_frob_sq, x_l2_sq_max, B):
    """γ* = 1/S_batch, γ*_mean = B/S_batch (witness defaults, not code values)."""
    x_l2_sq_sum = sum(x_l2_sq_max)
    S = wo_frob_sq * x_l2_sq_sum
    return S, wo_frob_sq * B * max(x_l2_sq_max), 1 / S, B / S


S_B, S_MAX, GS, GSM = gamma_star_batch(wo_frob_sq=WIT_WO2, x_l2_sq_max=[5, 2], B=2)
add("γ (guarded Adam lr), batch form", CODE["adam_lr_guarded"],
    f"γ* = 1/S_batch (mean: B/S_batch) = {GS:.4f} (mean {GSM:.4f}); witness, не код",
    "w1MeanCE_optimal_step_drop FirstLayerLipBatch.lean:247; PROPOSAL-smoothness-logging (#11)",
    "HONEST-GAP", "—")
add("S_batch (W1 smoothness, batch) witness", "—", f"{WIT_WO2}·(5+2) = {S_B:g} ≤ B·7·max = {S_MAX:g}",
    "w1BatchCE_descent_lemma FirstLayerLipBatch.lean:113; S_batch_le_max :86 (witness)", "BOUNDED", "—")
add("γ*_batch / γ*_mean witness", "—", f"1/{S_B:g} = {GS:.4f}; B/S_batch = {GSM:.4f}",
    "w1BatchCE_optimal_step_drop :218; w1MeanCE_optimal_step_drop :247 (witness)", "BOUNDED", "—")
add("Lfun (W1 Lipschitz) witness", "—",
    f"2·√{WIT_WO2}·√{WIT_X2} = {2 * math.sqrt(WIT_WO2 * WIT_X2):.4f}",
    "w1CE_lipschitz_param :182 (функция, не градиент; witness)", "BOUNDED", "—")
add("L_dir certified step (denom)", "Q' + 4·curv_reg",
    "R² = denom: код ИЗМЕРЯЕТ (core.py:1314-1319)",
    "ce_range_code_drop AdaptiveMajorizer.lean:1497; useful_first_step :584", "DERIVED", "—")
for nm, g in GAMMA_AUTO:
    add(f"γ_auto {nm} (ATA/TGC)", f"{float(g):.4f}", f"1/(2·trH̄)={g.numerator}/{g.denominator}",
        "auto-LR 1/(2·trace H̄), receipt C609", "DERIVED")
add("L implied by γ_auto", "—",
    "/".join(f"{2 / float(g):.3f}" for _, g in GAMMA_AUTO),
    "L = 2·trH̄ = 1/γ_auto", "DERIVED", "—")

# ---- η* = 4|a|/R², drop = 2a²/R² ---------------------------------------
# код: eta = 4A/denom, A=‖ḡ‖², denom = Q' (+4·curv) (core.py:1320-1321; lm.py:861)
# d = −ḡ ⇒ a = ⟨ḡ,d⟩ = −A < 0; linDrop = −(ηa + η²R²/8), R² = denom.
add("η certified step", "4A/denom", "−4a/R² = 4A/denom",
    "useful_first_step FunctionPreservingGrowth.lean:584", "DERIVED", "1")
add("drop certified step", "2A²/denom", "2a²/R²",
    "useful_first_step :584 (R² = denom)", "DERIVED", "1")
add("witness R=2, a=−1/2: η*", "—", "1.0", "useful_first_step (R=2)", "DERIVED", "—")

# ---- COMMIT threshold ---------------------------------------------------
add("COMMIT threshold", CODE["commit_eps"], ">0 (строго)",
    "warmup_h1_of_certified_steps FunctionPreservingGrowth.lean:410", "BOUNDED")
add("backtrack β / probes", f"{CODE['bt_beta']} / {CODE['bt_probes_cert']}",
    "β, probes: не формализованы", "—", "HONEST-GAP", "—")

# ---- snap k* ------------------------------------------------------------
add("snap k*", "нет snap-грида",
    "⌈log₂(L·d/ε)⌉−1", "snap_k_eq_ceil GrowSnap.lean:342", "DERIVED", "—")
add("snap k* bench (C597): код legacy / auto", f"{BENCH['legacy_k']}",
    "/".join(map(str, BENCH["snap_k"])), "receipt C597 (paper-draft.md:1332)", "DERIVED")
for m in (4, 8, 16, 20):
    x = 2.0 ** (m + 1)
    add(f"  k* при L·d/ε = 2^{m+1}", "—", str(ceil(math.log2(x)) - 1),
        "snap_k_eq_ceil", "DERIVED", "—")
add("bits saved vs legacy (33 snaps)", "—", "2788",
    "receipt C597", "DERIVED", "—")

# ---- w* = √(a/c) --------------------------------------------------------
add("coverage w", f"max {max(CODE['w_choices'])} (tol {CODE['w_tol']})",
    "√(a/c); a, c в коде не измеряются",
    "mixedCost_relax_min_eq CoverageReading.lean:648", "HONEST-GAP", "—")
add("w bench (n=100000, fixed cost)", "16", f"{BENCH['w_bench']} → {BENCH['reads'][2]} reads",
    "windowCost_fixed_mono CoverageReading.lean:575; receipt C623", "BOUNDED",
    f"{16 / BENCH['w_bench']:.4g}")
add("  reads(16)/reads(256)", f"{BENCH['reads'][0]}", f"{BENCH['reads'][2]}",
    "receipt C623", "DERIVED")

# ---- growth gate --------------------------------------------------------
p_all = 256 * CODE["dim"] + CODE["k_ctx"] * CODE["dim"] * CODE["hidden"] + CODE["hidden"] \
    + CODE["hidden"] * 256 + 256
c_add = (CODE["dim"] * CODE["hidden"] + CODE["hidden"] ** 2) / p_all * CODE["c_add_mult"]
add("growth c_add", "10·(d·h+h²)/N", f"{c_add:.4f} (N={p_all}, no blocks)",
    "growth_gate_stay_char NegativeTransfer.lean:576", "DERIVED")
add("growth probe n", CODE["probe_grow"], "n·G²/(2L): n не формализовано",
    "growth_gate_stay_char :576", "HONEST-GAP", "—")
add("growth L", "CE loss (unified.py:400)", "Lipschitz-константа majorizer",
    "nl_drop_optimal :481", "HONEST-GAP", "—")

# ---- holdout k ≥ ln(2N/δ)/(2(ε/B)²) --------------------------------------
def hold_k(N, delta, eps):
    return int(ceil(math.log(2 * N / delta) / (2 * eps ** 2)))
for N in (2, 10):
    k = hold_k(N, 0.05, 0.05)
    add(f"holdout k (N={N}, δ=0.05, ε=0.05B)", f"max(256, 2%·n)", f"{k}",
        "holdout_gate_two_way_delta HoldoutGateTwoWay.lean:109; таблица не доказана (PROPOSAL 8)", "BOUNDED")
add("  n windows needed for k≥1199 @2%", "—", str(int(ceil(1199 / CODE["hold_mini"]))),
    "1199/0.02", "DERIVED", "—")

# ---- LCB ---------------------------------------------------------------
for z in (1.5, CODE["z_lcb"]):
    bound = 2 * math.exp(-2 * z * z / 16)
    add(f"P[false GROW] bound, z={z}, σ̂=B/2, n=256", "n=256",
        f"≤{bound:.4f} (vacuous: >1)", "paired_lcb_false_grow_bound NadyaOptimal.lean:270", "BOUNDED")
s = 0.05
b = 2 * math.exp(-256 * 2.4 ** 2 * s * s / 2)
add("P[false GROW] bound, z=2.4, σ̂=0.05B, n=256", "n=256", f"≤{b:.4f}",
    "paired_lcb_false_grow_bound NadyaOptimal.lean:270", "BOUNDED")
kn = int(ceil(2 * math.log(2 / 0.05) / (2.4 ** 2 * 0.05 ** 2)))
add("LCB n for P≤0.05 (z=2.4, σ̂=0.05B)", "256", f"{kn}", "paired_lcb_false_grow_bound :270", "DERIVED",
    f"{256 / kn:.4g}")

# ---- Muon ---------------------------------------------------------------
def ns(sigma, k):
    for _ in range(k):
        sigma = sigma * (3 - sigma * sigma) / 2
    return sigma
tbl = ", ".join(f"{s}:{ns(s, 3):.4f}" for s in (0.1, 0.3, 0.5, 0.7, 0.9, 1.0))
add("σ₃(σ₀) table", "iters=3", tbl, "ns_sigma_min_three NewtonSchulzSigma.lean:126 (σ₀≥½ ⇒ ≥39/40)", "DERIVED", "—")
add("σ₃(1) bound", "—", f"{float(Fraction(39, 40)):.4f} ≤ {ns(1.0, 3):.4f}", "ns_sigma_min_three :126", "DERIVED")
add("Muon effective step (t=1)", f"{CODE['lr0_hybrid']}·sched·{CODE['muon_scale']}",
    f"{CODE['lr0_hybrid'] * 0.5 * (1 + math.cos(math.pi / CODE['steps_hybrid'])) * CODE['muon_scale']:.5f}",
    "step = cos_lr·0.7·X₃ (core.py:1755)", "DERIVED")
# C686: m1 = 0.85*m1 + 0.15*gW1 (core.py:1754), NS применяется к m1 (core.py:1755).
# Доказано (MomentumAlign.lean): выравнивание и граница drop; значение 0.85 не выводится.
add("Muon momentum alignment", f"m1 = {CODE['muon_ema_old']}·m1 + {CODE['muon_ema_new']}·gW1",
    "⟨G,m1⟩ = 0.15·‖G‖² + 0.85·⟨G,m1_prev⟩ ≥ 0.15·‖G‖² (если ⟨G,m1_prev⟩ ≥ 0)",
    "momentum_align, momentum_align_ge MomentumAlign.lean:140/:169", "BOUNDED", "—")
add("Muon momentum half-residual", "‖G−m1‖_F·‖X₃‖_F",
    "≤ ‖m1‖_F/2 ⇒ ⟨G,X₃⟩ ≥ ‖G‖_F/3 (X₃ = ns₃(m1/‖m1‖_F))",
    "muon_momentum_bound :419; muon_momentum_third :442", "BOUNDED", "—")
add("Muon momentum", f"{CODE['muon_ema_old']}/{CODE['muon_ema_new']}", "значение 0.85 не выводится",
    "momentum_align_cs MomentumAlign.lean:149 (⟨G,m⟩ ≥ (1−μ)‖G‖² − μ‖G‖‖m_prev‖)", "HONEST-GAP", "—")

# ---- cosine -------------------------------------------------------------
for T, name in ((CODE["steps_hybrid"], "hybrid"), (CODE["steps_mini"], "minibatch")):
    f1 = 0.5 * (1 + math.cos(math.pi / T))
    add(f"sched(T) {name}", f"{CODE['sched_min_frac']:.1f} (eta_min=0)", "3/20 = 0.15",
        "cosine_sched_bounds NadyaOptimal.lean:143", "BOUNDED")
    add(f"sched(1)/sched(0) {name}", f"{f1:.6f}", "≤1", "cosine_sched_bounds :143", "BOUNDED")

# ---- honest -------------------------------------------------------------
add("Adam β₁/β₂/eps", f"{CODE['adam_b1']}/{CODE['adam_b2']}/{CODE['adam_eps']}", "—", "теоремы нет", "HONEST-GAP", "—")
add("weight decay λ", CODE["wd"], "B²=Bn·t0/c → значение λ не выводится", "WeightDecayLeak.lean:126 (механизм, не значение)", "HONEST-GAP", "—")
add("batch B", CODE["batch"], "B*=√(Bn·t0/c); Bn,t0,c не измерены",
    "amgm_equality Audit.lean:651", "HONEST-GAP", "—")
add("steps / epochs", f"{CODE['steps_mini']}/{CODE['epochs_guarded']}", "—", "теоремы нет", "HONEST-GAP", "—")
add("k_ctx, dim, hidden, seed", f"{CODE['k_ctx']}/{CODE['dim']}/{CODE['hidden']}/{CODE['seed']}", "—", "теоремы нет", "HONEST-GAP", "—")
add("init scale", CODE["init_scale"], "—", "теоремы нет", "HONEST-GAP", "—")
add("LCB z", CODE["z_lcb"], "—", "z не выводится (r свободный параметр)", "HONEST-GAP", "—")
add("adapter min gain", CODE["adapter_min_gain"], "—", "теоремы нет", "HONEST-GAP", "—")
add("ternary grid", "3 levels, row scale mean|W|", "—", "теоремы оптимальности нет", "HONEST-GAP", "—")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    print(f"# derive_config — HAGI_v2 @{SHA}\n")
    print("| параметр | код | выведено | код/выведено | статус | источник |")
    print("|---|---|---|---|---|---|")
    cnt = {}
    for p, c, d, r, src, st in rows:
        cnt[st] = cnt.get(st, 0) + 1
        print(f"| {p} | {c} | {d} | {r} | {st} | {src} |")
    print("\nSTATUS COUNTS:", " ".join(f"{k}={v}" for k, v in sorted(cnt.items())))


if __name__ == "__main__":
    main()

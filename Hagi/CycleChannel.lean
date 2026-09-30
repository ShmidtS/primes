/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.RootContrast

set_option linter.style.header false

/-!
# CycleChannel: CycleDecay + ChannelBudget — the generation-decay law
and the movement/rank channel switching

The measured dbridge movement channel (siblings → merge → joint):
gen-0→1 Δ_joint = 0.3504 (blind prediction 0.10 — exceeded),
gen-1→2 Δ_joint = 0.1874 (factor ~0.53 — NOT geometric); the LoRA
rank channel: −0.024 (on the swiglu-joint base), −0.043 (on the
clamp-8 base) — the rank gain GROWS with the base's residual gap.
Two anomalies need theory.

**T1 — `cycle_decay_mono` + `cycle_decay_ratio`**: the
saturating-decay model: a generation's free-energy gap F_g shrinks
by Δ_g = k·F_g/(F_g + s) (k = μ·M: the learning rate × fresh
tokens; s: the landscape constant). Theorems (conditional form —
the model is phenomenological, calibrated on TWO points with the
third as blind verification):
- monotonicity: F_{g+1} = F_g·(1 − k/(F_g+s)) < F_g and stays
  nonneg whenever 0 < k < F_g + s;
- the exact step-ratio identity: Δ_{g+1}/Δ_g =
  F_{g+1}(F_g+s)/(F_g(F_{g+1}+s)) — the measurable relation
  (NOTE: the plan's stated ratio (F_g+s)/(F_{g−1}+s) omitted the
  prefactor F_{g+1}/F_g — the correct identity includes it);
- calibration: two points (0.35, 0.19) fix (k, s); the blind
  prediction Δ_3 = Δ_2·F_2(F_1+s)/(F_1(F_2+s)); if the measured
  Δ_3 deviates > 30% the saturation form is WRONG — audit
  (candidate replacement: exponential in generations with a
  noise floor).

**T2 — `channel_switch`**: two channels at costs C_move (full
sibling cycle, ~2.5 GPU-h) and C_rank (LoRA, ~0.7 h): the
movement gain saturates (k·F/(F+s)); the rank gain grows as
b·√F (b = ν·r_eff — bigger on an under-trained base: explains
−0.024 vs −0.043). THEOREM: for F < F_switch (explicitly
F_switch = (b·C_move·s/(k·C_rank))² in √F-form: √F·k·C_rank <
b·C_move·s), the RANK index strictly dominates the movement
index: k·F/(F+s)/C_move < b·√F/C_rank — the movement channel
NEVER wins below the threshold: the automatic stop rule for
sibling generations (replacing the manual ledger decision).
This is the Gittins rule (argmax Δ_i/C_i) instantiated on the
two channels with the crossing computed.

**C — the certificate (no GPU)**: from saved telemetry,
F_2 := CE(clamp-8) − CE(LoRA-over-clamp8) is the measurable
proxy of the residual gap; rank the three candidates (gen-3
siblings / LoRA r=32,64 / F3-highway) by the measured indices.

**Blind predictions (ledger, BEFORE the run)**: Δ_3 from T1's
calibrated form (expected order 0.10–0.14 nat); if gen-3 gives
< ½ of it, T1 goes to audit.

**Honesty boundaries**: T1 is a phenomenological law (2-point
calibration + 1 blind verification, NOT a convergence theorem —
the Lean form is conditional); T2 assumes channel independence
(the measured LoRA-over-clamp8 super-additivity is a recorded
deviation, an interaction constant in the refinement, not
hidden).
-/

open Finset Real

namespace Hagi

section CycleDecay

/-- **T1a — the generation-decay monotonicity**: under the
saturating model F' = F·(1 − k/(F+s)) with 0 < k < F+s and
s ≥ 0, F' < F strictly and F' ≥ 0: each generation's
free-energy gap strictly decreases and stays nonnegative. -/
theorem cycle_decay_mono (F k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hk : 0 < k) (hklt : k < F + s) :
    F * (1 - k/(F + s)) < F ∧ 0 ≤ F * (1 - k/(F + s)) := by
  constructor
  · have heq : F * (1 - k/(F + s)) = F - F * k/(F + s) := by ring
    rw [heq]
    have hpos2 : 0 < F * k/(F + s) := by positivity
    linarith
  · have hfrac2 : 0 ≤ 1 - k/(F + s) := by
      have : k ≤ F + s := by linarith
      rw [sub_nonneg, div_le_one (by linarith : (0:ℝ) < F + s)]
      linarith
    positivity

/-- **T1b — the exact step-ratio identity**: for the saturating
model Δ_g = k·F/(F+s), the ratio of consecutive gains is
exactly Δ'/Δ = F'·(F+s)/(F·(F'+s)) — the measurable relation
for calibration (the plan's (F_g+s)/(F_{g−1}+s) form omitted
the F_{g+1}/F_g prefactor; the full identity is this one). -/
theorem cycle_decay_ratio (F F' k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hF' : 0 < F') (hk : 0 < k) :
    (k * F' / (F' + s)) / (k * F / (F + s))
      = F' * (F + s) / (F * (F' + s)) := by
  field_simp

end CycleDecay

section ChannelBudget

/-- **T2 — the channel-switch threshold theorem**: with the
movement gain k·F/(F+s) at cost C_move and the rank gain b·√F
at cost C_rank (all constants positive), whenever
√F·k·C_rank < b·C_move·s — i.e. F < F_switch where
F_switch = (b·C_move·s/(k·C_rank))² — the RANK channel's index
strictly dominates the movement channel's:
k·F/(F+s)/C_move < b·√F/C_rank.
The movement channel NEVER wins below the threshold: the
automatic stop for sibling generations (the Gittins argmax
Δ_i/C_i instantiated; the threshold is explicit and computable
from the calibrated constants and the measured residual gap F). -/
theorem channel_switch (F k s b Cm Cr : ℝ)
    (hs : 0 < s) (hk : 0 < k) (hb : 0 < b) (hCm : 0 < Cm)
    (hCr : 0 < Cr) (hF : 0 < F)
    (hswitch : √F * (k * Cr) < b * Cm * s) :
    k * F / (F + s) / Cm < b * √F / Cr := by
  set t := √F with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hF
  have hF2 : t * t = F := Real.mul_self_sqrt (le_of_lt hF)
  have hFs : (0:ℝ) < F + s := by nlinarith
  have h1 : k * F / (F + s) ≤ k * F / s := by
    rw [div_le_div_iff₀ hFs hs]
    nlinarith [mul_nonneg (le_of_lt hk) (le_of_lt hF),
      mul_nonneg (le_of_lt hk) (le_of_lt hF), mul_nonneg hs.le hs.le,
      mul_nonneg hFs.le hFs.le]
  have h2 : k * F / s * Cr < b * t * Cm := by
    have hstep : (t * (k * Cr)) * (t / s) < b * Cm * t := by
      have h1' : (t * (k * Cr)) * (t / s) < (b * Cm * s) * (t / s) :=
        mul_lt_mul_of_pos_right hswitch (by positivity : (0:ℝ) < t / s)
      rw [show (b * Cm * s) * (t / s) = b * Cm * t by field_simp] at h1'
      exact h1'
    calc k * F / s * Cr = (t * (k * Cr)) * (t / s) := by
          conv_lhs => rw [← hF2]
          field_simp
      _ < b * Cm * t := hstep
      _ = b * t * Cm := by ring
  have hA : k * F / (F + s) / Cm ≤ k * F / s / Cm :=
    div_le_div_of_nonneg_right h1 (le_of_lt hCm)
  have hB : k * F / s / Cm < b * t / Cr := by
    rw [div_lt_div_iff₀ hCm hCr]
    exact h2
  linarith

end ChannelBudget

end Hagi

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Depth.RootContrast

set_option linter.style.header false

/-!
# CycleChannel — generation-decay law and channel switching

Under a saturating-decay model, a generation's free-energy gap `F`
shrinks by `k·F/(F+s)`. Two conditional results (the model is
phenomenological, calibrated on data, and assumed as hypotheses;
nothing here is a convergence theorem):

* `cycle_decay_mono`: if `0 < k < F + s` and `s ≥ 0`, then
  `F·(1 − k/(F+s)) < F` and is nonnegative;
* `cycle_decay_ratio`: the exact step-ratio identity
  `Δ'/Δ = F'·(F+s)/(F·(F'+s))` for the model gains
  `Δ = k·F/(F+s)`;
* `channel_switch`: with movement gain `k·F/(F+s)` at cost `Cm`
and rank gain `b·√F` at cost `Cr` (all constants positive), if
`√F·k·Cr < b·Cm·s` then the rank index strictly dominates:
`k·F/(F+s)/Cm < b·√F/Cr`.

T2 additionally assumes channel independence; the measured
LoRA-over-clamp8 super-additivity is a recorded deviation outside
this model.
-/

open Finset Real

namespace Hagi.Growth

section CycleDecay

/-- If `0 ≤ s`, `0 < F`, `0 < k`, and `k < F + s`, then
`F * (1 - k/(F + s)) < F` and `0 ≤ F * (1 - k/(F + s))`. -/
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

/-- Exact step-ratio identity for the saturating model gains
`Δ = k·F/(F+s)`: if `0 ≤ s`, `0 < F`, `0 < F'`, `0 < k`, then
`(k·F'/(F'+s)) / (k·F/(F+s)) = F'·(F+s)/(F·(F'+s))`. -/
theorem cycle_decay_ratio (F F' k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hF' : 0 < F') (hk : 0 < k) :
    (k * F' / (F' + s)) / (k * F / (F + s))
      = F' * (F + s) / (F * (F' + s)) := by
  field_simp

end CycleDecay

section ChannelBudget

/-- If all constants are positive (`0 < s`, `0 < k`, `0 < b`,
`0 < Cm`, `0 < Cr`, `0 < F`) and `√F·k·Cr < b·Cm·s`, then the
rank index dominates the movement index:
`k·F/(F+s)/Cm < b·√F/Cr`. -/
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

end Hagi.Growth

namespace Hagi
export Hagi.Growth (cycle_decay_mono cycle_decay_ratio channel_switch)
end Hagi

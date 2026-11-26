/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# AdamRel — локальный timestep после смены масштаба градиента

Adam-Rel (Ellis et al., NeurIPS 2024): рост нормы градиента (смена цели,
новый домен) при глобальном timestep даёт завышенные обновления; сброс
timestep к 0 после смены возвращает корректную bias-correction. Для HAGI
(continual, смена доменов) — альтернатива g-SNR-скейлингу (proposal 15),
не требующая warmup и сохраняющая второй момент.

* `vEMA` — второй момент EMA после `t` шагов на градиентах масштаба `s²`;
* `rel_reset_exact` — после сброса `v̂ = s²` точно на первом шаге;
* `rel_vhat_ge_global` — при росте масштаба (`v₀ ≤ s²`) Adam-Rel момент
  ≥ глобального (старого `v₀`): глобальный шаг завышен в `s/√v₀` раз.
-/

namespace Hagi.Step.AdamRel

/-- Второй момент после `t` шагов EMA (β₂) на градиентах масштаба `s²`:
`v_t = β₂^t·v₀ + (1 − β₂^t)·s²`. -/
noncomputable def vEMA (b2 v0 s : ℝ) (t : ℕ) : ℝ := b2 ^ t * v0 + (1 - b2 ^ t) * s ^ 2
theorem vEMA_zero (b2 v0 s : ℝ) : vEMA b2 v0 s 0 = v0 := by simp [vEMA]
theorem vEMA_succ (b2 v0 s : ℝ) (t : ℕ) : vEMA b2 v0 s (t+1) = b2 * vEMA b2 v0 s t + (1 - b2) * s ^ 2 := by
  rw [vEMA, vEMA, pow_succ]
  ring
/-- Adam-Rel: сброс timestep даёт bias-corrected `v̂` точным на первом шаге
нового масштаба (`s²`); глобальный timestep (bias ≈ 1) оставляет старый `v₀`. -/
theorem rel_reset_exact (b2 s : ℝ) (hb1 : b2 ≠ 1) : vEMA b2 0 s 1 / (1 - b2 ^ (1:ℕ)) = s ^ 2 := by
  rw [vEMA_succ, vEMA_zero]
  have hb : 1 - b2 ^ (1:ℕ) = 1 - b2 := by norm_num
  rw [hb]
  field_simp [sub_ne_zero.2 hb1]
  ring
/-- With a gradient-scale increase (`v0 <= s^2`) the Adam-Rel bias-corrected
second moment of the first step is at least the stale global one: the global
step is oversized by the ratio. -/
theorem rel_vhat_ge_global (b2 v0 s : ℝ) (hb1 : b2 < 1) (h : v0 ≤ s ^ 2) :
    v0 ≤ vEMA b2 0 s 1 / (1 - b2 ^ (1:ℕ)) := by
  rw [rel_reset_exact b2 s hb1.ne]
  exact h

end Hagi.Step.AdamRel

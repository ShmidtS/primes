/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# EpochTradeoff — почему больше эпох на приём уменьшает забывание

`neuro_symbolic_cycle.py` (ec80163): `CYCLE_EPOCHS = 4` вместо 2 — замер на
трёх одинаковых новых доменах: выигрыш на новых одинаков (4.53 → 4.50 нат),
потеря старых вдвое меньше (0.183 → 0.097), цена +68% времени.

Модель: new-loss насыщается по эпохам (`L(E) = L∞ + (L₀ − L∞)(1 − η)^E`),
забывание старых затухает (`R(E) = R₀(1 − ρ)^E`) — на каждом шаге приёма
доля старых байтов ревизуется. После насыщения дополнительные эпохи не меняют
выученность, но делят забывание на `(1 − ρ)^{ΔE}`.

* `newLoss`, `oldReg` — модели;
* `newLoss_anti`, `oldReg_anti` — монотонность по эпохам;
* `saturation_tradeoff` — `L(E₁) ≤ L∞ + ε ⇒ L(E₂) ≤ L∞ + ε` и `R(E₂) ≤ R(E₁)`;
* `oldReg_ratio` — `R(E₂) = R(E₁)·(1 − ρ)^{E₂ − E₁}`.
-/

namespace Hagi.Learning.EpochTradeoff

/-- Модель приёма: new-loss насыщается (`L(E) = Linf + (L0 − Linf)(1 − η)^E`),
забывание старых затухает по эпохам (`R(E) = R0·(1 − ρ)^E`) — ревизия старых
байтов в каждом шаге приёма уменьшает регрессию. -/
noncomputable def newLoss (L0 Linf η : ℝ) (E : ℕ) : ℝ := Linf + (L0 - Linf) * (1 - η) ^ E
noncomputable def oldReg (R0 ρ : ℝ) (E : ℕ) : ℝ := R0 * (1 - ρ) ^ E
/-- New-loss монотонно падает по эпохам (при `L0 ≥ Linf`, `0 ≤ η ≤ 1`). -/
theorem newLoss_anti (L0 Linf η : ℝ) (h0 : Linf ≤ L0) (hη : 0 ≤ η) (hη2 : η ≤ 1)
    (E₁ E₂ : ℕ) (h : E₁ ≤ E₂) : newLoss L0 Linf η E₂ ≤ newLoss L0 Linf η E₁ := by
  unfold newLoss
  apply add_le_add (le_rfl : Linf ≤ Linf)
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.2 h0)
  exact pow_le_pow_of_le_one (by linarith) (by linarith) h
/-- Забывание старых монотонно падает по эпохам. -/
theorem oldReg_anti (R0 ρ : ℝ) (hR : 0 ≤ R0) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1)
    (E₁ E₂ : ℕ) (h : E₁ ≤ E₂) : oldReg R0 ρ E₂ ≤ oldReg R0 ρ E₁ := by
  unfold oldReg
  apply mul_le_mul_of_nonneg_left _ hR
  exact pow_le_pow_of_le_one (by linarith) (by linarith) h
/-- После насыщения (new-loss в `ε` от `Linf`) дополнительные эпохи не меняют
выученность, но уменьшают забывание в `(1 − ρ)^{ΔE}` раз. -/
theorem saturation_tradeoff (L0 Linf η R0 ρ ε : ℝ) (h0 : Linf ≤ L0) (hη : 0 ≤ η)
    (hη2 : η ≤ 1) (hR : 0 ≤ R0) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1) (E₁ E₂ : ℕ) (h : E₁ ≤ E₂)
    (hsat : newLoss L0 Linf η E₁ ≤ Linf + ε) :
    newLoss L0 Linf η E₂ ≤ Linf + ε ∧ oldReg R0 ρ E₂ ≤ oldReg R0 ρ E₁ := by
  exact ⟨le_trans (newLoss_anti L0 Linf η h0 hη hη2 E₁ E₂ h) hsat,
    oldReg_anti R0 ρ hR hρ hρ2 E₁ E₂ h⟩
/-- Количественно: `R(E₂) = R(E₁)·(1 − ρ)^{E₂ − E₁}`. -/
theorem oldReg_ratio (R0 ρ : ℝ) (E₁ E₂ : ℕ) (h : E₁ ≤ E₂) :
    oldReg R0 ρ E₂ = oldReg R0 ρ E₁ * (1 - ρ) ^ (E₂ - E₁) := by
  unfold oldReg
  rw [mul_assoc R0, ← pow_add, Nat.add_sub_cancel' h]

end Hagi.Learning.EpochTradeoff

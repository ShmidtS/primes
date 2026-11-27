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
* `oldReg_ratio` — `R(E₂) = R(E₁)·(1 − ρ)^{E₂ − E₁}`;
* `cost c₀ c₁ E = c₀ + E·c₁` — фиксированные расходы плюс шаги;
* `cost_ratio_le` — стоимость сублинейна: `cost(E₂)/cost(E₁) ≤ E₂/E₁`;
* `overhead_from_measurement` — 403 с / 677 с ⇒ `c₁ = 137`, `c₀ = 129`:
  накладные расходы приёма ≈ 0.94 эпохи (поэтому ×2 эпох даёт +68%, не +100%);
* `objective c₀ c₁ lam R₀ ρ E = cost E + lam·oldReg E` — стоимость плюс штраф;
* `objective_delta` — приращение за эпоху `= c₁ − lam·R₀·ρ·(1−ρ)^E`;
* `objective_delta_mono` — приращение не убывает (цель выпукла по эпохам);
* `stop_condition` — первое `E` с `lam·R₀·ρ·(1−ρ)^E ≤ c₁` оптимально:
  все дальнейшие эпохи не уменьшают цель.
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

/-- Стоимость приёма `E` эпох: фиксированные расходы `c₀` (валидация, откат,
рост) плюс `E·c₁` (шаги обучения). -/
noncomputable def cost (c₀ c₁ : ℝ) (E : ℕ) : ℝ := c₀ + E * c₁
/-- Стоимость сублинейна по эпохам: `cost(E₂)/cost(E₁) ≤ E₂/E₁` при `c₀ ≥ 0`. -/
theorem cost_ratio_le (c₀ c₁ : ℝ) (h0 : 0 ≤ c₀) (h1 : 0 < c₁) (E₁ E₂ : ℕ) (hE₁ : 0 < E₁)
    (h : E₁ ≤ E₂) : cost c₀ c₁ E₂ / cost c₀ c₁ E₁ ≤ (E₂ : ℝ) / E₁ := by
  unfold cost
  have hE2 : (0 : ℝ) < E₂ := by exact_mod_cast lt_of_lt_of_le hE₁ h
  have hE1' : (0 : ℝ) < E₁ := by exact_mod_cast hE₁
  have hpos : 0 < c₀ + E₁ * c₁ := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  · have : ((E₁ : ℝ)) * c₀ ≤ (E₂ : ℝ) * c₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast h) h0
    nlinarith
/-- Замер ec80163 (403 с при 2 эпохах, 677 с при 4): `c₁ = 137`, `c₀ = 129` —
накладные расходы ≈ 0.94 эпохи. -/
theorem overhead_from_measurement (c₀ c₁ : ℝ) (h2 : c₀ + 2 * c₁ = 403)
    (h4 : c₀ + 4 * c₁ = 677) : c₁ = 137 ∧ c₀ = 129 := by
  constructor <;> linarith

/-- Целевая: стоимость приёма плюс штраф за забывание. -/
noncomputable def objective (c₀ c₁ lam R₀ ρ : ℝ) (E : ℕ) : ℝ :=
  cost c₀ c₁ E + lam * oldReg R₀ ρ E
/-- Приращение цели от одной эпохи: `c₁ − lamR₀ρ(1−ρ)^E`. -/
theorem objective_delta (c₀ c₁ lam R₀ ρ : ℝ) (E : ℕ) :
    objective c₀ c₁ lam R₀ ρ (E + 1) - objective c₀ c₁ lam R₀ ρ E
      = c₁ - lam * R₀ * ρ * (1 - ρ) ^ E := by
  unfold objective cost oldReg
  rw [pow_add, pow_one]
  push_cast
  ring
/-- Приращение не убывает по `E` (цель выпукла) при `lam R₀ ρ ≥ 0`, `0 ≤ ρ ≤ 1`. -/
theorem objective_delta_mono (c₀ c₁ lam R₀ ρ : ℝ) (hlam : 0 ≤ lam) (hR : 0 ≤ R₀)
    (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1) (E₁ E₂ : ℕ) (h : E₁ ≤ E₂) :
    objective c₀ c₁ lam R₀ ρ (E₁ + 1) - objective c₀ c₁ lam R₀ ρ E₁
      ≤ objective c₀ c₁ lam R₀ ρ (E₂ + 1) - objective c₀ c₁ lam R₀ ρ E₂ := by
  simp only [objective_delta]
  have hp : (1 - ρ) ^ E₂ ≤ (1 - ρ) ^ E₁ := pow_le_pow_of_le_one (by linarith) (by linarith) h
  have hn : 0 ≤ lam * R₀ * ρ := by positivity
  have hm := mul_le_mul_of_nonneg_left hp hn
  linarith
/-- Условие остановки: эпоха `E + 1` не окупается, если `lam R₀ ρ (1−ρ)^E ≤ c₁`;
после этого цель не убывает. -/
theorem stop_condition (c₀ c₁ lam R₀ ρ : ℝ) (hlam : 0 ≤ lam) (hR : 0 ≤ R₀)
    (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1) (E : ℕ)
    (h : lam * R₀ * ρ * (1 - ρ) ^ E ≤ c₁) :
    ∀ E', E ≤ E' → objective c₀ c₁ lam R₀ ρ E ≤ objective c₀ c₁ lam R₀ ρ E' := by
  intro E' hE'
  induction E' with
  | zero =>
    have : E = 0 := Nat.eq_zero_of_le_zero hE'
    subst this; exact le_rfl
  | succ E' ih =>
    rcases Nat.eq_or_lt_of_le hE' with heq | hlt
    · rw [heq]
    · have hle : E ≤ E' := Nat.le_of_lt_succ hlt
      have h1 := ih hle
      have hd := objective_delta c₀ c₁ lam R₀ ρ E'
      have hmono := objective_delta_mono c₀ c₁ lam R₀ ρ hlam hR hρ hρ2 E E' hle
      simp only [objective_delta] at hmono
      have hpos : 0 ≤ objective c₀ c₁ lam R₀ ρ (E' + 1) - objective c₀ c₁ lam R₀ ρ E' := by
        rw [objective_delta]
        linarith
      linarith

end Hagi.Learning.EpochTradeoff

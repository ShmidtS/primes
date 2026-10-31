import Mathlib
import Hagi.Probability.NoiseTemperature

/-!
# BatchSNR (источник №76: McCandlish et al., "An Empirical
# Model of Large-Batch Training", arXiv 1812.06162)

Gradient noise scale: сигнал/шум батч-градиента растёт
ЛИНЕЙНО по размеру батча (следствие temperature law
Var(ĝ) = Var(g)/B из NoiseTemperature); критический
батч B* = σ²/μ² — порог, выше которого сигнал
превышает шум.
-/

namespace Hagi.Probability.BatchSNR

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Детерминированный SNR батч-градиента размера B:
μ²·B/σ² (σ² = popVar, μ = popMean). -/
noncomputable def snr (g : V → ℝ) (B : ℕ) : ℝ :=
  (popMean g)^2 * B / popVar g

/-- РЕАЛИЗОВАННЫЙ SNR: по temperature law (batch_variance_eq)
E[(ĝ−μ)²] = σ²/B, поэтому snr g B = μ²/E[(ĝ−μ)²] —
определение совпадает с фактическим отношением
сигнал/шум батч-градиента. -/
theorem snr_realized (g : V → ℝ) {b : ℕ} [Nonempty (Fin b)] :
    snr g b = (popMean g)^2
      / prodE (uniP b) (fun ω => (batchMean g ω - popMean g) ^ 2) := by
  have hv := batch_variance_eq (V := V) (b := b) g
  unfold snr
  rw [hv]
  field_simp

/-- ЛИНЕЙНОСТЬ ПО БАТЧУ: SNR(B) = B · SNR(1) — удвоение
батча удваивает отношение сигнал/шум (закон убывания
шума 1/B). -/
theorem snr_linear (g : V → ℝ) (B : ℕ) :
    snr g B = B * snr g 1 := by
  unfold snr
  field_simp
  ring

/-- КРИТИЧЕСКИЙ БАТЧ: B* = σ²/μ² (при μ ≠ 0, σ² > 0) —
минимальный вещественный размер батча с SNR = 1. -/
noncomputable def criticalBatch (g : V → ℝ) : ℝ :=
  popVar g / (popMean g)^2

/-- ПОРОГОВЫЙ ЗАКОН: SNR(B) ≥ 1 ⟺ B ≥ B* — выше
критического батча сигнал доминирует над шумом. -/
theorem snr_ge_one_iff (g : V → ℝ)
    (hμ : popMean g ≠ 0) (hσ : 0 < popVar g) (B : ℕ) :
    snr g B ≥ 1 ↔ criticalBatch g ≤ B := by
  have hμ2 : 0 < (popMean g)^2 := sq_pos_iff.mpr hμ
  unfold snr criticalBatch
  rw [ge_iff_le, le_div_iff₀ hσ, div_le_iff₀ hμ2]
  constructor <;> intro h <;> linarith

/-- Модель критического батча (источник №76, §4):
прогресс шага ∝ min(1, B/B*) — ниже B* прогресс
линейный по B, выше — насыщается (шум подавлен). -/
noncomputable def batchGain (Bstar : ℝ) (B : ℝ) : ℝ :=
  min 1 (B / Bstar)

/-- Стоимость шага: фиксированная β + линейная α·B
(параллелизм идеален до α). -/
noncomputable def stepCost (alpha beta B : ℝ) : ℝ :=
  alpha * B + beta

/-- Прогресс на единицу стоимости. -/
noncomputable def gainPerCost (Bstar alpha beta B : ℝ) : ℝ :=
  batchGain Bstar B / stepCost alpha beta B

/-- ЗАКОН УБЫВАНИЯ ЭФФЕКТИВНОСТИ: при B₂ > B₁ ≥ B*
прогресс на единицу стоимости СТРОГО убывает — за
критическим батчем каждый доп. образец покупает всё
меньше прогресса за вычисления (оптимум в B*). -/
theorem gain_decreasing_past_critical
    (Bstar alpha beta B1 B2 : ℝ)
    (hstar : 0 < Bstar) (hbeta : 0 < beta) (halpha : 0 < alpha)
    (h1 : Bstar ≤ B1) (h2 : B1 < B2) :
    gainPerCost Bstar alpha beta B2
      < gainPerCost Bstar alpha beta B1 := by
  have hmin1 : batchGain Bstar B1 = 1 :=
    min_eq_left ((le_div_iff₀ hstar).mpr (by linarith))
  have hmin2 : batchGain Bstar B2 = 1 :=
    min_eq_left ((le_div_iff₀ hstar).mpr (by linarith))
  unfold gainPerCost stepCost
  rw [hmin1, hmin2]
  have hB1pos : (0:ℝ) < B1 := lt_of_lt_of_le hstar h1
  have hc : (0:ℝ) < alpha * B1 + beta := by
    have hnn : 0 ≤ alpha * B1 :=
      mul_nonneg (le_of_lt halpha) (le_of_lt hB1pos)
    linarith
  have hc2 : (0:ℝ) < alpha * B2 + beta := by
    have hB2pos : (0:ℝ) < B2 := lt_of_lt_of_le hstar
      (le_trans h1 (le_of_lt h2))
    have hnn2 : 0 ≤ alpha * B2 :=
      mul_nonneg (le_of_lt halpha) (le_of_lt hB2pos)
    linarith
  rw [one_div_lt_one_div hc2 hc]
  have hBpos : (0:ℝ) < B2 - B1 := sub_pos.mpr h2
  have hmul : 0 < alpha * (B2 - B1) :=
    mul_pos halpha hBpos
  nlinarith [hmul]

end Hagi.Probability.BatchSNR

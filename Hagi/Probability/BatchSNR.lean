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

end Hagi.Probability.BatchSNR

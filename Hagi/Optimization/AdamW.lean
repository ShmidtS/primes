import Mathlib

/-!
# AdamW — decoupled weight decay (источник №64: Loshchilov
# & Hutter, "Decoupled Weight Decay Regularization",
# arXiv 1711.05101)

Идея: в AdamW decay РАСЦЕПЛЁН с градиентным шагом:
w ← (1 − λ)·w − η·s — затухание применяется к весам
напрямую, а не через L2-слагаемое градиента, делённое
адаптивным знаменателем. Формализуем ключевое следствие:
при нулевом градиенте веса СТРОГО сжимаются всегда,
тогда как coupled-L2 версия делит decay на √v̂ + 1 и
может давать сколь угодно малое эффективное затухание.
-/

namespace Hagi.Optimization.AdamW

/-- Шаг AdamW: decay-часть (1−λ)·w плюс градиентная s. -/
def adamwStep (lam eta : ℝ) (w s : ℝ) : ℝ :=
  (1 - lam) * w - eta * s

/-- Coupled-L2 шаг: decay через градиентное слагаемое,
делённое на адаптивный знаменатель √v̂ + 1. -/
noncomputable def l2Step (lam eta vhat : ℝ) (w : ℝ) : ℝ :=
  w - eta * (lam * w / (Real.sqrt vhat + 1))

/-- ИСТОЧНИК №64, УРОВЕНЬ 1: DECAY ДЕЙСТВУЕТ ВСЕГДА — при
нулевом градиенте, λ ∈ (0,1], w ≠ 0 шаг AdamW СТРОГО
сжимает модуль веса (фактор |1−λ| < 1). -/
theorem adamw_shrink (lam eta w : ℝ) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hw : w ≠ 0) :
    |adamwStep lam eta w 0| < |w| := by
  have h1 : adamwStep lam eta w 0 = (1 - lam) * w := by
    unfold adamwStep
    ring
  rw [h1, abs_mul]
  have habs : |1 - lam| < 1 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hw0 : 0 < |w| := abs_pos.mpr hw
  calc |1 - lam| * |w| < 1 * |w| :=
        mul_lt_mul_of_pos_right habs hw0
    _ = |w| := one_mul _

/-- УРОВЕНЬ 1b: COUPLED-L2 ОСЛАБЛЯЕТ DECAY — эффективный
decay-фактор L2-версии есть λ/(√v̂+1) ≤ λ, и при √v̂ ≥ 1/λ
он не превосходит λ² ≤ λ: coupled decay подавляется
адаптивным знаменателем (ядро критики источника №64). -/
theorem l2_decay_diluted (lam vhat : ℝ) (hlam : 0 < lam)
    (_hv : 0 ≤ vhat) (hbig : 1 ≤ lam * (Real.sqrt vhat + 1)) :
    lam / (Real.sqrt vhat + 1) ≤ lam * lam := by
  have hsq : 0 ≤ Real.sqrt vhat := Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt vhat + 1 := by positivity
  rw [div_le_iff₀ hden]
  have hmul : lam * 1 ≤ lam * (lam * (Real.sqrt vhat + 1)) :=
    mul_le_mul_of_nonneg_left hbig (le_of_lt hlam)
  linarith

end Hagi.Optimization.AdamW

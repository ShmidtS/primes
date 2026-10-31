import Mathlib

/-!
# LLRD — послойное затухание learning rate (источник №68:
# layer-wise learning rate decay, стандарт глубокого
# fine-tuning BERT-эпохи; напр. Howard & Ruder 1801.06146
# ULMFiT-дискриминативное тонкая настройка)

Идея: нижние (близкие к входу) слои — более общие, их
меньше трогают: η_l = η·γ^(L−l) с γ < 1 — чем глубже слой
(ближе к выходу), тем выше LR. Формализуем монотонность:
LR строго растёт с номером слоя при γ < 1.
-/

namespace Hagi.Optimization.LLRD

/-- LR слоя l в стеке глубины L: базовый η, затухание γ
на уровень глубины. -/
def layerLR (eta gamma : ℝ) (L l : ℕ) : ℝ :=
  eta * gamma ^ (L - l)

/-- ИСТОЧНИК №68, УРОВЕНЬ 1: МОНОТОННОСТЬ — при 0 < γ < 1,
η > 0 LR СТРОГО растёт с номером слоя (верхние слои учатся
быстрее; нижние почти заморожены). -/
theorem llrd_strict_mono (eta gamma : ℝ) (L l1 l2 : ℕ)
    (heta : 0 < eta) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hl : l1 < l2) (hl2 : l2 ≤ L) :
    layerLR eta gamma L l1 < layerLR eta gamma L l2 := by
  have hle : ∀ k : ℕ, gamma ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ m ih =>
        calc gamma ^ (m + 1) = gamma ^ m * gamma := pow_succ gamma m
          _ ≤ 1 * gamma :=
            mul_le_mul_of_nonneg_right ih hg.le
          _ = gamma := one_mul _
          _ ≤ 1 := le_of_lt hg1
  have hd : (L - l1 : ℕ) = (L - l2) + (l2 - l1) := by omega
  have hsplit : gamma ^ (L - l1)
      = gamma ^ (L - l2) * gamma ^ (l2 - l1) := by
    rw [hd, pow_add]
  have hpos2 : 0 < gamma ^ (L - l2) := pow_pos hg _
  have hsmall : gamma ^ (l2 - l1) < 1 := by
    have hk1 : l2 - l1 = (l2 - l1 - 1) + 1 := by omega
    rw [hk1, pow_succ]
    have hprev := hle (l2 - l1 - 1)
    nlinarith [hprev, hg, hg1]
  unfold layerLR
  have hkey : gamma ^ (L - l2) * gamma ^ (l2 - l1)
      < gamma ^ (L - l2) * 1 :=
    mul_lt_mul_of_pos_left hsmall hpos2
  rw [mul_one] at hkey
  rw [hsplit]
  exact mul_lt_mul_of_pos_left hkey heta

/-- УРОВЕНЬ 1b: НЕОТРИЦАТЕЛЬНОСТЬ всех LR. -/
theorem llrd_nonneg (eta gamma : ℝ) (L l : ℕ)
    (heta : 0 ≤ eta) (hg : 0 ≤ gamma) :
    0 ≤ layerLR eta gamma L l := by
  unfold layerLR
  exact mul_nonneg heta (pow_nonneg hg _)

end Hagi.Optimization.LLRD

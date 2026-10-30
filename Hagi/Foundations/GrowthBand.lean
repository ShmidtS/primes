import Mathlib

/-!
# GrowthBand — двухсторонняя полоса роста (аудит v10 P0)

Канонический дом полосы роста: независимые коэффициенты
alpha_min/alpha_max вместо одного (что вынуждает точное
насыщение). Живёт в нижнем слое Foundations — доступно
и Growth, и Model без нарушения слоёв.
-/

namespace Hagi.Foundations.GrowthBand

/-- АУДИТ v10 P0: ДВУХСТОРОННЯЯ ПОЛОСА РОСТА. Вместо
одновременных нижней и верхней границ одним коэффициентом
(что вынуждает ТОЧНОЕ насыщение C' = (1+α)C, G = αC,
D = (α/γ)C — см. takeoff_edge_forced) — два НЕЗАВИСИМЫХ
коэффициента αmin ≤ αmax: шаг может быть где угодно внутри
полосы. Это честная гарантия для обучения с шумом;
насыщение — частный случай αmin = αmax. -/
theorem growth_band_step (C C' G : ℝ) (αmin αmax : ℝ)
    (_h0 : 0 ≤ C) (_hmin : 0 ≤ αmin) (_hband : αmin ≤ αmax)
    (hstep : C' = C + G)
    (hGlo : αmin * C ≤ G) (hGhi : G ≤ αmax * C) :
    (1 + αmin) * C ≤ C' ∧ C' ≤ (1 + αmax) * C := by
  constructor <;> linarith

/-- ПОЛОСА НА T ШАГОВ: при сохранении полосы на каждом шаге
рост зажат между (1+αmin)^T и (1+αmax)^T от C0 — нижняя
граница экспоненциальна, верхняя не выше капа. -/
theorem growth_band_iter (C : ℕ → ℝ) (αmin αmax : ℝ)
    (hmin : 0 ≤ αmin) (hband : αmin ≤ αmax)
    (hstep : ∀ t, (1 + αmin) * C t ≤ C (t + 1)
      ∧ C (t + 1) ≤ (1 + αmax) * C t) :
    ∀ T, (1 + αmin) ^ T * C 0 ≤ C T
      ∧ C T ≤ (1 + αmax) ^ T * C 0 := by
  intro T
  induction T with
  | zero =>
      constructor <;> simp
  | succ t ih =>
      obtain ⟨hlo, hhi⟩ := hstep t
      obtain ⟨ihlo, ihhi⟩ := ih
      have hgpow : 0 ≤ 1 + αmin := by linarith
      have hGpow : 0 ≤ 1 + αmax := by linarith
      constructor
      · calc (1 + αmin) ^ (t + 1) * C 0
            = (1 + αmin) * ((1 + αmin) ^ t * C 0) := by ring
          _ ≤ (1 + αmin) * C t :=
            mul_le_mul_of_nonneg_left ihlo hgpow
          _ ≤ C (t + 1) := hlo
      · calc C (t + 1) ≤ (1 + αmax) * C t := hhi
          _ ≤ (1 + αmax) * ((1 + αmax) ^ t * C 0) :=
            mul_le_mul_of_nonneg_left ihhi hGpow
          _ = (1 + αmax) ^ (t + 1) * C 0 := by ring


end Hagi.Foundations.GrowthBand

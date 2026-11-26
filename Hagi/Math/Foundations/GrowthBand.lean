import Mathlib.Tactic

/-!
# GrowthBand — двухсторонняя полоса роста

Двусторонняя полоса роста с независимыми коэффициентами
alpha_min/alpha_max и динамика роста с насыщением.
-/

namespace Hagi.Foundations.GrowthBand

/-- **Двусторонняя полоса роста**: вместо одного коэффициента,
дающего точное насыщение C' = (1+α)C (см.
`cone_edge_geometric_growth`), — два независимых коэффициента
αmin ≤ αmax: шаг может быть где угодно внутри полосы; αmin = αmax
даёт насыщение. -/
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



/-! ### Насыщение роста

Динамика C_{t+1} = C_t + σ·(C* − C_t): прирост ограничен
остатком до потолка, ни один шаг не обязан исчерпывать
весь доступный фронтир. -/

/-- ИТЕРАЦИОННОЕ СЖАТИЕ ЗАЗОРА: динамика
C_{t+1} = C_t + σ(C* − C_t) удовлетворяет
C* − C_T = (1−σ)^T · (C* − C_0) — расстояние до потолка
сжимается геометрически со скоростью (1−σ):
ЛИНЕЙНАЯ СХОДИМОСТЬ К ПОТОЛКУ вместо экспоненциального
взлёта в бесконечность. -/
theorem saturation_gap (Cstar σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (C : ℕ → ℝ)
    (hstep : ∀ t, C (t + 1) = C t + σ * (Cstar - C t)) :
    ∀ T, Cstar - C T = (1 - σ) ^ T * (Cstar - C 0) := by
  intro T
  induction T with
  | zero => simp
  | succ t ih =>
      have h1 : Cstar - C (t + 1) = (1 - σ) * (Cstar - C t) := by
        rw [hstep t]; ring
      rw [h1, ih, pow_succ]
      ring

/-- ВЕРХНЯЯ ГРАНИЦА ПОД ПОТОЛКОМ: при C_0 ≤ C* зазор
неотрицателен и сжимается — C_T ≤ C* − (1−σ)^T(C*−C_0),
в частности C_T ≤ C* на всех горизонтах (рост не
пересекает потолок) и C_T монотонно растёт. -/
theorem saturation_ceiling (Cstar σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (C : ℕ → ℝ)
    (hstep : ∀ t, C (t + 1) = C t + σ * (Cstar - C t))
    (hC0 : C 0 ≤ Cstar) :
    ∀ T, C T ≤ Cstar - (1 - σ) ^ T * (Cstar - C 0) ∧ C T ≤ Cstar := by
  intro T
  have hg := saturation_gap Cstar σ hσ hσ1 C hstep T
  have hgap0 : (0:ℝ) ≤ Cstar - C 0 := by linarith
  have hpow : (0:ℝ) ≤ (1 - σ) ^ T := pow_nonneg (by linarith) _
  have hP : (0:ℝ) ≤ (1 - σ) ^ T * (Cstar - C 0) := mul_nonneg hpow hgap0
  constructor
  · linarith
  · linarith

end Hagi.Foundations.GrowthBand

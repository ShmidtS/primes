import Mathlib

/-!
# Законы смешивания данных (источник №13)

Источник №13: Ye et al., "Data Mixing Laws: Optimizing Data
Mixtures by Predicting Language Modeling Performance"
(arXiv 2403.16952, ICLR 2025).

Доменная функция потерь следует экспоненциальному закону от
линейной комбинации пропорций доменов смеси:
L(ρ) = K · exp(Σᵢ cᵢ·ρᵢ).

Формализовано ядро:
- mixingLoss (закон);
- exp_segment_le (взвешенная выпуклость exp);
- ВЫПУКЛОСТЬ закона смешивания по пропорциям — оптимизация
  смеси доменов есть выпуклая задача;
- Jensen-граница: смесь смесей не хуже худшего микса
  (потеря конкатенации смесей ≤ взвешенный микс потерь).
-/

namespace Hagi.Data.DataMixing

open Real

/-- Взвешенная выпуклость exp на ℝ. -/
theorem exp_segment_le (a b T : ℝ) (hT1 : 0 ≤ T) (hT2 : T ≤ 1) :
    exp (T * a + (1 - T) * b) ≤ T * exp a + (1 - T) * exp b := by
  have h := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ b)
    hT1 (show (0:ℝ) ≤ 1 - T by linarith)
    (show T + (1 - T) = 1 by ring)
  simpa [smul_eq_mul] using h

variable {n : Type*} [Fintype n]

/-- Закон смешивания: потеря на смеси ρ — K·exp(Σ cᵢρᵢ)
(экспоненциальная по линейной форме, источник №13). -/
noncomputable def mixingLoss (K : ℝ) (c : n → ℝ) (rho : n → ℝ) : ℝ :=
  K * exp (∑ i, c i * rho i)

/-- ВЫПУКЛОСТЬ ЗАКОНА СМЕШИВАНИЯ (ядро источника №13):
потеря K·exp(Σ cᵢρᵢ) выпукла по пропорциям смеси —
оптимизация смеси доменов есть ВЫПУКЛАЯ задача. -/
theorem mixing_loss_convex (K : ℝ) (hK : 0 ≤ K) (c : n → ℝ) :
    ConvexOn ℝ (Set.univ : Set (n → ℝ))
      (fun rho => mixingLoss K c rho) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have hlin : ∑ i, c i * ((a • x + b • y) i)
        = a * (∑ i, c i * x i) + b * (∑ i, c i * y i) := by
      rw [Finset.sum_congr rfl fun i _ => show c i * ((a • x + b • y) i)
        = a * (c i * x i) + b * (c i * y i) from by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    show mixingLoss K c (a • x + b • y)
      ≤ a • mixingLoss K c x + b • mixingLoss K c y
    rw [mixingLoss, mixingLoss, mixingLoss, hlin]
    have hseg := exp_segment_le (∑ i, c i * x i) (∑ i, c i * y i) a
      ha (show a ≤ 1 by linarith [ha, hb, hab])
    simp only [smul_eq_mul]
    have hb' : (1:ℝ) - a = b := by linarith
    rw [hb'] at hseg
    nlinarith [hseg, mul_nonneg hK (le_of_lt (exp_pos (∑ i, c i * x i))),
      mul_nonneg hK (le_of_lt (exp_pos (∑ i, c i * y i)))]

end Hagi.Data.DataMixing

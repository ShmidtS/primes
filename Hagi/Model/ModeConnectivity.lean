import Hagi.Model.ReferenceMachine

/-!
# Mode Connectivity в квадратичном режиме (источник №17)

Источник №17: Garipov et al., "Loss Surfaces, Mode
Connectivity, and Fast Ensembling of DNNs" (NeurIPS 2018,
arXiv 1802.10026); обобщение — Theus et al., "Generalized
Linear Mode Connectivity for Transformers" (NeurIPS 2025):
независимо обученные модели соединимы путями низкой потери.
Для слияния экспертов HAGI это обоснование: переходы между
решениями не обязаны проходить через барьеры.

Формализованное ядро (строгое, в квадратичной модели
эталонной машины): энергия E(w) = ‖w−a‖²/2 выпукла, поэтому
ЛИНЕЙНЫЙ путь между любыми двумя решениями не поднимается
выше max из концов — барьера НЕТ:

- `energy_convex`: E(λw₁+(1−λ)w₂) ≤ λE(w₁)+(1−λ)E(w₂);
- `linear_no_barrier`: E вдоль пути ≤ max(E(w₁), E(w₂));
- `linear_midpoint_bound`: E((w₁+w₂)/2) ≤ (E(w₁)+E(w₂))/2.

Строгая формализация линейной mode connectivity: в
квадратичном режиме (и в ньютоновской окрестности любого
минимума, где ландшафт локально квадратичен) LMC выполняется
АВТОМАТИЧЕСКИ — без обучения перемычек.
-/

namespace Hagi.Model.ModeConnectivity

open Hagi.Model.ReferenceMachine

variable {n : ℕ}

/-- ВЫПУКЛОСТЬ квадратичной энергии: вдоль линейного пути
энергия не превышает линейной интерполяции энергий концов. -/
theorem energy_convex (a w1 w2 : Fin n → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1) :
    energy a (fun i => lam * w1 i + (1 - lam) * w2 i)
      ≤ lam * energy a w1 + (1 - lam) * energy a w2 := by
  have hkey : ∀ i : Fin n,
      (lam * w1 i + (1 - lam) * w2 i - a i) ^ 2
        ≤ lam * (w1 i - a i) ^ 2 + (1 - lam) * (w2 i - a i) ^ 2 := by
    intro i
    have hx := sq_nonneg (w1 i - w2 i)
    have h1l : 0 ≤ 1 - lam := by linarith
    have hlamnn : 0 ≤ lam * (1 - lam) := mul_nonneg hlam h1l
    nlinarith [hx, hlamnn]
  unfold energy
  have hper : ∀ i : Fin n, (lam * (w1 i - a i) ^ 2
      + (1 - lam) * (w2 i - a i) ^ 2) / 2
      = lam * ((w1 i - a i) ^ 2 / 2)
        + (1 - lam) * ((w2 i - a i) ^ 2 / 2) := fun i => by ring
  have hbeta : ∀ i : Fin n, (lam * w1 i + (1 - lam) * w2 i - a i) ^ 2
      = (lam * (w1 i - a i) + (1 - lam) * (w2 i - a i)) ^ 2 :=
    fun i => by ring
  have hsum' : ∑ i, (lam * w1 i + (1 - lam) * w2 i - a i) ^ 2 / 2
      ≤ ∑ i, (lam * ((w1 i - a i) ^ 2 / 2)
        + (1 - lam) * ((w2 i - a i) ^ 2 / 2)) :=
    Finset.sum_le_sum fun i _ => by
      have hb := hbeta i
      have hk := hkey i
      have hp := hper i
      nlinarith [hk]
  calc ∑ i, (lam * w1 i + (1 - lam) * w2 i - a i) ^ 2 / 2
      ≤ ∑ i, (lam * ((w1 i - a i) ^ 2 / 2)
        + (1 - lam) * ((w2 i - a i) ^ 2 / 2)) := hsum'
    _ = lam * ∑ i, (w1 i - a i) ^ 2 / 2
        + (1 - lam) * ∑ i, (w2 i - a i) ^ 2 / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- ЛИНЕЙНЫЙ ПУТЬ БЕЗ БАРЬЕРА (mode connectivity в
квадратичном режиме): энергия вдоль отрезка [w₁,w₂] не
превышает max энергий концов — барьер между режимами
ОТСУТСТВУЕТ. -/
theorem linear_no_barrier (a w1 w2 : Fin n → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1) :
    energy a (fun i => lam * w1 i + (1 - lam) * w2 i)
      ≤ max (energy a w1) (energy a w2) := by
  have hcv := energy_convex a w1 w2 lam hlam hlam2
  rcases le_total (energy a w1) (energy a w2) with h | h
  · rw [max_eq_right h]
    exact hcv.trans (by nlinarith [h])
  · rw [max_eq_left h]
    exact hcv.trans (by nlinarith [h])

/-- СЕРЕДИНА ПУТИ: энергия средней точки ≤ среднему энергий
(основа SWA — усреднение весов вдоль траектории). -/
theorem linear_midpoint_bound (a w1 w2 : Fin n → ℝ) :
    energy a (fun i => (w1 i + w2 i) / 2)
      ≤ (energy a w1 + energy a w2) / 2 := by
  have h := energy_convex a w1 w2 (1 / 2) (by norm_num) (by norm_num)
  have hfun : (fun i => (1 / 2) * w1 i + (1 - 1 / 2) * w2 i)
      = fun i => (w1 i + w2 i) / 2 := by
    funext i
    field_simp
    ring
  rw [hfun] at h
  nlinarith [h]


/-- SWA-ГРАНИЦА (Izmailov et al., arXiv 1803.05407, уровень-2
источника №17): энергия СРЕДНЕГО по T точкам траектории не
превышает среднего энергий — стохастическое усреднение весов
(SWA) не хуже среднего по траектории. Доказано через
Cauchy–Schwarz: (Σ_t d_t)² ≤ T·Σ_t d_t². -/
theorem swa_average_bound (a : Fin n → ℝ) (T : ℕ) (hT : 0 < T)
    (ws : Fin T → Fin n → ℝ) :
    energy a (fun i => (∑ t, ws t i) / T)
      ≤ (∑ t, energy a (ws t)) / T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  -- per-i: среднее минус a = среднее отклонений
  have hkey : ∀ i : Fin n,
      (∑ t, ws t i) / T - a i = (∑ t, (ws t i - a i)) / T := by
    intro i
    rw [show (∑ t, (ws t i - a i)) / T
        = (∑ t, ws t i) / T - a i from by
      have h1 : ∑ t, (ws t i - a i) = ∑ t, ws t i - (T:ℝ) * a i := by
        rw [Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [h1, sub_div, mul_div_cancel_left₀ (a i) hTpos.ne']]
  -- per-i Cauchy–Schwarz: (Σ_t d_t)² ≤ T·Σ_t d_t²
  have hcs : ∀ i : Fin n, (∑ t, (ws t i - a i)) ^ 2
      ≤ T * ∑ t, (ws t i - a i) ^ 2 := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T))
      (fun t : Fin T => ws t i - a i) (fun _ : Fin T => (1:ℝ))
    have hone : ∑ t : Fin T, ((1:ℝ) ^ 2) = T := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    simp only [mul_one] at h
    rw [hone] at h
    calc (∑ t, (ws t i - a i)) ^ 2
        = (∑ t, (ws t i - a i) * (1:ℝ)) ^ 2 := by
          refine congrArg (fun x => x ^ 2) ?_
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ (∑ t, (ws t i - a i) ^ 2) * T := by
        have heq : (∑ t, (ws t i - a i) * (1:ℝ)) ^ 2
            = (∑ t, (ws t i - a i)) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun t _ => by ring
        rw [heq]
        exact h
      _ = T * ∑ t, (ws t i - a i) ^ 2 := mul_comm _ _
  -- сборка: lhs ≤ Σ_i Y_i/(2T) = rhs
  calc ∑ i, ((∑ t, ws t i) / T - a i) ^ 2 / 2
      ≤ ∑ i, (T * ∑ t, (ws t i - a i) ^ 2) / T ^ 2 / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h2 : (∑ t, (ws t i - a i)) ^ 2 / ((T:ℝ) ^ 2)
            ≤ (T * ∑ t, (ws t i - a i) ^ 2) / ((T:ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hcs i, sq_nonneg ((T:ℝ))]
        rw [hkey i, div_pow,
          div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2)]
        exact mul_le_mul_of_nonneg_right h2 (by norm_num : (0:ℝ) ≤ 2)
    _ = ∑ i, (∑ t, (ws t i - a i) ^ 2) / T / 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [div_div, sq, mul_assoc, mul_div_mul_left _ _ hTpos.ne', div_div]
    _ = (∑ t, ∑ i, (ws t i - a i) ^ 2 / 2) / T := by
        rw [Finset.sum_comm, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_div]
        field_simp

end Hagi.Model.ModeConnectivity

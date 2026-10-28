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

end Hagi.Model.ModeConnectivity

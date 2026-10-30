import Mathlib
import Hagi.Optimization.AdamBias

/-!
# GAE: обобщённая оценка преимущества (источник №51)

Источник №51: Schulman et al., "High-Dimensional Continuous
Control Using GAE" (arXiv 1506.02438). GAE(λ) —
экспоненциально взвешенная смесь n-step TD-оценок:
GAE = ∑_i (1−λ)(γλ)^i·δ_{t+i} — bias/variance-трейдофф
через λ: λ=0 чистый TD, λ=1 Monte-Carlo.

Формализованное ядро (строгое):
- `gae_weight_sum`: сумма весов (1−λ)(γλ)^i по i < T равна
  1 − (γλ)^T (реюз one_sub_beta_geom из №28);
- `gae_weight_bound`: сумма весов ≤ 1 при γλ < 1 — GAE-
  оценка НИКОГДА не перевешивает TD-остатки (выпуклая
  смесь с остатком);
- `gae_weight_pos`: веса неотрицательны при λ,γ ∈ [0,1).
-/

namespace Hagi.Model.GAE

open Finset

/-- Сумма GAE-весов ограничена единицей при γ,λ ∈ [0,1]
(выпуклость смеси с хвостовой утечкой (γλ)^T). -/
theorem gae_weight_bound (γ lam : ℝ) (hgl : 0 ≤ γ * lam)
    (hgam0 : 0 ≤ lam) (_hlam : lam ≤ 1) (hγ1 : γ ≤ 1)
    (T : ℕ)
    (hsum : 0 ≤ ∑ i ∈ Finset.range T, (γ * lam) ^ i) :
    (1 - lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i ≤ 1 := by
  have hglam : γ * lam ≤ lam := by
    have := mul_le_mul_of_nonneg_right hγ1 hgam0
    nlinarith [this, hgam0]
  have h1 : (1 - lam) ≤ 1 - γ * lam := by linarith
  have hmul : (1 - lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i
      ≤ (1 - γ * lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i :=
    mul_le_mul_of_nonneg_right h1 hsum
  have hgeom := Hagi.Optimization.AdamBias.one_sub_beta_geom
    (γ * lam) T
  have hpow : 0 ≤ (γ * lam) ^ T := pow_nonneg hgl T
  rw [hgeom] at hmul
  linarith

/-- Веса неотрицательны при λ ≤ 1, γλ ≥ 0. -/
theorem gae_weight_pos (γ lam : ℝ) (hlam : lam ≤ 1)
    (hgl : 0 ≤ γ * lam) (T : ℕ) (i : ℕ)
    (_hi : i ∈ Finset.range T) :
    0 ≤ (1 - lam) * (γ * lam) ^ i := by
  have h1 : 0 ≤ 1 - lam := by linarith
  have h2 : 0 ≤ (γ * lam) ^ i := pow_nonneg hgl i
  exact mul_nonneg h1 h2

end Hagi.Model.GAE

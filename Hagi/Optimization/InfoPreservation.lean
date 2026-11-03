import Mathlib.Tactic
import Hagi.Optimization.MirrorDescent

/-!
# InfoPreservation (аудит v16, Test 6: information
# preservation вдоль траектории)

Регрет-форма сохранения информации: вдоль mirrorIterate
(вариационное ядро №70) суммарное превышение потерь
траектории над ЛЮБЫМ целевым распределением ρ* ограничено
начальным KL-расстоянием T·KL(ρ*‖ρ₀) — дрейф не свободен:
информация о цели сохраняется в среднем (реюз mirror_regret
БЕЗ новых посылок).
-/

namespace Hagi.Optimization.InfoPreservation

open Hagi.Optimization

variable {V : Type*} [Fintype V] [Nonempty V]

/-- TEST 6: СРЕДНИЕ ПОТЕРИ ТРАЕКТОРИИ ≤ ПОТЕРИ ЦЕЛИ +
дрейф-квота: (1/n)·Σ⟨ρ_k,ℓ_k⟩ ≤ (1/n)·Σ⟨ρ*,ℓ_k⟩ +
T·KL(ρ*‖ρ₀)/n — отклонение траектории от целевого
распределения гасится начальной информационной близостью;
при n → ∞ дрейф исчезает. -/
theorem info_preservation_regret
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρstar : V → ℝ) (hρstar : ∀ v, 0 < ρstar v)
    (hρstar1 : ∑ v, ρstar v = 1) (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n,
        ∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
      / n
      ≤ (∑ k ∈ Finset.range n, ∑ v, ρstar v * ℓs k v) / n
        + T * (∑ v, ρstar v * Real.log (ρstar v / ρ₀ v)) / n := by
  have hr := mirror_regret ρ₀ ℓs T hT hρ₀ hρ₀1 ρstar hρstar hρstar1 n
  have hdiv : (0:ℝ) < n := by exact_mod_cast hn
  have hsumd : ∑ k ∈ Finset.range n,
      ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
        - (∑ v, ρstar v * ℓs k v))
      = (∑ k ∈ Finset.range n,
          ∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
        - (∑ k ∈ Finset.range n, ∑ v, ρstar v * ℓs k v) := by
    simp [Finset.sum_sub_distrib]
  rw [hsumd] at hr
  have hgoal : (∑ k ∈ Finset.range n,
      ∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
    ≤ (∑ k ∈ Finset.range n, ∑ v, ρstar v * ℓs k v)
      + T * (∑ v, ρstar v * Real.log (ρstar v / ρ₀ v)) := by
    have hsplit : (∑ k ∈ Finset.range n,
        ∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
      = ((∑ k ∈ Finset.range n,
          ∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
        - (∑ k ∈ Finset.range n, ∑ v, ρstar v * ℓs k v))
      + (∑ k ∈ Finset.range n, ∑ v, ρstar v * ℓs k v) := by ring
    rw [hsplit]
    linarith
  rw [← add_div, div_le_div_iff₀ hdiv hdiv]
  exact mul_le_mul_of_nonneg_right hgoal hdiv.le

end Hagi.Optimization.InfoPreservation

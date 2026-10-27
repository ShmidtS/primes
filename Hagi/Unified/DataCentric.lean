import Hagi.Pretraining.DataPruning
import Hagi.Pretraining.RobustnessLaw

/-!
# Unified.DataCentric — фасад data-centric блока

Слой-6 фасад: RobustnessLaw + DataPruning. Дихотомия
прореживания: гладкие (L-липшицевы) таргеты на плотных сетках
восстанавливаются с ошибкой ≤ L·δ; состязательные таргеты
гарантируют NFL-потерю ≥ 1.
-/

namespace Hagi.Unified

export Hagi.Pretraining (pruning_nfl pruning_free_for_constant
  pruning_recovery_bound robust_interpolation_lipschitz_floor
  lipschitz_floor_of_noisy_labels noisy_interpolation_step_cap
  robust_slows_learning robust_budget_floor)

/-- ДИХОТОМИЯ PRUNING: (1) гладкий таргет на плотной сетке —
ошибка восстановления выброшенной точки ≤ L·δ; (2)
состязательный таргет — любой ученик теряет ≥ 1 в сумме.
Успех прореживания определяется гладкостью таргета и
плотностью сетки, а не алгоритмом отбора. -/
theorem pruning_dichotomy (f : ℝ → ℝ) (t x0 x1 : ℝ) (L δ : ℝ)
    (kept : Finset ℕ) (p : ℕ)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hl : x0 ≤ t) (hr : t ≤ x1) (hδ : |x1 - x0| ≤ δ)
    (hp : p ∉ kept)
    (g : (ℕ → ℝ) → ℝ)
    (hagree : ∀ y1 y2 : ℕ → ℝ, (∀ i ∈ kept, y1 i = y2 i) →
      g y1 = g y2) :
    |f t - f x0| ≤ L * δ ∧
    (1:ℝ) ≤ |g (fun _ => (0:ℝ)) - (fun _ => (0:ℝ)) p|
      + |g (fun i => if i = p then (1:ℝ) else 0)
        - (fun i => if i = p then (1:ℝ) else 0) p| :=
  ⟨pruning_recovery_bound f t x0 x1 L δ hlip hl hr hδ,
    pruning_nfl kept p hp g hagree⟩

end Hagi.Unified

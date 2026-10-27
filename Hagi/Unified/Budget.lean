import Hagi.Budget.WaterFilling
import Hagi.Budget.FlopsEconomy
import Hagi.Budget.BitAlloc
import Hagi.Budget.ThermoCondensation
import Hagi.Budget.WaterFillingMoE

/-!
# Unified.Budget — фасад бюджетной экономии

Слой-6 фасад: бюджетный блок HAGI. Балансировка аллокаций
(WaterFilling), амортизированный рост (FlopsEconomy),
дистилляционные цепочки (BitAlloc), термокон­денсация
(ThermoCondensation), MoE-водозаполнение (WaterFillingMoE).
-/

namespace Hagi.Unified

export Hagi.Budget (exists_balanced_allocation
  amortized_growth_cheaper pipeline_beats_baseline_iff
  marginalValue_law)
export Hagi.Ensemble (distill_chain_telescoping)

/-- БЮДЖЕТНЫЙ ПРИНЦИП (сводка): (1) для любых стоимостей
слоёв существует сбалансированная аллокация бит; (2)
дистилляционная цепочка телескопирует ошибки с
контролируемым суммарным дельта-зазором — обе экономики
одновременно достижимы. -/
theorem budget_allocation_and_distillation {m : ℕ}
    (c : Fin m → ℝ) (B : ℕ) (hc : ∀ l, 0 ≤ c l)
    (n : ℕ) (S E : ℕ → ℝ) (delta : ℕ → ℝ)
    (hdist : ∀ k ≤ n, S k ≤ E k + delta k)
    (hgrow : ∀ k < n, E (k + 1) ≤ S k) :
    (∃ f : Fin m → ℕ,
      (∑ l, f l ≤ B) ∧
      (∀ j k : Fin m, f k ≠ 0 →
        Hagi.Budget.layerError (c j) (f j)
          ≤ 2 * Hagi.Budget.layerError (c k) (f k)))
    ∧ S n ≤ E 0 + ∑ k ∈ Finset.range (n + 1), delta k :=
  ⟨exists_balanced_allocation c B hc,
    Hagi.Ensemble.distill_chain_telescoping n hdist hgrow⟩

end Hagi.Unified

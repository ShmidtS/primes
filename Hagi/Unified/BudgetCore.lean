import Mathlib
import Hagi.Budget.ActiveCompute
import Hagi.Budget.AnytimeCondensation
import Hagi.Budget.BatchCap
import Hagi.Budget.BitAlloc
import Hagi.Budget.BitAllocTermination
import Hagi.Budget.CertifiedArgmax
import Hagi.Budget.DesignOpt
import Hagi.Budget.ElementQuant
import Hagi.Budget.FlopsEconomy
import Hagi.Budget.JointCost
import Hagi.Budget.KVWater
import Hagi.Budget.RankBudget
import Hagi.Budget.ThermoCondensation
import Hagi.Budget.TokenWeightBias
import Hagi.Budget.WaterFilling
import Hagi.Budget.WaterFillingMoE

/-!
# BudgetCore — объединённый бюджетный фасад
(слияние одно-теоремных фасадов Budget/BudgetExt, аудит v9 P3).
-/

namespace Hagi.Unified


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



/-!
# Unified.BudgetExt — фасад бюджетных расширений

Слой-6 фасад: KV-водолив, блочно-низкоранговые затраты,
терминация бит-аллокации, активные флопсы, anytime-сгущение.
-/

namespace Hagi.Unified

export Hagi.Budget (waterfilling_bound block_lowrank_lt_dense_iff
  alloc_entry_le active_flops rankResidual_equalized)

/-- БЮДЖЕТНАЯ ЭКОНОМИЯ (сводка): (1) KV-водолив оптимален —
выравнивание экспоненциальных остатков минимизирует
Hagi.Budget.kvResidual при том же бюджете; (2) блочно-низкоранговое
представление строго дешевле плотного ⟺ 3r < (N−1)h.
-/
theorem budget_waterfill_and_lowrank
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (kappa lam : ℝ)
    (hlam : 0 < lam) (bstar b : ι → ℝ)
    (heq : ∀ i, c i * Real.exp (-kappa * bstar i) = lam)
    (hbudget : ∑ i, b i = ∑ i, bstar i)
    (N h r : ℝ) (hh : 0 < h) (hN : 2 ≤ N) :
    Hagi.Budget.kvResidual c kappa bstar ≤ Hagi.Budget.kvResidual c kappa b
      ∧ ((N * h^2 + 3 * (N * h) * r < (N * h)^2)
          ↔ 3 * r < (N - 1) * h) :=
  ⟨waterfilling_bound c kappa lam hlam bstar b heq hbudget,
    block_lowrank_lt_dense_iff N h r hh hN⟩


end Hagi.Unified

import Hagi.Budget.ActiveCompute
import Hagi.Budget.AnytimeCondensation
import Hagi.Budget.BatchCap
import Hagi.Budget.BitAllocTermination
import Hagi.Budget.CertifiedArgmax
import Hagi.Budget.DesignOpt
import Hagi.Budget.ElementQuant
import Hagi.Budget.JointCost
import Hagi.Budget.KVWater
import Hagi.Budget.RankBudget
import Hagi.Budget.TokenWeightBias

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

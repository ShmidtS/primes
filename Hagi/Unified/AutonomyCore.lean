import Hagi.Autonomy.HedgeSurvivor
import Hagi.Autonomy.Insight
import Hagi.Autonomy.ParetoController
import Hagi.Autonomy.SupervisorSafety
import Hagi.Autonomy.SupervisorViability
import Hagi.Autonomy.TTTStability

/-!
# Unified.AutonomyCore — фасад автономного контура

Слой-6 фасад: адаптация (EW-регрет из склеенной цепочки
Hedge), самонаблюдение (KL-десцент инсайта), стабильность
test-time-training (BIBO), надзор (viability/safety).
-/

namespace Hagi.Unified

export Hagi.Autonomy (ew_regret hsurv_derived insight_kl_descent
  forgetting_kl_bound ttt_bibo ttt_chain_bounded)

/-- ПРИНЦИП АВТОНОМИИ (сводка): (1) адаптация не хуже
эталона — EW-регрет ≤ ln K/η + ηT/2 (склеенная цепочка
hedge_step → hsurv → router_regret_bound); (2) test-time
обновления BIBO-стабильны (|W^T x| ≤ |x| при |W| ≤ 1).
АВТОНОМИЯ = подклеенный регрет + ограниченная динамика. -/
theorem autonomy_regret_and_stability
    {ι : Type} [Fintype ι] [Nonempty ι]
    (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (heta : 0 < eta ∧ eta ≤ 1)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1)
    (W x : ℝ) (hW : abs W ≤ 1) :
    (∑ t ∈ Finset.range T, ∑ i,
        Hagi.Autonomy.ewNorm l eta t i * l t i)
      - ∑ t ∈ Finset.range T, l t i
      ≤ Real.log (Fintype.card ι) / eta + eta * T / 2
      ∧ abs (W ^ T * x) ≤ abs x :=
  ⟨Hagi.Autonomy.ew_regret l eta T i heta hl,
    Hagi.Autonomy.ttt_bibo W hW x T⟩

end Hagi.Unified

import Hagi.Step.MDLThreeCurrency
import Hagi.Step.HybridState
import Hagi.Step.MetricSafeQP
import Hagi.Step.Muon
import Hagi.Step.MuonTwoLevel
import Hagi.Step.NewtonPolar
import Hagi.Step.PreconditionerDescent
import Hagi.Step.SNRWeights
import Hagi.Optimization.AdaptiveCycle
import Hagi.Optimization.DirectionPacking
import Hagi.Optimization.SphericalDamping
import Hagi.Optimization.SubspaceGrowth

/-!
# Unified.OptStepExt — фасад оптимизационных расширений

Слой-6 фасад: MDL-трёхвалютный объектив, гибридное
состояние (устаревший момент), Muon-разложения,
Ньютон–полярный, адаптивный цикл, сферическое демпфирование.
-/

namespace Hagi.Unified

export Hagi.Step (J3_nonincreasing stale_momentum_bias
  newton_polar_scalar_error)
export Hagi.Optimization (adaptive_cycle_expansions
  chordal_residual_eq projResidual_ortho)

/-- ОПТИМИЗАЦИОННАЯ ДИСЦИПЛИНА (сводка): (1) трёхвалютный
MDL-объектив монотонен по компонентам; (2) устаревший слот
момента — это истинный градиент плюс измеримое смещение.
Объектив честен, инерция учтена. -/
theorem opt_objective_monotone_and_bias_bounded
    (Lp Lp' Cst Cst' Rp Rp' lamM lamR : ℝ)
    (hp : Lp' ≤ Lp) (hc : Cst' ≤ Cst) (hr : Rp' ≤ Rp)
    (hM : 0 ≤ lamM) (hR : 0 ≤ lamR)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (g0 gt slot : V)
    (hslot : slot = g0) :
    Hagi.Step.J3 Lp' Cst' Rp' lamM lamR
      ≤ Hagi.Step.J3 Lp Cst Rp lamM lamR
      ∧ ∃ bias : V, slot = gt + bias ∧ ‖bias‖ = ‖g0 - gt‖ :=
  ⟨J3_nonincreasing Lp Lp' Cst Cst' Rp Rp' lamM lamR hp hc hr
      hM hR,
    stale_momentum_bias g0 gt slot hslot⟩

end Hagi.Unified

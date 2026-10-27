import Hagi.Step.MDLObjective
import Hagi.Step.MuonWD
import Hagi.Step.NCEExact
import Hagi.Step.RiemannNewtonPolar
import Hagi.Step.Upgrades
import Hagi.Step.WarmupSchedule
import Hagi.Step.WeightDecay
import Hagi.Core.Element
import Hagi.Core.F3Root
import Hagi.Core.FrobOuter
import Hagi.Core.Hadamard
import Hagi.Core.Lift
import Hagi.Core.NonlinearStep0
import Hagi.Core.RealF3Ortho
import Hagi.Core.Select

/-!
# Unified.StepExt — фасад расширений шага и компонентов

Слой-6 фасад: warmup-расписание, weight decay, Muon-WD
рекурсия, NCE-декомпозиция, обновления с пропусками;
ортогональные корни F3, жадный выбор.
-/

namespace Hagi.Unified

export Hagi.Step (warmup_eta_monotone wd_norm_bound
  muon_wd_recursion nce_decomposition)
export Hagi.Core (frobSq_outer_orthonormal meanBound_greedy
  root_invariance)

/-- РАСПИСАНИЕ И ОГРАНИЧЕНИЕ (сводка): (1) warmup-шаг
монотонен по зазору Δ (меньше зазор — меньше η); (2)
weight-decay рекурсия ограничивает норму весов
max‖w 0‖ (G/λ). Динамика шага управляема на всём горизонте. -/
theorem step_warmup_monotone_and_wd_bounded
    (c K0 Krho rho Δ Δ' : ℝ)
    (hc : 0 ≤ c) (hle : Δ' ≤ Δ) (hΔ' : 0 < Δ')
    (hrho : 0 < rho) (hKr : 0 < Krho)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (w g : ℕ → X)
    (eta lam G : ℝ)
    (hlam : 0 < lam) (hetal : 0 ≤ eta * lam)
    (hetau : eta * lam ≤ 1)
    (hG : ∀ t, ‖g t‖ ≤ G)
    (hrec : ∀ t, w (t + 1) = (1 - eta * lam) • (w t) - eta • (g t))
    (t : ℕ) :
    Hagi.Step.warmupEta c K0 Krho rho Δ
      ≤ Hagi.Step.warmupEta c K0 Krho rho Δ'
      ∧ ‖w t‖ ≤ max ‖w 0‖ (G / lam) :=
  ⟨warmup_eta_monotone c K0 Krho rho Δ Δ' hc hle hΔ' hrho hKr,
    wd_norm_bound w g eta lam G hlam hetal hetau hG hrec t⟩

end Hagi.Unified

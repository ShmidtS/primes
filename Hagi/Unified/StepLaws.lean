/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Step.ArmijoAcceptance
import Hagi.Step.CausalFilter
import Hagi.Step.Compound
import Hagi.Step.FrobeniusLMO
import Hagi.Step.GPM
import Hagi.Step.LazyAdam
import Hagi.Runtime.ControllerGates
import Hagi.Runtime.LiveDeltaQuant
import Hagi.Sparsity.SparseStep0
import Hagi.Step.MDLObjective
import Hagi.Step.Muon
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
# Шаговые законы (объединённые)

StepLaws и StepExt. Имена деклараций сохранены.
-/

/-!
# Unified.StepLaws — фасад теории шага

Слой-6 фасад: условия Armijo, стабильный SGD-шаг, точный
lazy-decay, GQA-фильтрация, компаунд-стабилизация.
-/

open Real InnerProductSpace

namespace Hagi.Unified

export Hagi.Step (armijo_sufficient_decrease sgd_stable_step
  lazyDecay_exact compound_c_stabilizes)

/-- ТЕОРИЯ ШАГА (сводка): (1) условие Armijo с направлением
спуска и гладкостью даёт достаточное убывание; (2) SGD-шаг с
η < 2⟪G,G⟫/(λ‖G‖²) строго убывает. Шаг одновременно
согласован и стабилен. -/
theorem step_armijo_and_sgd_stable
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (J : X → ℝ) (g d : X)
    (L c1 alpha : ℝ) (hL : 0 ≤ L) (hc1 : 0 < c1)
    (halpha : 0 < alpha)
    (hdir : ⟪g, d⟫_ℝ ≤ -(c1 * ‖d‖ ^ 2))
    (hsmooth : J (0 + alpha • d) ≤ J 0 + ⟪g, alpha • d⟫_ℝ
      + L / 2 * ‖alpha • d‖^2)
    (L' G eta lam : ℝ)
    (heta_pos : 0 < eta) (hlam : 0 < lam) (hG : G ≠ 0)
    (hquad : L' ≤ L - eta * ⟪G, G⟫_ℝ
      + lam / 2 * eta ^ 2 * ‖G‖ ^ 2)
    (heta : eta < 2 * ⟪G, G⟫_ℝ / (lam * ‖G‖ ^ 2)) :
    J (0 + alpha • d) ≤ J 0 - (c1 - L * alpha / 2) * alpha * ‖d‖^2
      ∧ L' < L :=
  ⟨armijo_sufficient_decrease J g d L c1 alpha hL hc1 halpha
      hdir hsmooth,
    sgd_stable_step L L' G eta lam heta_pos hlam hG hquad heta⟩

end Hagi.Unified

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

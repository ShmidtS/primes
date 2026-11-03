/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Architecture.AlignedMerge
import Hagi.Architecture.Configuration
import Hagi.Architecture.CortexFiber
import Hagi.Architecture.FactorRank
import Hagi.Architecture.FactorizedMerge
import Hagi.Architecture.Heterarchy
import Hagi.Architecture.LiveDelta
import Hagi.Architecture.OrthoInjection
import Hagi.Architecture.ResidualSplit
import Hagi.Audit.Audit
import Hagi.Autonomy.HedgeSurvivor
import Hagi.Autonomy.Insight
import Hagi.Autonomy.SupervisorSafety
import Hagi.Autonomy.SupervisorViability
import Hagi.Autonomy.TTTStability
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
import Hagi.Core.Attention
import Hagi.Core.Element
import Hagi.Core.ErrorProp
import Hagi.Core.F3Root
import Hagi.Core.FrobOuter
import Hagi.Core.Hadamard
import Hagi.Core.Kronecker
import Hagi.Core.Lift
import Hagi.Core.Mix
import Hagi.Core.NonlinearStep0
import Hagi.Core.RealF3Ortho
import Hagi.Core.Ridge
import Hagi.Core.Select
import Hagi.Data.CertifiedArgmax
import Hagi.Data.DBridge
import Hagi.Data.DField
import Hagi.Data.DFieldKKT
import Hagi.Data.DistillRecursion
import Hagi.Data.InfoNCE
import Hagi.Data.NessDissipation
import Hagi.Data.PACBayes
import Hagi.Discovery.PPT
import Hagi.Dynamics.ControllerPolicy
import Hagi.Dynamics.EndpointContraction
import Hagi.Dynamics.FastGrowth
import Hagi.Dynamics.Laws
import Hagi.Dynamics.ProxyGap
import Hagi.Dynamics.WallClockTakeoff
import Hagi.Energy.Cooling
import Hagi.Energy.EntropyProduction
import Hagi.Energy.FreeEnergy
import Hagi.Energy.PoEBound
import Hagi.Energy.PreNorm
import Hagi.Energy.STEStep
import Hagi.Ensemble.CompressionCert
import Hagi.Ensemble.Hoeffding
import Hagi.Ensemble.MergeIdentity
import Hagi.Ensemble.MergeMixture
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.MergeScaling
import Hagi.Ensemble.PolicyCompatibility
import Hagi.Ensemble.QFormerBridge
import Hagi.Ensemble.SigmaKernel
import Hagi.Ensemble.UniformCert
import Hagi.External.Diversity
import Hagi.External.Flywheel.CoherenceCharacterization
import Hagi.External.Flywheel.CourantFischer
import Hagi.External.Flywheel.FrobeniusNorm
import Hagi.External.Flywheel.MDLRank
import Hagi.External.Flywheel.MatrixNormRelations
import Hagi.External.Flywheel.NormSupport
import Hagi.External.Flywheel.SVD
import Hagi.External.Flywheel.SpectralNormGap
import Hagi.External.Flywheel.TruncatedSVDRank1
import Hagi.External.Flywheel.WeylInequality
import Hagi.Foundations.GrowthDynamics
import Hagi.Growth.AdaptiveQuery
import Hagi.Growth.Ceilings
import Hagi.Growth.ChainUnification
import Hagi.Growth.ConeDynamics
import Hagi.Growth.FiberNecessity
import Hagi.Growth.FrontierProduction
import Hagi.Growth.GammaDeficit
import Hagi.Growth.Grow
import Hagi.Growth.GrowthGate
import Hagi.Growth.IntegrationOrder
import Hagi.Growth.NoiseDisentangle
import Hagi.Growth.PlasticityLedger
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.RoundViability
import Hagi.Growth.SeedOnly
import Hagi.Growth.Thermostat
import Hagi.Information.Capacity
import Hagi.Model.Adaptive
import Hagi.Model.CycleCertificate
import Hagi.Model.HypothesisCompetition
import Hagi.Model.Memory
import Hagi.Model.Sidon
import Hagi.Model.SoftmaxStep
import Hagi.Model.StageSemantics
import Hagi.Numerics.SoftmaxFix
import Hagi.Omni.CrossModalGap
import Hagi.Omni.OmniInvariant
import Hagi.Omni.OmniState
import Hagi.Optimization.AdaptiveCycle
import Hagi.Optimization.DirectionPacking
import Hagi.Optimization.SphericalDamping
import Hagi.Optimization.SubspaceGrowth
import Hagi.Pretraining.DataPruning
import Hagi.Pretraining.Dust
import Hagi.Pretraining.DustAlign
import Hagi.Pretraining.ProbeError
import Hagi.Pretraining.RobustnessLaw
import Hagi.Pretraining.Speedrun
import Hagi.Pretraining.SyntheticPretrain
import Hagi.Pretraining.TrustRegion
import Hagi.Probability.PinskerTV
import Hagi.Probability.StationaryFlatness
import Hagi.Probability.ThermoAxes
import Hagi.Probability.ThermoBridge
import Hagi.Runtime.ControllerGates
import Hagi.Runtime.LiveDeltaQuant
import Hagi.Sparsity.SparseStep0
import Hagi.Spectral.RankGrowth
import Hagi.Step.ArmijoAcceptance
import Hagi.Step.CausalFilter
import Hagi.Step.Compound
import Hagi.Step.FrobeniusLMO
import Hagi.Step.GPM
import Hagi.Step.HybridState
import Hagi.Step.LazyAdam
import Hagi.Step.MDLObjective
import Hagi.Step.MDLThreeCurrency
import Hagi.Step.Muon
import Hagi.Step.NCEExact
import Hagi.Step.NewtonPolar
import Hagi.Step.PreconditionerDescent
import Hagi.Step.RiemannNewtonPolar
import Hagi.Step.SNRWeights
import Hagi.Step.Upgrades
import Hagi.Step.VariantSafeQP
import Hagi.Step.WarmupSchedule
import Hagi.Step.WeightDecay
import Hagi.System.DiscreteStep
import Hagi.System.StepCertificate
import Hagi.System.UnifiedStep
import Hagi.Unified.ArchitectureTheorem
import Mathlib.Tactic

set_option linter.style.header false

open Finset Matrix
open Matrix
open Matrix Finset
open Real InnerProductSpace
open scoped BigOperators

/-!
# FacadeLaws — консолидированный реестр фасадных конъюнкций
(merge-before-delete: 8 фасадных файлов Unified/*Core/CoreFacades/
StepLaws слиты в один модуль; все декларации и namespace
Hagi.Unified сохранены дословно; реальная семантика — в
канонических леммах, на которые конъюнкции делегируют.)
-/

/-! ## (was Unified/CoreFacades.lean) -/
namespace Hagi.Unified


/-!
# Unified.ArchitectureCore — фасад архитектурного блока

Слой-6 фасад: архитектурные принципы HAGI — ортогональные
волокна (нет взаимных помех), конфигурационная экономия
(разреженная маршрутизация дешевле плотной), гетерархичность
(нет глобального ранжирования модулей).
-/

open Finset Matrix


export Hagi.Architecture (fiberSplitOrtho fiberActionNoInterference
  config_storage_beats_dense no_global_ranking cycle_breaks_ranking
  routed_eval_exact orthoNorm)

/-- АРХИТЕКТУРНЫЙ ПРИНЦИП (сводка): (1) ортогональная
инъекция не создаёт помех — проекция исчерпывает действие
(fiberSplitOrtho); (2) конфигурация r≪d экономит память
строго (config_storage_beats_dense). Архитектура HAGI
одновременно инвариантна (волокна) и экономна. -/
theorem architecture_invariant_and_economical
    {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : Hagi.Architecture.IsOrthoCol U) (A : Matrix (Fin d) (Fin r) ℝ)
    (dd nn : ℕ) (h : nn * r < dd) (hd : 0 < dd) :
    Uᵀ * (A - U * (Uᵀ * A)) = 0
      ∧ (nn * r) * dd < dd * dd :=
  ⟨fiberSplitOrtho U hU A,
    config_storage_beats_dense dd r nn h hd⟩


/-!
# Unified.AutonomyCore — фасад автономного контура

Слой-6 фасад: адаптация (EW-регрет из склеенной цепочки
Hedge), самонаблюдение (KL-десцент инсайта), стабильность
test-time-training (BIBO), надзор (viability/safety).
-/


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

/-!
# Unified.MiscCore — фасад разрозненных теоремных модулей

Слой-6 фасад: дискретный шаг (квантованный телескоп),
сертификаты шага, Айкен-экстраполяция, PPT-норма,
softmax-фикс, временные состояния, QFormer-мост,
разнообразие, ранговый рост.
-/


export Hagi.System (quantized_descent_telescope)
export Hagi.Audit (aitken_exact exp_jensen)

/-- ЧИСЛЕННАЯ ДИСЦИПЛИНА (сводка): (1) квантованный
градиентный телескоп накапливает ошибку не более T·Δ/2;
(2) Айкен-экстраполяция геометрического убывания ТОЧНА.
Дискретизация контролируема, ускорение точно. -/
theorem misc_quantized_telescope_and_aitken
    (x g : ℕ → ℝ) (Δ γ : ℝ)
    (hΔ : 0 < Δ) (T : ℕ)
    (hstep : ∀ t < T, x (t + 1)
      = Hagi.Energy.gridQ Δ hΔ (x t - γ * g t))
    (Lstar d c L0 L1 L2 : ℝ)
    (h0 : L0 = Lstar + d) (h1 : L1 = Lstar + d * c)
    (h2 : L2 = Lstar + d * c^2) (hd : d ≠ 0) (hc : c ≠ 1) :
    x T ≤ x 0 - (∑ t ∈ Finset.range T, γ * g t) + (T : ℝ) * Δ / 2
      ∧ (L0 * L2 - L1^2) / (L0 + L2 - 2*L1) = Lstar
        ∧ (L2 - L1) / (L1 - L0) = c :=
  ⟨quantized_descent_telescope x g Δ γ hΔ T hstep,
    aitken_exact Lstar d c L0 L1 L2 h0 h1 h2 hd hc⟩

end Hagi.Unified


/-! ## (was Unified/StepLaws.lean) -/
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


/-! ## (was Unified/BudgetCore.lean) -/
namespace Hagi.Unified


/-!
# Unified.Budget — фасад бюджетной экономии

Слой-6 фасад: бюджетный блок HAGI. Балансировка аллокаций
(WaterFilling), амортизированный рост (FlopsEconomy),
дистилляционные цепочки (BitAlloc), термокон­денсация
(ThermoCondensation), MoE-водозаполнение (WaterFillingMoE).
-/


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


/-! ## (was Unified/AlgebraMatrixCore.lean) -/
namespace Hagi.Unified

/-!
# Unified.CoreAlgebra — фасад компонентной алгебры

Слой-6 фасад: компонентные примитивы HAGI — устойчивость
внимания (ошибка демпфируется весами), оптимальность риджа
(решение нормального уравнения минимизирует), распространение
ошибки по слоям, кронекерова алгебра.
-/


export Hagi.Core (attention_error_damped_sum attention_error_damped
  propagate_bound ridge_optimal kronecker_mul_conjTranspose
  mixed_invisible)

/-- КОМПОНЕНТНЫЙ ПРИНЦИП (сводка): (1) ошибка внимания
демпфируется весами (‖Δ‖ ≤ Σ p·‖e‖); (2) ридж-решение
нормального уравнения глобально оптимально. Смешение не
создает видимых артефактов (mixed_invisible) — примитивы
корректны по построению. -/
theorem core_stable_and_optimal
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ι → ℝ) (v e : ι → E)
    (hp : ∀ i, 0 ≤ p i)
    {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ)
    (y : m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) {w₀ : n → ℝ}
    (hne : ridgeNormalEq X y lam w₀) :
    ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ ∑ i, p i * ‖e i‖
      ∧ ∀ w : n → ℝ, ridge X y lam w ≥ ridge X y lam w₀ :=
  ⟨attention_error_damped_sum p v e hp,
    ridge_optimal hlam hne⟩


/-!
# Unified.MatrixLib — фасад матричной библиотеки Flywheel

Слой-6 фасад: SVD, Эккарт–Янг, Вейль, Курант–Фишер,
кронекеровы перестановки, MDL-ранг. Кандидат в апстрим
Mathlib (план аудита v5 L1-Matrix).
-/

open Matrix


/-- МАТРИЧНАЯ БИБЛИОТЕКА (сводка): (1) сингулярные значения
неотрицательны; (2) MDL-ошибка усечения антинтонна по
рангу (больше ранг — меньше ошибка). Спектральная теория
корректна и монотонна. -/
theorem matrix_svd_nonneg_and_mdl_antitone
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    ∀ i : n, 0 ≤ Hagi.External.Flywheel.Matrix.SVD.singularValues A i
      ∧ Antitone (Hagi.External.Flywheel.Hagi.MDL.Rank.mdlErr A) := by
  intro i
  exact ⟨Hagi.External.Flywheel.Matrix.SVD.singularValues_nonneg A i,
    Hagi.External.Flywheel.Hagi.MDL.Rank.mdlErr_antitone A⟩

end Hagi.Unified


/-! ## (was Unified/InfoDataCore.lean) -/
namespace Hagi.Unified



/-!
# Pinsker — единая точка входа семейства Пинскера (P1.5)

Консолидация форм неравенства Пинскера (план P1.5;
дубли «Pinsker×2 + KL/TV-модули»):

* **Функциональная форма** (`Hagi.Information.Pinsker`,
  `pinsker4_fin`): |E_q f − E_p f| ≤ 2√KL для 0 ≤ f ≤ 1;
* **TV-форма** (`Hagi.Probability.PinskerTV`,
  `pinsker_sqrt_kl`): ½ Σ|p−q| ≤ √KL — классика через
  Бхаттачарью;
* **Энтропийная непрерывность** (`entropy_continuity_pinsker`
  и `'`-вариант в этом же модуле Unified): Фанне-Пинскер
  оценка |H(p) − H(q)|.

Все формы на канонических `Prelude.klDef/entDef/tvDef`;
настоящий модуль — фасад и реестр форм (P1.5), дубликатных
определений нет.
-/

/-- ДЕДУП-МОСТ (аудит v5 п.5): f-форма Пинскера
(pinsker4_fin, Information) выводится из канонной TV-формы
(pinsker_sqrt_kl, Probability): разность ожиданий ограничена
тотал-вариацией, TV ≤ √KL. Копии связаны, примитив один. -/
theorem pinsker4_via_canon {V : Type*} [Fintype V] [Nonempty V]
    (q p f : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
  -- |Eq f − Ep f| ≤ Σ|q − p|
  have hstep : ∀ v, |(q v - p v) * f v| ≤ |q v - p v| := by
    intro v
    have h1 : |(q v - p v) * f v| = |q v - p v| * |f v| :=
      abs_mul _ _
    rw [h1, mul_comm]
    have h2 : |f v| ≤ 1 := by
      rcases lt_or_ge (f v) 0 with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith [(hf v).1]
      · rw [abs_of_nonneg h]
        exact (hf v).2
    nlinarith [h2, abs_nonneg (q v - p v)]
  have habs : abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := by
    have hsplit : ∑ v, q v * f v - ∑ v, p v * f v
        = ∑ v, (q v - p v) * f v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hsplit]
    calc abs (∑ v, (q v - p v) * f v)
        ≤ ∑ v, |(q v - p v) * f v| :=
          Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ v, |q v - p v| :=
          Finset.sum_le_sum (fun v _ => hstep v)
  -- канон: ½Σ|p−q| ≤ √KL(p||q) = √klDef q p (симметрия ролей)
  have hcanon := Hagi.Probability.pinsker_sqrt_kl q p hq hsumq
    hp hsump
  -- klDef q p = Σ q·log(q/p): канон даёт Σ p·log(p/q) с
  -- ролями (q,p) → Σ q·log(q/p) = klDef q p ✓
  calc abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := habs
    _ = 2 * ((1/2) * ∑ v, |q v - p v|) := by ring
    _ ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
        apply mul_le_mul_of_nonneg_left hcanon (by norm_num)


/-!
# Unified.ProbInfo — фасад вероятностно-информационного блока

Слой-6 фасад: восстановимость усиления, маршрутизационная
ёмкость, экспоненциальная хорда, ось шума/температуры,
мосты ПМФ/термодинамики.
-/


export Hagi.Information (no_free_recovery devEnergyF_pos_iff)
export Hagi.Probability (noise_axes_coincide prodE_as_expQ
  tail_sum_identity)

/-- ПРИНЦИП ИНФОРМАЦИИ (сводка): (1) бесплатного
восстановления нет — хорошая пара encode/decode на одном
слове даёт witnesses-код; (2) энергия девиации строго
положительна ⟺ девиация ненулевая (обнаружимость).
Информация измерима и не бесплатна. -/
theorem info_not_free_and_detectable
    {A Q : Type} (encode : A → Q)
    (decode : Q → A) (good : A → A → Prop) (w : A)
    (h : good (decode (encode w)) w)
    {N d : ℕ} (dev : Fin N → Fin d → ℝ) :
    (∃ q : Q, good (decode q) w)
      ∧ (0 < Hagi.Information.devEnergyF dev
          ↔ ∃ k : Fin N, dev k ≠ 0) :=
  ⟨no_free_recovery encode decode good w h,
    devEnergyF_pos_iff dev⟩

/-!
# Unified.DataCentric — фасад data-centric блока

Слой-6 фасад: RobustnessLaw + DataPruning. Дихотомия
прореживания: гладкие (L-липшицевы) таргеты на плотных сетках
восстанавливаются с ошибкой ≤ L·δ; состязательные таргеты
гарантируют NFL-потерю ≥ 1.
-/


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


/-!
# Unified.DataEnergy — фасад данных и энергии

Слой-6 фасад: сертифицированный argmax, поле данных (KKT),
дистилляционная рекурсия, InfoNCE, PAC-Bayes, диссипация
Несса, термодинамика (охлаждение, свободная энергия, Ландауэр).
-/


export Hagi.Data.CertifiedArgmax (certified_argmax_strict)
export Hagi.Data (dfield_ascent_transfer fresh_data_prevents_collapse_uniform)
export Hagi.Energy (two_level_meanEnergy_strictMono partition_cold_limit)

/-- ПРИНЦИП ДАННЫХ И ЭНЕРГИИ (сводка): (1) сертифицированный
argmax устойчив при зазоре 2ε; (2) положительная
теплоёмкость — средняя энергия строго растёт по T
(двухуровневая система). Выбор и термодинамика корректны. -/
theorem data_certified_and_thermodynamic
    {ι : Type*} [Fintype ι] [Nonempty ι] {v est : ι → ℝ} {ε : ℝ}
    (herr : ∀ i, |est i - v i| ≤ ε)
    {imax : ι} (hgap : ∀ i, i ≠ imax → 2 * ε < v imax - v i)
    (ℓ : ι → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v) :
    (∀ i, i ≠ imax → est i < est imax)
      ∧ Filter.Tendsto (fun T : ℝ => ∑ v, Real.exp (-(ℓ v)/T))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (∑ v, if ℓ v = 0 then (1:ℝ) else 0)) :=
  ⟨certified_argmax_strict herr hgap,
    partition_cold_limit ℓ hℓ⟩

end Hagi.Unified


/-! ## (was Unified/DynamicsGrowthCore.lean) -/
namespace Hagi.Unified


/-!
# Unified.DynamicsLaws — фасад динамики и омнимодальности

Слой-6 фасад: счётный такофф (мультипликативный рост),
KL-контракция при дистилляции, endpoint-контракция,
wall-clock такофф, омни-инварианты.
-/


export Hagi.Dynamics (kl_contraction_budget
  capability_gain_transfer depth_capped_by_time)
export Hagi.Foundations (capability_takeoff_counted)

/-- ДИНАМИКА (сводка): (1) мультипликативный рост с
интенсивностями s t даёт C T ≥ C 0·(1+α)^{Σs}; (2)
KL-контракция с бюджетом: kl T ≤ δ при достаточном горизонте.
Рост и сжатие одновременно управляемы. -/
theorem dynamics_growth_and_distillation
    (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (kl : ℕ → ℝ) (κ_KL δ : ℝ)
    (hκ : 0 < κ_KL) (hκ1 : κ_KL < 1) (hδ : 0 < δ)
    (hstep : ∀ t, kl (t + 1) ≤ κ_KL * kl t)
    (hneed : kl 0 / δ ≤ (1 / κ_KL) ^ T) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t)
      ∧ kl T ≤ 0 + δ :=
  ⟨Hagi.Foundations.capability_takeoff_counted C s alpha halpha
      hmul T,
    Hagi.Dynamics.kl_contraction_budget kl κ_KL δ T hκ hκ1 hδ
      hstep hneed⟩



/-!
# Unified.GrowthLaws — фасад законов роста

Слой-6 фасад: потенциал-телескоп (диссипативный баланс),
гамма-дефицит, конусная динамика данных.
-/


export Hagi.Growth (potential_telescope
  gamma_min_for_target cone_data_invariant)

/-- ЗАКОН РОСТА (сводка): (1) диссипативный баланс —
потенциал-телескоп W T + Σε ≤ W 0 + Σb; (2) конусная
инвариантность данных (k·C ≤ D сохраняется шагом). Рост
ограничен и структурно инвариантен. -/
theorem growth_balanced_and_conic
    (W eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ W t)
    (hstep : ∀ t, W (t + 1) ≤ W t - eps t + b t)
    (cd : Hagi.Growth.ConeData) (k : ℝ)
    (hk : 0 ≤ k) (hγ : 0 ≤ cd.γ) (hρ : 0 ≤ cd.ρ)
    (hCpos : 0 < cd.C T)
    (hcone : k * cd.C T ≤ cd.D T)
    (h_dyn : cd.ρ * cd.D T + cd.β * cd.C T - cd.ξ T
      ≤ cd.D (T + 1))
    (h_C_cap : cd.C (T + 1) ≤ (1 + cd.γ * k) * cd.C T)
    (hβ : k * (1 + cd.γ * k - cd.ρ) + cd.ξ T / cd.C T
      ≤ cd.β) :
    W T + ∑ t ∈ Finset.range T, eps t
      ≤ W 0 + ∑ t ∈ Finset.range T, b t
      ∧ k * cd.C (T + 1) ≤ cd.D (T + 1) :=
  ⟨potential_telescope W eps b T hVnn hstep,
    Hagi.Growth.cone_data_invariant cd k T hk hγ hρ hCpos
      hcone h_dyn h_C_cap hβ⟩


/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
set_option linter.style.header false

/-!
# Global dynamics: idle behavior and the Fisher forgetting bound

* `safeqp_idle`: `dist 0 0 ≤ dist d 0` for every `d ∈ C` (the
  g₀ = 0 specialization of the SafeQP objective).
* `idle_merge_zero_gap`: at consensus logits the merge gap is
  exactly 0.
-/

open Real InnerProductSpace


/-- At a softmax distribution with all pairwise logit
deviations 0, `twoGap` is exactly 0. The compression stage's
idle behavior is not formalized here. -/

theorem idle_merge_zero_gap {k : Type} [Fintype k] [Nonempty k]
    (m : k → ℝ) (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.twoGap (fun v => Real.exp (m v) / ∑ w, Real.exp (m w)) (fun _ => (0:ℝ)) = 0 :=
    (Hagi.twoGap_zero_iff hp hsum).mpr ⟨0, fun _ => rfl⟩



end Hagi.Unified


/-! ## (was Unified/GrowthEnsembleCore.lean) -/
namespace Hagi.Unified

/-!
# Unified.GrowthExt — фасад расширений роста

Слой-6 фасад: обновление возможностей (self-development),
затухание посевного цикла, нелинейный конус, пластичность,
термостат, T3-зажигание.
-/


export Hagi.Growth (opportunity_renewal cycle_decay_mono
  round_exhausted thermostat_stop kl_le_log_card
  training_core_is_measurement_tail orthogonal_noise_averaging)

/-- САМОРАЗВИТИЕ (сводка): (1) при конусной динамике с полом
возможностей фронт строго растёт (D + ΔO ≤ D'); (2)
посевной капитал затухает монотонно, оставаясь
неотрицательным. Саморазвитие возобновляет ресурс и не
истощает посев. -/
theorem growth_renews_and_seed_survives
    (D D' C rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi)
    (F k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hk : 0 < k) (hklt : k < F + s) :
    D + deltaO ≤ D'
      ∧ F * (1 - k/(F + s)) < F
        ∧ 0 ≤ F * (1 - k/(F + s)) :=
  ⟨opportunity_renewal D D' C rho beta xi deltaO hdyn hfloor,
    cycle_decay_mono F k s hs hF hk hklt⟩


/-!
# Unified.EnsembleTheory — фасад теории ансамблей

Слой-6 фасад: слияние и маршрутизация — shift-инвариантность
softmax, точность смешанной продукции, квадратичная цена
слияния, sigma-ядро, совместимость политик.
-/

open Matrix Finset


export Hagi.Ensemble (softmax_shift_invariance
  geometric_mean_logit_mean merged_output_exact routing_drift_bound
  merge_price_quad uniform_good_mass integration_net_gain_pos)

/-- ПРИНЦИП СЛИЯНИЯ (сводка): (1) softmax-маршрутизация
инвариантна к сдвигу логитов (выбор не зависит от калибровки);
(2) смешанная продукция точна (линейность по построению). -/
theorem merge_calibrated_and_exact {V : Type} [Fintype V]
    (z : V → ℝ) (c : ℝ) {m d : ℕ} (w : Fin m → ℝ)
    (x : Fin d → ℝ)
    {W : Fin m → Matrix (Fin d) (Fin d) ℝ} :
    (fun v => Real.exp (z v + c) / ∑ u, Real.exp (z u + c))
      = (fun v => Real.exp (z v) / ∑ u, Real.exp (z u))
      ∧ (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) :=
  ⟨Hagi.Ensemble.softmax_shift_invariance V z c,
    merged_output_exact W w x⟩


/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

/-!
# DualCeiling — двойной потолок термостата (R559)

Объединение двух ограничительных каналов: полоса-потолок
(R556) и γ-бюджет-потолок (R530-гейт). Capability ограничен
минимумом двух потолков.
-/

open scoped BigOperators


/-- **Двойной потолок (R559)**: при затухающей полосе прироста
и γ-гейте (α·C t ≤ G t ≤ γ·D̄) capability ограничен обоими
потолками сразу: C T ≤ C 0 + b/σ (полоса, R556) и
C T ≤ γ·D̄/α (γ-бюджет через гейт). -/
theorem dual_ceiling (C G D : ℕ → ℝ) (b σ Dbar alpha gamma : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgate : ∀ t, alpha * C t ≤ G t)
    (hgain : ∀ t, G t ≤ gamma * Dbar)
    (hα : 0 < alpha) :
    C T ≤ C 0 + b / σ ∧ C T ≤ gamma * Dbar / alpha := by
  classical
  obtain ⟨_, hceil⟩ := Hagi.Foundations.geometric_band_ceiling
    C G b σ T hstep hband hb hσ hσ1
  refine ⟨hceil, ?_⟩
  have hgateT : C T * alpha ≤ gamma * Dbar := by
    have h1 : alpha * C T ≤ G T := hgate T
    have h2 : G T ≤ gamma * Dbar := hgain T
    have h3 : alpha * C T ≤ gamma * Dbar := le_trans h1 h2
    rw [mul_comm] at h3
    exact h3
  exact (le_div_iff₀ hα).mpr hgateT

end Hagi.Unified


/-! ## (was Unified/PretrainOptRobustCore.lean) -/
namespace Hagi.Unified


/-!
# Unified.ModelPretrain — фасад модели и предобучения

Слой-6 фасад: сертификаты цикла, конкуренция гипотез,
консолидация памяти, MoE-расширение, сидон-множества;
пылевые оценки, зонное выравнивание, синтетическое
предобучение, trust region.
-/


export Hagi.Model (consolidation_bits_cap cycle_certificate_composition)
export Hagi.Pretraining (time_to_capability_correct)

/-- ПАМЯТЬ И ВРЕМЯ (сводка): (1) консолидация ограничена
битами записи (F ≤ B/cUnit); (2) время до capability
корректно определено (первый достижимый момент, монотонный
хвост). Ресурсы и горизонты согласованы. -/
theorem memory_capped_and_time_correct
    (B cUnit F : ℝ) (hcUnit : 0 < cUnit)
    (h_emp_memwrite : cUnit * F ≤ B)
    (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n)
    (hmono : ∀ t, C t ≤ C (t + 1)) :
    F ≤ B / cUnit
      ∧ τ ≤ C (Hagi.Pretraining.TimeToCapability τ C hreach)
        ∧ (∀ k < Hagi.Pretraining.TimeToCapability τ C hreach, C k < τ) :=
  ⟨consolidation_bits_cap B cUnit F hcUnit h_emp_memwrite,
    (time_to_capability_correct τ C hreach hmono).1,
    (time_to_capability_correct τ C hreach hmono).2.1⟩



/-!
# Unified.OptStepExt — фасад оптимизационных расширений

Слой-6 фасад: MDL-трёхвалютный объектив, гибридное
состояние (устаревший момент), Muon-разложения,
Ньютон–полярный, адаптивный цикл, сферическое демпфирование.
-/


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



/-!
# Unified.Robustness — фасад теории робастности

Слой-6 фасад (LayerLint-валиден: Information не импортируется):
robustness-теория данных + бюджетный капстоун HAGI
образуют КОРИДОР РОСТА: шумные данные ставят нижнюю границу
бюджета (robust_budget_floor), бюджет — верхнюю границу
роста (budget_capability_ceiling).
-/


export Hagi.Pretraining (robust_interpolation_lipschitz_floor
  lipschitz_floor_of_noisy_labels noisy_interpolation_step_cap
  robust_slows_learning robust_budget_floor)

/-- КОРИДОР РОБАСТНОГО РОСТА: достижение смещения D на
шумных данных (σ при шаге δ) требует бюджета
B0 ≥ c·D·σ/(δ·G) (пол), а любой бюджет B0 ограничивает
итоговую capability сверху: C T ≤ (1+α)^(B0/c)·C0
(потолок). Данные и физика зажимают рост с двух сторон. -/
theorem robust_growth_corridor {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (tr : Hagi.Model.Trajectory X) (α c D σ δ G η : ℝ)
    (hα : 1 ≤ 1 + α) (hc : 0 < c) (hD : 0 < D)
    (hσ : 0 < σ) (hδ : 0 < δ) (hη : 0 ≤ η) (hG : 0 < G)
    (hcost : ∀ t < tr.T, c ≤ (tr.input t).eff.growCost
      + (tr.input t).eff.mergeCost
      + (tr.input t).eff.jointCost
      + (tr.input t).eff.compressCost)
    (hbudget : ∀ t ≤ tr.T, 0 ≤ (tr.state t).budget)
    (hC0 : 0 ≤ (tr.state 0).capability)
    (hcap : ∀ t < tr.T, (tr.state (t + 1)).capability
      ≤ (1 + α) * (tr.state t).capability)
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L : ℝ)
    (hi : i + 1 < n)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hnoise : σ ≤ |y (i + 1) - y i|)
    (hspace : |x (i + 1) - x i| ≤ δ)
    (hstab : η * L ≤ 1)
    (hprogress : D ≤ (tr.T : ℝ) * (η * G)) :
    c * (D * σ / (δ * G)) ≤ (tr.state 0).budget
      ∧ (tr.state tr.T).capability
        ≤ (1 + α) ^ ((tr.state 0).budget / c)
          * (tr.state 0).capability := by
  refine ⟨?_,
    Hagi.Model.budget_capability_ceiling tr α c hα hc hcost hbudget hC0
      hcap⟩
  -- связка: телескоп бюджета траектории даёт T·c ≤ B0
  have hB : (tr.T : ℝ) * c ≤ (tr.state 0).budget := by
    have htele : ∀ n : ℕ, n ≤ tr.T →
        (tr.state n).budget
          ≤ (tr.state 0).budget - (n : ℝ) * c := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hstep := tr.h_step n (by omega)
        have hc' := hcost n (by omega)
        have ih' := ih (by omega)
        have hbud : (tr.state (n + 1)).budget
            ≤ (tr.state n).budget - c := by
          rw [hstep]
          simp only [Hagi.Model.advance]
          linarith
        have hcast : (((n : ℝ) + 1)) * c = (n : ℝ) * c + c := by ring
        have hcast2 : ((n + 1 : ℕ) : ℝ) * c = (n : ℝ) * c + c := by
          push_cast
          ring
        nlinarith [hbud, ih']
    have h0 := htele tr.T (le_refl _)
    have hnn := hbudget tr.T (le_refl _)
    linarith
  exact robust_budget_floor f x y n i L σ δ η G D (tr.T : ℝ) c
    (tr.state 0).budget hi hσ hδ hη hG (le_of_lt hc) (Nat.cast_nonneg _) hinter
    hlip hnoise hspace hstab hprogress hB

end Hagi.Unified

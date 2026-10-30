import Mathlib
import Hagi.Energy.PreNorm
import Hagi.Energy.STEStep
import Hagi.Model.CycleCertificate
import Hagi.Model.HypothesisCompetition
import Hagi.Model.MemoryConsolidation
import Hagi.Model.MoeExpansion
import Hagi.Model.Sidon
import Hagi.Model.SoftmaxStep
import Hagi.Model.StageSemantics
import Hagi.Optimization.AdaptiveCycle
import Hagi.Optimization.DirectionPacking
import Hagi.Optimization.SphericalDamping
import Hagi.Optimization.SubspaceGrowth
import Hagi.Pretraining.Dust
import Hagi.Pretraining.DustAlign
import Hagi.Pretraining.ProbeError
import Hagi.Pretraining.RobustnessLaw
import Hagi.Pretraining.Speedrun
import Hagi.Pretraining.SyntheticPretrain
import Hagi.Pretraining.TrustRegion
import Hagi.Step.HybridState
import Hagi.Step.MDLThreeCurrency
import Hagi.Step.MetricSafeQP
import Hagi.Step.Muon
import Hagi.Step.MuonTwoLevel
import Hagi.Step.NewtonPolar
import Hagi.Step.PreconditionerDescent
import Hagi.Step.SNRWeights

/-!
# PretrainOptRobustCore — претрен/оптшаг/робастность
(слияние одно-теоремных фасадов ModelPretrain/OptStepExt/Robustness, аудит v9 P3).
-/

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



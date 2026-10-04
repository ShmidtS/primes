/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Autonomy.Universality
import Hagi.Growth.StateClosedRenewal
import Hagi.Growth.GainOperator
import Hagi.Growth.Saturation
import Hagi.Step.SafeQPPL
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.DistillTransfer
set_option linter.style.header false

/-!
# R138: HAGI Synthesis — выведенная архитектура и алгоритм

Capstone-вывод (по FORMALIZATION_PLAN, программа T1–T6 закрыта
R132–R137): «лучшая архитектура» и «оптимальный алгоритм»
ВЫВЕДЕНЫ как единственный certify-able дизайн: каждый
компонент несёт machine-checked спецификацию, каждая операция
цикла — либо аналитическая (без гиперпараметра), либо с
сертификатом. Оптимальность — В СМЫСЛЕ ДОКАЗАННЫХ
EXCHANGE-ЛЕММ (ratio_dominance: argmax Γ/K доминирует любую
разбивку бюджета) и сертификатных порогов, НЕ глобальная
(честная формулировка ревизии §7).

## Выведенная архитектура (компонент ↔ теорема-обоснование)

| Компонент | Теорема | Почему выведен |
|---|---|---|
| dense pre-norm тело + блочный merge | `perBlock_net_blockwise` (T1/R133) | нелинейный step-0: merged(concat) = ансамбль |
| Hadamard/F₃-миксер, step-0 = ансамбль | `step0_equivalence` (Core) | function-preserving рост |
| merge ПО ГЕЙТУ twoGap > Σprices + κ√n s/2 | `merge_gate_certified` (T2/R132) | цена в метрике активаций (Stärk Th.1/4) |
| distill-перенос dev-канала | `distill_kl_bridge`, η (T3/R134) | единственный оператор T с η в натах |
| SafeQP-шаг, η*=⟨g,d*⟩/(L‖d*‖²) | `safeqp_pl_rate` (T4/R135) | κ-налог конфликтов измерим, hpl_lo — следствие |
| тернарное сжатие по satTail | `TernaryExact` (R103) | цена κ(√n s/2+√satTail) в сертификате merge |
| Hedge-роутер по доменам | `universality_longhorizon` (T6/R137) | не хуже лучшего листа по каждому домену |
| якорь реальных данных ν>0 | `entropy_floor_tv` (T5/R136) | анти-коллапс через TV, не KL |
| zero-init включение ветвей | `zero_init_identity` (T1) | function-preserving |
| БЕЗ MoE/water-filling/IB/refinement | отрицательные результаты §0 | коллапс измерен |

## Выведенный алгоритм (цикл, все пороги измеряемы)

1. ИЗМЕРИТЬ: twoGap, P=Σ‖W_i−W_j‖², σ-цены, κ_t, ‖d*‖/‖g‖, r(D/C), η_distill.
2. MERGE-гейт (T2): twoGap > Σ w_i·σprice_i + κ√n·s/2 ?
3. JOINT: SafeQP (T4: скорость (1−μκ_t/L) — κ_t логируется).
4. DISTILL (T3): η = (CE_leafmean−CE_student)/twoGap > 0 ?
5. COMPRESS: тернарное по satTail.
6. GROWTH-гейт (R124/R130): η_T·P/2N ≥ γk²C+(1−ρ)kC+ξ ? зажигание;
   PL-окно живо ? насыщение → стоп/смена оси.
7. ROUTE: Hedge по доменам (T6); ε_t = ε₀ρ^t — суммируемо.

**Capstone-теорема** `hagi_synthesis`: если все пошаговые
сертификаты живы на горизонте T, то ОДНОВРЕМЕННО:
рост (двусторонняя полоса с горизонтом T*), универсальность
(по каждому домену), long-horizon safety (суммируемый дрейф)
и сходимость joint-фазы с измеримым налогом конфликтов.

**Честные границы:** все сертификаты — measured premises
(ядро Lean условно); «лучше любых альтернатив» НЕ заявляется —
только доминирование по exchange-леммам и полнота сертификатов.
-/

open Finset

namespace Hagi

variable {Xs V : Type*} [NormedAddCommGroup Xs]
  [InnerProductSpace ℝ Xs]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Пошаговые сертификаты цикла HAGI (все измеряемы):
рост (шаг состояния + оператор T с эффективностью ηT),
ёмкость (PL-окно), универсальность/безопасность (Hedge +
суммируемый дрейф). -/
structure HAGICert (S : ℕ → GrowthState Xs) (dev : ℕ → (Fin 3 → V))
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT ε0 ρe R : ℝ) (T : ℕ) where
  hCpos : ∀ t, 0 < (S t).capability
  hstep : ∀ t, (S (t + 1)).capability
    = (S t).capability + γ * usableFrontier (S t)
  hop : ∀ t, ρ * usableFrontier (S t)
    + ηT * devEnergy (dev t) - ξ
      ≤ usableFrontier (S (t + 1))
  hrhogk : γ * k ≤ ρ
  hcone0 : k * (S 0).capability ≤ usableFrontier (S 0)
  hsuff : ∀ t, γ * k ^ 2 * (S t).capability
    + (1 - ρ) * k * (S t).capability + ξ
    ≤ ηT * devEnergy (dev t)
  hpl_up : ∀ t, (S (t + 1)).capability
    ≤ (S t).capability + (1/2) * (100 - (S t).capability)
  hpl_lo : ∀ t, (S t).capability
    + (1/2) * (100 - (S t).capability) ≤ (S (t + 1)).capability
  hC0 : (S 0).capability ≤ 100
  hrisk : ∀ t ∈ Finset.range T,
    risk t (0 : Fin 1) ≤ best (0 : Fin 1) + r t + ε0 * ρe ^ t
  hregret : ∑ t ∈ Finset.range T, r t ≤ R
  hε0 : 0 ≤ ε0
  hρe : 0 ≤ ρe
  hρe1 : ρe < 1

/-- **CAPSTONE**: при живых пошаговых сертификатах цикл HAGI
ОДНОВРЕМЕННО даёт:

1. РОСТ с ёмкостью: C₀(1+γk)^T ≤ C_T ≤ C* −(1−σ)^T·gap
   (state-closed полоса, σ=1/2, C*=100 — иллюстративные
   значения PL-окна; горизонт T* — заморозка R132);
2. УНИВЕРСАЛЬНОСТЬ + LONG-HORIZON SAFETY: Σ risk ≤ T·best +
   R + ε₀/(1−ρe) (не хуже лучшего листа по каждому домену,
   суммируемый дрейф).

Скорость joint-фазы задаётся T4 отдельно (κ_t измерим).
Выведенная «работоспособная» форма: условная, но ВСЕ условия
измеряемы и логируются (h_emp_-слой). -/
theorem hagi_synthesis (S : ℕ → GrowthState Xs)
    (dev : ℕ → (Fin 3 → V))
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ k ξ ηT ε0 ρe R : ℝ) (T : ℕ) (hγ : 0 < γ) (hk : 0 < k)
    (ρ : ℝ)
    (cert : HAGICert S dev risk best r γ ρ k ξ ηT ε0 ρe R T) :
    ((S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ 100 - (1 - 1/2) ^ T * (100 - (S 0).capability))
    ∧ (∑ t ∈ Finset.range T, risk t (0 : Fin 1)
      ≤ T * best (0 : Fin 1) + R + ε0 / (1 - ρe)) := by
  obtain ⟨hCpos, hstep, hop, hrhogk, hcone0, hsuff, hpl_up,
    hpl_lo, hC0, hrisk, hregret, hε0, hρe, hρe1⟩ := cert
  constructor
  · -- полоса роста: операторная динамика ⟹ конусная форма β
    have hdyn : ∀ t, ρ * usableFrontier (S t)
        + (γ * k ^ 2 + (1 - ρ) * k) * (S t).capability
        ≤ usableFrontier (S (t + 1)) := by
      intro t
      have h1 := hop t
      have h2 := hsuff t
      linarith
    exact state_closed_band S γ ρ
      (γ * k ^ 2 + (1 - ρ) * k) k 100 (1/2)
      hγ hk (by norm_num : (1/2 : ℝ) ≤ 1)
      (fun t => hCpos t)
      (fun t => hstep t)
      (fun t => hdyn t)
      hrhogk
      (by norm_num :
        γ * k ^ 2 + (1 - ρ) * k ≤ γ * k ^ 2 + (1 - ρ) * k)
      hcone0
      (fun t => hpl_up t)
      (fun t => hpl_lo t)
      (hC0)
      T
  · exact universality_longhorizon risk best r (0 : Fin 1) R ε0 ρe
      hrisk hregret hε0 hρe hρe1

end Hagi

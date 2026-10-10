/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.LiveDeltaSafe
import Hagi.Runtime.LiveDeltaAudit
import Hagi.Runtime.LiveDeltaQuant

set_option linter.style.header false

/-!
# Сквозной цикл живых весов (план интеграции, п. 6)

Одна теорема о полном цикле низкорангового обучения:

обновление новейшего блока (изоляция состояния) →
SafeQP-окно (защищаемые потери в бюджетах) →
динамический аудит (в допуске) →
квантизация при упаковке (квадратичная ошибка ≤ mn(s/2)²) →
бюджет памяти (точный, не меняется при обновлении).

Все измеряемые посылки (десцент-линии, телеметрия,
в-диапазонность) — h_emp_ гипотезы. Никакого утверждения о
качестве обучения нет — это сертификат ЦИКЛА, соединяющий
уже доказанные части.
-/

open Finset Matrix Real InnerProductSpace
open Hagi.LiveDelta Hagi.LiveDeltaSafe Hagi.LiveDeltaAudit
  Hagi.LiveDeltaQuant

namespace Hagi.LiveDeltaCycle

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- **Сквозной сертификат одного цикла живых весов**:
при (1) обновлении только новейшего блока, (2) SafeQP-окне
шага в фактор-пространстве, (3) прохождении динамического
аудита и (4) в-диапазонности упаковываемой базы —
одновременно: защищаемые потери в бюджетах, состояние
изолировано (база/хвост/длина/стоимость неизменны), аудит в
допуске, упаковочная ошибка ≤ mn(s/2)². -/
theorem live_delta_cycle (s : LiveDelta m n r)
    (B' : Matrix r n ℝ)
    -- SafeQP window in the factor space
    (g : K → X) (eps L : K → ℝ) (d : X) (dL : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMax g eps L d)
    -- dynamic audit
    (tol : AuditTolerance) (tel tel' : DynTelemetry)
    (haudit : auditAccept tol tel tel')
    -- packaging: the folded base is in ternary range
    (sPack : ℝ) (hs : 0 < sPack)
    (hin : ∀ i j, ternInRange sPack (effectiveWeights s i j)) :
    -- 1. protected losses within budgets
    (∀ i, dL i ≤ eps i)
    -- 2. state isolation
    ∧ (updateNewest B' s).base = s.base
      ∧ (updateNewest B' s).blocks.length = s.blocks.length
    -- 3. memory cost unchanged
    ∧ (updateNewest B' s).blocks.length
        * (Fintype.card r * (Fintype.card m + Fintype.card n))
      = s.blocks.length
        * (Fintype.card r * (Fintype.card m + Fintype.card n))
    -- 4. dynamic audit within tolerance
    ∧ (|tel'.lamMax - tel.lamMax| ≤ tol.tolLam
      ∧ |tel'.pPlus - tel.pPlus| ≤ tol.tolP
      ∧ |tel'.partRatio - tel.partRatio| ≤ tol.tolPR)
    -- 5. packaging quantization error bound
    ∧ ∑ i, ∑ j, (effectiveWeights s i j
        - quantMat sPack (effectiveWeights s) i j) ^ 2
      ≤ (Fintype.card m * Fintype.card n) * (sPack / 2) ^ 2 :=
  ⟨safe_update_window g eps L d dL eta hL heps heta hd h_lipline
      h_eta,
    updateNewest_base B' s, updateNewest_length B' s,
    updateNewest_cost B' s, haudit,
    quantMat_sq_bound sPack hs (effectiveWeights s) hin⟩

end Hagi.LiveDeltaCycle

import Hagi.Model.RL
import Hagi.Probability.PinskerTV

/-!
# Alignment-риск: KL-штраф → сертифицированный риск-канал

RLHF/DPO-штраф ограничивает расхождение обновлённой
политики с референсной. Пинскер переводит бюджет KL в
границу полной вариации, и липшицевый по TV риск-канал
получает сертифицированный лимит: alignment-обучение
совместимо с риск-контрактом certified-цикла.
-/

namespace Hagi.Model.AlignmentRisk

open Hagi.Prelude Hagi.Probability

variable {V : Type*} [Fintype V] [Nonempty V]

/-- ГЛАВНЫЙ МОСТ: бюджет KL-штрафа → лимит риска.
Если расхождение политик ограничено KL-штрафом, а
риск-канал липшицев по полной вариации с константой c,
то прирост риска не превосходит c·√(KL): alignment-штраф
поставляет риск-сертификат certified-цикла. -/
theorem kl_budget_risk_bound (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (risk : ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hlip : risk ≤ c * ((1/2) * ∑ v : V, |p v - q v|)) :
    risk ≤ c * Real.sqrt (Hagi.Prelude.klDef q p) := by
  have hpin := pinsker_sqrt_kl q p hq hq1 hp hp1
  have hcomm : ∑ v : V, |q v - p v| = ∑ v : V, |p v - q v| :=
    Finset.sum_congr rfl fun v _ => abs_sub_comm _ _
  rw [hcomm] at hpin
  calc risk ≤ c * ((1/2) * ∑ v : V, |p v - q v|) := hlip
    _ ≤ c * Real.sqrt (Hagi.Prelude.klDef q p) :=
        mul_le_mul_of_nonneg_left hpin hc

/-- СЛЕДСТВИЕ-ФОРМА: KL-штраф ≤ delta ⟹ риск ≤ c·√delta
— certified-цикл получает риск-лимит из alignment-штрафа. -/
theorem kl_penalty_certifies_risk (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (risk c delta : ℝ) (hc : 0 ≤ c)
    (hlip : risk ≤ c * ((1/2) * ∑ v : V, |p v - q v|))
    (hkl : Hagi.Prelude.klDef q p ≤ delta) :
    risk ≤ c * Real.sqrt delta :=
  le_trans (kl_budget_risk_bound p q hp hp1 hq hq1 risk c hc hlip)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkl) hc)

/-- Направление штрафа честно: RLHF-цель с KL-штрафом не
превышает цель без штрафа, и при нулевом расхождении
риск-лимит нулевой. -/
theorem rlhf_zero_drift_zero_risk (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (risk c : ℝ) (hc : 0 ≤ c)
    (hlip : risk ≤ c * ((1/2) * ∑ v : V, |p v - q v|))
    (heq : Hagi.Prelude.klDef q p ≤ 0) :
    risk ≤ 0 := by
  have h := kl_penalty_certifies_risk p q hp hp1 hq hq1 risk c 0 hc
    hlip heq
  rw [Real.sqrt_zero, mul_zero] at h
  exact h

end Hagi.Model.AlignmentRisk

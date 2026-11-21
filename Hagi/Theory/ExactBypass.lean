/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# ExactBypass — нулевой CE символьного bypass на PROVEN_EXACT-покрытии (C541)

Внешний план C537 (mapping, P8, top-4): HAGI_v2 Exact-First
Residual Coupling — детерминированные паттерны перехватываются
символьными экспертами с сертификатом PROVEN_EXACT (0 нейронных
FLOP на покрытых позициях), остаток — нейронным ядром
(z_joint = z_core + Σ g·α·φ; связанные модули Unified/DerivAlong,
`CECoupledShortcut`). Этот модуль — теорема корректности в
вероятностной семантике: если предсказатель ставит вероятность
1 на истинный байт, точечный log-loss равен −ln 1 = 0 РОВНО,
суммарный CE-вклад покрытия нулевой, и общий CE
разлагается линейно: CE_total = 0 + CE_residual (позиции
независимы — обоснование GapBuffer-архитектуры).

Модель (честная, KISS):

* позиция `x : ι` абстрактна; `p x : ℝ` — вероятность,
  назначенная истинному байту (ВХОД модели; калибровка p и
  способ её получения из символьного сертификата не
  утверждаются);
* `cePoint p = -Real.log p` — точечный log-loss. `Real.log`
  на p ≤ 0 даёт junk-значение, поэтому нулевой CE утверждается
  ТОЛЬКО при p = 1, а ошибочное покрытие (p = 0 на истинном
  байте) закрывается отрицанием гейта: сертификат отвергается,
  «CE = −ln 0» физически не вычисляется;
* покрытие — явный список позиций `xs : List ι` (конечность
  структурная).

Не утверждается: скорость исполнения, калибровка, агрегация
байтов внутри одной позиции (это делает канонический
`Hagi.Core.ceOneHot`, мост ниже), общность на непокрытых
позициях.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.ExactBypass

variable {ι : Type}

/-- Pointwise log-loss: `-log p`, where `p` is the probability
assigned to the true byte. -/
noncomputable def cePoint (p : ℝ) : ℝ := -Real.log p

/-- Total CE over a finite list of positions (bits independent:
sum, not a joint normalizer). -/
noncomputable def ceSum (p : ι → ℝ) (xs : List ι) : ℝ :=
  (xs.map fun x => cePoint (p x)).sum

/-- The honest PROVEN_EXACT gate: coverage is certified only
when probability 1 is assigned to the true byte at every
covered position. -/
def ExactGate (p : ι → ℝ) (xs : List ι) : Prop := ∀ x ∈ xs, p x = 1

/-- Core of P8: a predictor placing probability 1 on the true
byte has pointwise CE exactly `-ln 1 = 0`. -/
theorem ce_pointwise_of_prob_one (p : ℝ) (h : p = 1) :
    cePoint p = 0 := by
  rw [h, cePoint, Real.log_one, neg_zero]

/-- The total CE contribution of the PROVEN_EXACT coverage is
exactly zero. -/
theorem ce_covered_zero (p : ι → ℝ) (xs : List ι)
    (h : ∀ x ∈ xs, p x = 1) : ceSum p xs = 0 := by
  unfold ceSum
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hv
  rw [← hxe, h x hx]
  exact ce_pointwise_of_prob_one 1 rfl

/-- Linearity over positions (independent bits): CE is additive
along the split of the sequence. -/
theorem ce_split (p : ι → ℝ) (xs ys : List ι) :
    ceSum p (xs ++ ys) = ceSum p xs + ceSum p ys := by
  unfold ceSum
  rw [List.map_append, List.sum_append]

/-- Linear decomposition of the plan: on a mixed sequence
(covered positions with p = 1, then residual positions) the
total CE equals the residual CE alone — the covered share
contributes exactly zero. -/
theorem ce_total_eq_residual (p : ι → ℝ) (cov res : List ι)
    (h : ∀ x ∈ cov, p x = 1) :
    ceSum p (cov ++ res) = ceSum p res := by
  rw [ce_split, ce_covered_zero p cov h, zero_add]

/-- Gate soundness: a certified coverage contributes exactly
zero CE. -/
theorem exact_gate_sound (p : ι → ℝ) (xs : List ι)
    (h : ExactGate p xs) : ceSum p xs = 0 :=
  ce_covered_zero p xs h

/-- The gate rejects mistaken coverage: probability 0 on the
true byte at a covered position forbids the PROVEN_EXACT
certificate (infinite log-loss is a rejected certificate, not
a computed value). -/
theorem exact_gate_rejects_zero (p : ι → ℝ) (xs : List ι) (x₀ : ι)
    (hx₀ : x₀ ∈ xs) (hz : p x₀ = 0) : ¬ ExactGate p xs := fun h =>
  zero_ne_one (hz ▸ h x₀ hx₀)

/-- Bridge to the canonical CE SSOT (logit semantics): if the
canonical softmax probability of the true byte is exactly 1,
then the canonical `Hagi.Core.ceOneHot` at that position is
exactly zero.  Composition with the Unified/DerivAlong and
`CECoupledShortcut` modules goes through this common SSOT; their
types are not duplicated here. -/
theorem ceOneHot_eq_zero_of_softmaxP_eq_one {k : Type} [Fintype k]
    [Nonempty k] (z : k → ℝ) (t : k)
    (h : Hagi.Core.softmaxP z t = 1) : Hagi.Core.ceOneHot t z = 0 := by
  have hpos : 0 < ∑ v, Real.exp (z v) := Hagi.Core.exp_sum_pos z
  have hsum : ∑ v, Real.exp (z v) = Real.exp (z t) := by
    simp only [Hagi.Core.softmaxP, Hagi.Prelude.softDef] at h
    rw [div_eq_one_iff_eq hpos.ne'] at h
    exact h.symm
  show Hagi.Core.lse z - z t = 0
  unfold Hagi.Core.lse
  rw [hsum, Real.log_exp, sub_self]

end Hagi.Theory.ExactBypass

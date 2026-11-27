/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Unified.CertifiedLoop
import Hagi.Probability.PairedGain
import Hagi.Optimization.MuonDual

/-!
# CertifiedStepCompose — end-to-end сертификат составного шага PrimeCertTrain

Шаг `train_optimal`: кандидат `s'` строится из несмещённой importance-оценки
градиента с маскированием (`ResidualMasking.masked_importance_unbiased`,
`covered_window_propensity_zero`), полярного шага Muon под guard'ами
(`MuonDual.guards_sound`) и сертифицированного `η`; затем EB-gate на holdout
окнах решает: принять `s'` или держать `s` (откат).

* `gate D sig b α n g₀ ω` — `mean D − radius > g₀` на окнах `ω`;
* `composedStep` — `s'` при прошедшем gate, иначе `s`;
* `composed_never_increases` — детерминированная часть: если сертификат шага
  связывает gate с истинным улучшением, объект не растёт ни при каком `ω`,
  как бы ни был построен `s'`;
* `composed_gate_false_le` — вероятностная часть: при нулевой гипотезе gate
  проходит с вероятностью `≤ α` (`admit_false_le`).

Вместе: ложный приём ограничен `α`, истинный — улучшает, иначе hold.
-/

namespace Hagi.Unified.CertifiedStepCompose
open Hagi.Probability Hagi.Probability.PairedGain
open scoped Classical

variable {V : Type} [Fintype V] [Nonempty V] {S : Type}
/-- EB-gate на holdout-окнах `ω`: наблюдаемый выигрыш превышает радиус на `g₀`. -/
noncomputable def gate (D : V → ℝ) (sig b α : ℝ) (n : ℕ) (g₀ : ℝ) (ω : Fin n → V) : Prop :=
  (∑ i, D (ω i)) / n - radius sig b n α > g₀
/-- Составной шаг: при прошедшем gate — кандидат `s'`, иначе hold (`s`). -/
noncomputable def composedStep (D : V → ℝ) (sig b α : ℝ) (n : ℕ) (g₀ : ℝ)
    (s s' : S) (ω : Fin n → V) : S := if gate D sig b α n g₀ ω then s' else s
omit [Fintype V] [Nonempty V] in
/-- End-to-end (детерминированная часть): если сертификат шага связывает gate
с истинным улучшением, объект после составного шага не растёт ни при каком `ω`
— независимо от того, как построен `s'` (importance-оценка, маскирование,
полярный шаг с guard'ами). -/
theorem composed_never_increases (obj : S → ℝ) (D : V → ℝ) (sig b α : ℝ) (n : ℕ)
    (g₀ : ℝ) (s s' : S) (ω : Fin n → V)
    (hcert : gate D sig b α n g₀ ω → obj s' ≤ obj s) :
    obj (composedStep D sig b α n g₀ s s' ω) ≤ obj s := by
  unfold composedStep
  exact CertifiedLoop.gate_never_increases obj (gate D sig b α n g₀ ω) s s' hcert
/-- Вероятностная часть: при нулевой гипотезе gate проходит с вероятностью
`≤ α` (`admit_false_le` в форме дополнения) — ложный проход gate ограничен. -/
theorem composed_gate_false_le (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : V → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |D v| ≤ b)
    (sig : ℝ) (hsig : 0 < sig) (hmean : ∑ v, q v * D v = 0)
    (hvar : ∑ v, q v * D v ^ 2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hα2 : α < 1) (g₀ : ℝ) (hg₀ : 0 ≤ g₀) :
    prodPq (fun _ : Fin n => q) (fun ω => gate D sig b α n g₀ ω) ≤ α := by
  have h := admit_false_le q hq0 hq1 D b hb hbnd sig hsig hmean hvar n hn α hα hα2 g₀ hg₀
  have hcomp := prodPq_compl (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩)
    (fun ω => gate D sig b α n g₀ ω)
  unfold gate at hcomp ⊢
  have h' : prodPq (fun _ : Fin n => q) (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀))
      ≥ 1 - α := h
  rw [hcomp] at h'
  linarith

end Hagi.Unified.CertifiedStepCompose

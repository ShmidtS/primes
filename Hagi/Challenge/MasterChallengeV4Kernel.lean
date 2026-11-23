import Hagi.Unified.CertifiedLoop

/-!
# Comparator-Challenge v4 (kernel-form): CertifiedLoopKernel

Ядерная форма challenge-методологии openai/math Comparator: та же
дисциплина, что у `master_hagi_challenge_v3` (заключение прописано
ПОЛНОСТЬЮ, посылки — только сертифицированная цепь), но носитель —
ОБЩЕЕ ЯДРО `Hagi.Cert.CertStepGenBounded` (A14 QW5):
`TaskId` произвольный (жёсткий `Fin 5` legacy-цикла — инстанциация
потребителя, не ограничение), bounded-законы списания (≤).
Допустимые аксиомы: ровно propext, Classical.choice, Quot.sound.

Scope: спуск Σdrops ≤ obj₀ − objₙ, ядерный FloorsKept на конце,
0 ≤ budget n, бюджетный телескоп, риск-леджер Σrisks ≤ risk₀,
δ-леджер Σdeltas ≤ δ₀ — всё из одной bounded-цепи ядра.
-/

namespace Hagi.Challenge

open Hagi.Cert Hagi.Unified.CertifiedLoopKernel

/-- Comparator-формулировка v4 (kernel-form): заключение ядерного
капстона прописано полностью; посылки — только bounded-цепь ядра.
Доказательство делегирует `certified_loop_kernel`; при расхождении
формулировок файл не скомпилируется. -/
theorem master_hagi_challenge_v4_kernel {S TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    {deltaLevel : S → ℝ}
    (n : ℕ) (t : ℕ → S)
    (hfloor0 : FloorsKept M obl (t 0)) (hb0 : 0 ≤ M.budget (t 0))
    (hrisk0 : 0 ≤ M.risk (t 0)) (hdelta0 : 0 ≤ deltaLevel (t 0))
    (steps : ∀ j : Fin n, CertStepGenBounded M obl deltaLevel
      (t j.val) (t (j.val + 1)))
    (drops spends risks deltas : ℕ → ℝ)
    (hdrops : ∀ j : Fin n, drops j.val = (steps j).drop)
    (hspends : ∀ j : Fin n, spends j.val = (steps j).budgetSpend)
    (hrisks : ∀ j : Fin n, risks j.val = (steps j).riskSpend)
    (hdeltas : ∀ j : Fin n, deltas j.val = (steps j).delta) :
    -- ЗАКЛЮЧЕНИЕ (прописано, не делегировано):
    ∑ j ∈ Finset.range n, drops j ≤ M.objective (t 0) - M.objective (t n)
      ∧ FloorsKept M obl (t n)
      ∧ 0 ≤ M.budget (t n)
      ∧ M.budget (t n) ≤ M.budget (t 0) - ∑ j ∈ Finset.range n, spends j
      ∧ ∑ j ∈ Finset.range n, risks j ≤ M.risk (t 0)
      ∧ ∑ j ∈ Finset.range n, deltas j ≤ deltaLevel (t 0) :=
  certified_loop_kernel M obl n t hfloor0 hb0 hrisk0 hdelta0
    steps drops spends risks deltas hdrops hspends hrisks hdeltas

end Hagi.Challenge

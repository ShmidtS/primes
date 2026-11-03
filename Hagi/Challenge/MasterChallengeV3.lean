import Hagi.Unified.CertifiedLoop

/-!
# Comparator-Challenge v3: CertifiedLoop (Gen-3)

Методология openai/math Comparator: ЧЕСТНАЯ формулировка
закреплена в отдельном challenge-файле. Заключение прописано
ПОЛНОСТЬЮ (не делегировано): любое изменение смысла
`certified_loop_strict` (усиление посылок, ослабление
заключения) ломает тип делегирующего доказательства —
challenge падает в сборке. Посылки — ТОЛЬКО StepCert-цепочка
(честный спуск + покомпонентный floor + честный бюджет);
Gen-1 контракты (CorePremises, GenState, копируемые effects)
НЕ используются. Допустимые аксиомы: ровно propext,
Classical.choice, Quot.sound.

Scope (что закреплено): главный Gen-3 результат — строгий
спуск Σdrops ≤ obj₀ − objₙ (при n ≥ 1 строго objₙ < obj₀),
покомпонентное качество FloorKept на финальном состоянии и
точная бюджетная бухгалтерия bₙ ≤ b₀ − Σspends, 0 ≤ bₙ.
-/

namespace Hagi.Challenge

open Hagi.Unified.CertifiedLoop Hagi.Unified.LinkedQVec

/-- Comparator-формулировка v3: заключение certified_loop
прописано полностью; посылки — только StepCert-цепочка.
Доказательство делегирует certified_loop_strict /
certified_loop: при расхождении формулировок файл не
скомпилируется. -/
theorem master_hagi_challenge_v3 {S : Type*}
    (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop)
    (hspends : ∀ t : Fin n, spends t.val = (certs t).budgetSpend)
    (hn : 1 ≤ n) :
    -- ЗАКЛЮЧЕНИЕ (прописано, не делегировано):
    obj (f n) < obj (f 0)
      ∧ ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n)
      ∧ FloorKept M (f n) floor
      ∧ 0 ≤ b n
      ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, spends t := by
  obtain ⟨hstrict, hsum⟩ :=
    certified_loop_strict obj M floor riskLim f b drops n h₀ hb₀
      certs hdrops hn
  obtain ⟨_, hq, hbnn, hbtel⟩ :=
    certified_loop obj M floor riskLim f b drops spends n h₀ hb₀
      certs hdrops hspends
  exact ⟨hstrict, hsum, hq, hbnn, hbtel⟩

end Hagi.Challenge

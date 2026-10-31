import Mathlib

/-!
# StepContract — единый моноид сертификатов шага (аудит v15 §4.3)

Замена зоопарка из 21 структуры-сертификата одним контрактом:
`(decrease, riskCost, budgetSpend)` с неотрицательностью и
композицией-моноидом. Единая телескопическая теорема
`trajectory_convergence` заменяет ~2000 строк шаблонного
телескопирования в System/Unified/Model.

Ключевая честность: `decrease` — ДОКАЗАННОЕ падение потенциала
(не измеренное значение); любые эмпирические допущения живут в
гипотезах потребителей, не внутри контракта.
-/

namespace Hagi.Unified.StepCert

/-- Единый сертификат шага: доказанное падение + риски + бюджет. -/
structure StepContract where
  /-- Доказанное гарантированное падение потенциала. -/
  decrease : ℝ
  /-- Накопленный риск (нарушение защищаемых ограничений). -/
  riskCost : ℝ
  /-- Израсходованный бюджет (FLOPs/токены/биты — по контексту). -/
  budgetSpend : ℝ
  hDecreasePos : 0 ≤ decrease
  hRiskNonneg : 0 ≤ riskCost
  hBudgetNonneg : 0 ≤ budgetSpend

/-- Тождественный контракт (нейтральный элемент моноида). -/
def unit : StepContract where
  decrease := 0
  riskCost := 0
  budgetSpend := 0
  hDecreasePos := le_refl 0
  hRiskNonneg := le_refl 0
  hBudgetNonneg := le_refl 0

/-- Композиция: последовательное выполнение фаз ( associativity
по rfl, нейтраль `id` по rfl — истинный моноид, без
координатной путаницы risk/cost). -/
def compose (c1 c2 : StepContract) : StepContract where
  decrease := c1.decrease + c2.decrease
  riskCost := c1.riskCost + c2.riskCost
  budgetSpend := c1.budgetSpend + c2.budgetSpend
  hDecreasePos := add_nonneg c1.hDecreasePos c2.hDecreasePos
  hRiskNonneg := add_nonneg c1.hRiskNonneg c2.hRiskNonneg
  hBudgetNonneg := add_nonneg c1.hBudgetNonneg c2.hBudgetNonneg

theorem compose_assoc (c1 c2 c3 : StepContract) :
    compose (compose c1 c2) c3 = compose c1 (compose c2 c3) := by
  simp [compose, add_assoc]

theorem compose_id_left (c : StepContract) :
    compose unit c = c := by
  simp [compose, unit]

theorem compose_id_right (c : StepContract) :
    compose c unit = c := by
  simp [compose, unit]

instance : Zero StepContract := ⟨unit⟩

/-- Суммарный контракт цепочки шагов (свёртка по моноиду). -/
def chain {T : ℕ} (cs : Fin T → StepContract) : StepContract :=
  (List.map cs (List.finRange T)).foldr compose unit

theorem chain_decrease {T : ℕ} (cs : Fin T → StepContract) :
    (chain cs).decrease = ∑ t : Fin T, (cs t).decrease := by
  induction T with
  | zero => simp [chain, unit]
  | succ T ih =>
      have hfr : List.finRange (T+1) = 0 :: List.map Fin.succ (List.finRange T) := by
        simp [List.finRange_succ]
      rw [chain, hfr, List.map_cons, List.foldr_cons, Fin.sum_univ_succ]
      have h := ih (fun t => cs t.succ)
      simp only [chain] at h
      simp only [compose]
      rw [List.map_map]
      exact congrArg (fun x => (cs 0).decrease + x) h

/-- Бюджетная теорема: суммарный расход — сумма расходов. -/
theorem chain_budget {T : ℕ} (cs : Fin T → StepContract) :
    (chain cs).budgetSpend = ∑ t : Fin T, (cs t).budgetSpend := by
  induction T with
  | zero => simp [chain, unit]
  | succ T ih =>
      have hfr : List.finRange (T+1) = 0 :: List.map Fin.succ (List.finRange T) := by
        simp [List.finRange_succ]
      rw [chain, hfr, List.map_cons, List.foldr_cons, Fin.sum_univ_succ]
      have h := ih (fun t => cs t.succ)
      simp only [chain] at h
      simp only [compose]
      rw [List.map_map]
      exact congrArg (fun x => (cs 0).budgetSpend + x) h

/-- Риск цепочки — сумма рисков. -/
theorem chain_risk {T : ℕ} (cs : Fin T → StepContract) :
    (chain cs).riskCost = ∑ t : Fin T, (cs t).riskCost := by
  induction T with
  | zero => simp [chain, unit]
  | succ T ih =>
      have hfr : List.finRange (T+1) = 0 :: List.map Fin.succ (List.finRange T) := by
        simp [List.finRange_succ]
      rw [chain, hfr, List.map_cons, List.foldr_cons, Fin.sum_univ_succ]
      have h := ih (fun t => cs t.succ)
      simp only [chain] at h
      simp only [compose]
      rw [List.map_map]
      exact congrArg (fun x => (cs 0).riskCost + x) h

/-- ЕДИНАЯ ТЕЛЕСКОПИЧЕСКАЯ ТЕОРЕМА: если потенциал Φ на каждом
шаге падает на доказанное `decrease` с точностью до
`riskCost`, и Φ ограничен снизу на всей траектории, то
суммарное доказанное падение ≤ Φ₀ − Φ_min + суммарный риск. -/
theorem trajectory_convergence {T : ℕ}
    (cs : Fin T → StepContract)
    (Φ : ℕ → ℝ) (Φ_min : ℝ)
    (h_step : ∀ t : Fin T,
      Φ (t.val + 1) ≤ Φ t.val - (cs t).decrease + (cs t).riskCost)
    (h_floor : ∀ t ≤ T, Φ_min ≤ Φ t) :
    ∑ t : Fin T, (cs t).decrease
      ≤ Φ 0 - Φ_min + ∑ t : Fin T, (cs t).riskCost := by
  -- телескопическое неравенство по индукции
  have key : ∀ T : ℕ, ∀ cs : Fin T → StepContract,
      (∀ t : Fin T, Φ (t.val + 1) ≤ Φ t.val - (cs t).decrease + (cs t).riskCost) →
      (∀ t ≤ T, Φ_min ≤ Φ t) →
      Φ T ≤ Φ 0 - ∑ t : Fin T, (cs t).decrease + ∑ t : Fin T, (cs t).riskCost := by
    intro T
    induction T with
    | zero => intro cs _ _; simp
    | succ T ih =>
        intro cs hs hf
        have hlast := hs ⟨T, Nat.lt_succ_self T⟩
        have hprev := ih (fun t => cs t.castSucc)
          (fun t => hs ⟨t.val, by omega⟩)
          (fun t ht => hf t (by omega))
        have hD : ∑ t : Fin (T+1), (cs t).decrease
            = ∑ t : Fin T, (cs t.castSucc).decrease + (cs (Fin.last T)).decrease :=
          Fin.sum_univ_castSucc _
        have hR : ∑ t : Fin (T+1), (cs t).riskCost
            = ∑ t : Fin T, (cs t.castSucc).riskCost + (cs (Fin.last T)).riskCost :=
          Fin.sum_univ_castSucc _
        have hlast' : Φ (T+1) ≤ Φ T - (cs (Fin.last T)).decrease
            + (cs (Fin.last T)).riskCost := hlast
        have hfT := hf T (by omega)
        have hf0 := hf 0 (by omega)
        linarith
  have hkey := key T cs h_step h_floor
  have hfloor := h_floor T (le_refl T)
  linarith

end Hagi.Unified.StepCert

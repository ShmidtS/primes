import Mathlib.Tactic
import Hagi.Unified.HonestTransition
import Hagi.Unified.LinkedQVec
import Hagi.Unified.CanonicalParams

/-!
# CertifiedLoop — КАПСТОН: единый замкнутый цикл обучения

Интегрирует все сертифицированные компоненты серии аудита
в одну теорему верхнего уровня:

- `CanonicalParams` : params — единственный носитель;
- `HonestTransition` : спуск доказан зависимо от
  исполнения, а не «положительность показателя»;
- `MeasuredState`/`FloorKept` : качество — функция
  состояния, покомпонентный floor;
- бюджет: невозрастание и неотрицательность.

`certified_loop` — ГЛАВНАЯ ТЕОРЕМА: конечная цепочка
сертифицированных шагов даёт одновременно
1. кумулятивный РЕАЛЬНЫЙ спуск ≥ суммы сертификатов;
2. покомпонентное качество на всей цепочке;
3. неотрицательный остаточный бюджет;
4. телескоп бюджета: bₙ ≤ b₀ − Σ spends.

`gate_never_increases` — принцип commit/hold: без
сертификата состояние сохраняется; энергия не растёт
НИКОГДА. Это доказанный безопасный anytime-цикл HAGI.
-/

namespace Hagi.Unified.CertifiedLoop

open Hagi.Unified.HonestTransition Hagi.Unified.LinkedQVec

variable {S : Type*}

/-- Один шаг цикла: честный переход + качество + бюджет.
Связность с траекторией (f, b) заложена в типе индексации. -/
structure StepCert (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (s s' : S) (bt b' : ℝ) where
  /-- Риск-трата шага (НЕЗАВИСИМЫЙ канал: риск ≠ бюджет,
  spec P0-3.2 — запрет отождествления risk и compute cost). -/
  riskSpend : ℝ
  /-- Бюджетная (вычислительная) трата шага. -/
  budgetSpend : ℝ
  /-- Честный переход: спуск зависим от исполнения;
  риск-канал — riskSpend. -/
  trans : HonestTransition obj s s' riskSpend riskLim budgetSpend b'
  /-- Риск-трата неотрицательна. -/
  hriskSpend_nn : 0 ≤ riskSpend
  /-- Бюджетная трата неотрицательна. -/
  hbudgetSpend_nn : 0 ≤ budgetSpend
  /-- Бюджет невозрастает с учётом БЮДЖЕТНОЙ траты. -/
  hdec : b' ≤ bt - budgetSpend
  /-- Покомпонентное качество сохранено. -/
  quality : FloorKept M s' floor

/-- Главная теорема: сертифицированная цепочка шагов
даёт одновременно реальный спуск, качество, бюджет. -/
theorem certified_loop (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop)
    (hspends : ∀ t : Fin n,
      spends t.val = (certs t).budgetSpend) :
    ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n)
      ∧ FloorKept M (f n) floor
      ∧ 0 ≤ b n
      ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, spends t := by
  revert certs hdrops hspends
  induction n with
  | zero => intro _ _; simp [h₀, hb₀]
  | succ n ih =>
    intro certs hdrops hspends
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hdrop := (certs (Fin.last n)).trans.actualDescent
    have hpos := (certs (Fin.last n)).trans.objectiveDrop_pos
    have hbd := (certs (Fin.last n)).hdec
    have hbb := (certs (Fin.last n)).trans.budgetBound
    have hq := (certs (Fin.last n)).quality
    have hn1 : drops n = (certs (Fin.last n)).trans.objectiveDrop :=
      hdrops (Fin.last n)
    have hn1' : drops n = (certs (Fin.last n)).trans.objectiveDrop :=
      hn1
    have hn2 : spends n = (certs (Fin.last n)).budgetSpend :=
      hspends (Fin.last n)
    have hn2' : spends n = (certs (Fin.last n)).budgetSpend :=
      hn2
    obtain ⟨h1, h2, h3, h4⟩ := ih
      (fun t => certs t.castSucc)
      (fun t => hdrops t.castSucc)
      (fun t => hspends t.castSucc)
    have hdrop2 : obj (f (n + 1))
        ≤ obj (f n) - (certs (Fin.last n)).trans.objectiveDrop :=
      hdrop
    have hbb2 : 0 ≤ b (n + 1) := hbb
    have hbd2 : b (n + 1) ≤ b n - (certs (Fin.last n)).budgetSpend := hbd
    have hq2 : FloorKept M (f (n + 1)) floor := hq
    refine ⟨?_, hq2, hbb2, ?_⟩ <;> linarith

/-- Усиление: покомпонентный floor держится на ВСЕХ
промежуточных состояниях цепочки, не только в конце. -/
theorem certified_loop_all (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop)
    (hspends : ∀ t : Fin n,
      spends t.val = (certs t).budgetSpend) :
    ∀ t ≤ n, FloorKept M (f t) floor := by
  intro t ht
  induction n generalizing t with
  | zero =>
    have : t = 0 := Nat.le_zero.mp ht
    subst this
    exact h₀
  | succ n ih =>
    match t, ht with
    | 0, _ => exact h₀
    | t + 1, ht =>
      have hcert := certs (Fin.last n)
      have hstep : FloorKept M (f (n + 1)) floor :=
        hcert.quality
      match Nat.lt_or_ge t n with
      | .inr heq =>
        have hn : t = n := by omega
        subst hn
        exact hstep
      | .inl hlt =>
        exact ih (fun t' => certs t'.castSucc)
          (fun t' => hdrops t'.castSucc)
          (fun t' => hspends t'.castSucc) (t + 1) (by omega)

/-- Принцип commit/hold: без сертификата — hold,
состояние сохраняется. Энергия не растёт НИКОГДА. -/
theorem gate_never_increases (obj : S → ℝ) (P : Prop) [Decidable P]
    (s s' : S) (h : P → obj s' ≤ obj s) :
    obj (if P then s' else s) ≤ obj s := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

/-- УСИЛЕНИЕ: при n ≥ 1 спуск СТРОГИЙ — сертифицированная
цепочка хотя бы одного шага гарантированно улучшает.
(spends вычисляются из сертификатов внутри — вызывающей
стороне не нужно их передавать.) -/
theorem certified_loop_strict (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop)
    (hn : 1 ≤ n) :
    obj (f n) < obj (f 0) ∧
      ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n) := by
  set spends : ℕ → ℝ :=
    fun t => if h : t < n then (certs ⟨t, h⟩).budgetSpend else 0 with hsp_def
  have hspends : ∀ t (ht : t < n),
      spends t = (certs ⟨t, ht⟩).budgetSpend := by
    intro t ht
    rw [hsp_def]
    simp only [dif_pos ht]
  obtain ⟨h1, h2, h3, h4⟩ := certified_loop obj M floor riskLim f b
    drops spends n h₀ hb₀ certs hdrops (fun t => hspends t.val t.isLt)
  have hsum : 0 < ∑ t ∈ Finset.range n, drops t :=
    Finset.sum_pos
      (fun t ht => by
        have ht' := Finset.mem_range.mp ht
        have he := hdrops ⟨t, ht'⟩
        have hp := (certs ⟨t, ht'⟩).trans.objectiveDrop_pos
        linarith)
      ⟨0, Finset.mem_range.mpr hn⟩
  exact ⟨by linarith, h1⟩


/-! ### Риск-агрегация (цикл 34, аудит #8 п.9 +Risk) -/

/-- ПЕРВАЯ ТЕОРЕМА НАКОПЛЕННОГО РИСКА: сертифицированная
цепочка из n шагов накапливает риск НЕ БОЛЕЕ n·riskLim —
индивидуальные riskBound каждого шага агрегируются в
глобальный лимит. Риск-канал сертификатов теперь УЧАСТВУЕТ
в выводе цикла (аудит #8: «riskBound в выводе certified_loop
не участвует вообще» — закрыто). -/
theorem certified_loop_risk (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1))) :
    ∑ t : Fin n, (certs t).riskSpend ≤ (n : ℝ) * riskLim := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hlast : (certs (Fin.last m)).riskSpend ≤ riskLim :=
      (certs (Fin.last m)).trans.riskBound
    have hrest : ∑ t : Fin m, (certs ⟨t.val, by omega⟩).riskSpend
        ≤ (m : ℝ) * riskLim :=
      ih (fun t => certs ⟨t.val, by omega⟩)
    rw [Fin.sum_univ_castSucc]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hconv : ∑ t : Fin m, (certs t.castSucc).riskSpend
        = ∑ t : Fin m, (certs ⟨t.val, by omega⟩).riskSpend := by
      exact Finset.sum_congr rfl (fun (t : Fin m) (_ : t ∈ Finset.univ) => by
        have he : (t.castSucc : ℕ) = t.val := rfl
        rfl)
    rw [hconv]
    linarith

end Hagi.Unified.CertifiedLoop

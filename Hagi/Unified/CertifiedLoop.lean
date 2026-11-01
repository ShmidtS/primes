import Mathlib
import Hagi.Unified.HonestTransition
import Hagi.Unified.LinkedQVec
import Hagi.Unified.CanonicalParams

/-!
# CertifiedLoop — КАПСТОН: единый замкнутый цикл обучения

Интегрирует все сертифицированные компоненты серии аудита
в одну теорему верхнего уровня:

- `CanonicalParams` (P0-3): params — единственный носитель;
- `HonestTransition` (P0-2): спуск доказан зависимо от
  исполнения, а не «положительность показателя»;
- `MeasuredState`/`FloorKept` (P0-4): качество — функция
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
  /-- Затраты шага. -/
  spend : ℝ
  /-- Честный переход: спуск зависим от исполнения. -/
  trans : HonestTransition obj s s' spend riskLim spend b'
  /-- Бюджет невозрастает с учётом затрат. -/
  hdec : b' ≤ bt - spend
  /-- Покомпонентное качество сохранено. -/
  quality : FloorKept M s' floor

/-- ГЛАВНАЯ ТЕОРЕМА HAGI: сертифицированная цепочка шагов
даёт одновременно реальный спуск, качество, бюджет. -/
theorem certified_loop (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : ℕ,
      StepCert obj M floor riskLim (f t) (f (t + 1)) (b t) (b (t + 1)))
    (hdrops : ∀ t < n, drops t = (certs t).trans.objectiveDrop)
    (hspends : ∀ t < n, spends t = (certs t).spend) :
    ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n)
      ∧ FloorKept M (f n) floor
      ∧ 0 ≤ b n
      ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, spends t := by
  revert hdrops hspends
  induction n with
  | zero => intro _ _; simp [h₀, hb₀]
  | succ n ih =>
    intro hdrops hspends
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hdrop := (certs n).trans.actualDescent
    have hpos := (certs n).trans.objectiveDrop_pos
    have hbd := (certs n).hdec
    have hbb := (certs n).trans.budgetBound
    have hq := (certs n).quality
    have hn1 : drops n = (certs n).trans.objectiveDrop :=
      hdrops n (Nat.lt_succ_self n)
    have hn2 : spends n = (certs n).spend :=
      hspends n (Nat.lt_succ_self n)
    obtain ⟨h1, h2, h3, h4⟩ := ih
      (fun t ht => hdrops t (Nat.lt_succ_of_lt ht))
      (fun t ht => hspends t (Nat.lt_succ_of_lt ht))
    refine ⟨?_, hq, hbb, ?_⟩ <;> linarith

/-- Принцип commit/hold: без сертификата — hold,
состояние сохраняется. Энергия не растёт НИКОГДА. -/
theorem gate_never_increases (obj : S → ℝ) (P : Prop) [Decidable P]
    (s s' : S) (h : P → obj s' ≤ obj s) :
    obj (if P then s' else s) ≤ obj s := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

/-- УСИЛЕНИЕ: при n ≥ 1 спуск СТРОГИЙ — сертифицированная
цепочка хотя бы одного шага гарантированно улучшает. -/
theorem certified_loop_strict (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept M (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : ℕ,
      StepCert obj M floor riskLim (f t) (f (t + 1)) (b t) (b (t + 1)))
    (hdrops : ∀ t < n, drops t = (certs t).trans.objectiveDrop)
    (hspends : ∀ t < n, spends t = (certs t).spend)
    (hn : 1 ≤ n) :
    obj (f n) < obj (f 0) ∧
      ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n) := by
  obtain ⟨h1, h2, h3, h4⟩ := certified_loop obj M floor riskLim f b
    drops spends n h₀ hb₀ certs hdrops hspends
  have hsum : 0 < ∑ t ∈ Finset.range n, drops t :=
    Finset.sum_pos
      (fun t ht => by
        rw [hdrops t (Finset.mem_range.mp ht)]
        exact (certs t).trans.objectiveDrop_pos)
      (⟨0, by simp; omega⟩)
  exact ⟨by linarith, h1⟩

end Hagi.Unified.CertifiedLoop

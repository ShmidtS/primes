/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.GrowTrunkBlock

/-!
# GrowSnap — certified snap-политика при identity-grow (C521)

C506 измерил экспоненциальную стену повторяемого grow-цикла:
знаменатели дробей признаков растут ~×3.2 на grow-событие
(63 → 263 → 789 → 2366 цифр для глубин 2 → 5), глубина 6
проецировалась ~8000 цифр / ~150 s — честный вычислительный
предел Fraction-арифметики (не теоретический). C521 снимает
стену certified snap-политикой на КАЖДОЙ границе grow:

* веса обученного нового блока и признаки снапятся к
  рациональной сетке q/2^k (banker's rounding, детерминировано,
  per-value ошибка ≤ 2^-(k+1) — полуячейка);
* знаменатели на границе grow bounded 2^k — компаундинг
  начинается заново с k бит, а не с тысяч цифр прошлого grow
  (`snap_denominator_reset`: (q / 2^k : ℚ).den ≤ 2^k);
* деградация obj от снапа CERTIFIED, не предположительна:
  obj — линейная голова над признаками (per-point MSE
  (w·f − y)²), per-point bound
  |(s+ds−y)² − (s−y)²| ≤ (2|s−y| + |ds|)·|ds|, ds = w·δf
  вычислим ТОЧНО в Fraction — bench-форма per-block hLip
  premise (`CertifiedBlock` C436 / BlockLipschitz:
  композиция перемножает константы). Общая форма —
  `snap_preserves_objective_bound`;
* телескоп по циклу: если каждая фаза даёт
  obj_{i+1} ≤ obj_i + b_i (certified drop даёт вклад ≤ 0),
  то финал ≤ старт + Σ b_i — `grow_snap_cycle_sound`
  (индукция по списку bound'ов).

Cycle-соответствие: `scripts/bench_bridge.py --mode grow-snap`
исполняет ровно эту схему: C506 repeated grow (γ=0 identity,
EXACT obj-инвариант на каждом событии, certified fd-шаги
блока) + snap-фаза после обучения каждого блока; run-time
assert'ы: obj_after_snap ≤ obj_before + bound (bound ≥ факт),
знаменатели ≤ 2^k на каждой границе, telescoped
obj_final ≤ obj_cycle_start + Σ bounds.

## Honest pins (что этот мост НЕ покрывает)

- **Certified-шаги** — measured (drop > 0), как в C504/C506;
  snap-BOUND certified, но не монотонность obj через снап
  (снап может поднять obj в пределах bound — честно
  репортируется: bound vs actual).
- **Per-block hLip premise** — премиза (как в C436 контракте
  `CertifiedBlock`): bench-инстанс выставляет точный
  линейный bound для линейной головы; производные hLip
  (BlockLipschitz) — отдельный модуль.
- **Banker's rounding** — детерминизм Python-реализации
  (divmod + round-half-even на Fractions) — bench-факт,
  Lean-модель оперирует готовым snapped-значением из грида.
- **Глубина 8+** — bench-измерение бюджета (13 цифр
  знаменателей на границе против 2366 у C506), не теорема.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.GrowSnap

open Hagi.Theory.GrowTrunkBlock

/-! ## (a) Snap сохраняет obj с certified-границей

Lipschitz-премиза общего вида (bench: линейная голова MSE,
per-point (2|s−y| + |ds|)·|ds|; контракт-форма — per-block
`CertifiedBlock.hLip` с композицией L_old·L_new). -/
section ObjectiveBound

variable {ι : Type}

/-- Если obj Lipschitz по ℓ¹-расстоянию признаков с константой
L, а снап меняет каждую координату не более чем на полуячейку
2^-(k+1) сетки q/2^k, то obj после снапа ≤ obj до + L·n·2^-(k+1):
CERTIFIED граница деградации (bench-инстанс вычисляет её
точно и требует bound ≥ факт). -/
theorem snap_preserves_objective_bound
    {n : ℕ} (obj : (Fin n → ℝ) → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (k : ℕ)
    (hL : ∀ f g : Fin n → ℝ,
      |obj f - obj g| ≤ L * (∑ i, |f i - g i|))
    (f g : Fin n → ℝ)
    (herr : ∀ i, |f i - g i| ≤ (2 : ℝ) ^ (-(k : ℝ) - 1)) :
    obj g ≤ obj f + L * n * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
  have h1 : |obj g - obj f| ≤
      L * (∑ i, |g i - f i|) := hL g f
  have h2 : (∑ i, |g i - f i|) ≤
      (∑ _ : Fin n, (2 : ℝ) ^ (-(k : ℝ) - 1)) :=
    Finset.sum_le_sum fun i _ =>
      by simpa [abs_sub_comm] using herr i
  have h3 : (∑ _ : Fin n, (2 : ℝ) ^ (-(k : ℝ) - 1)) =
      n * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
    simp [Finset.card_univ, nsmul_eq_mul]
  have h4 : L * (∑ i, |g i - f i|) ≤
      L * n * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
    refine le_trans (mul_le_mul_of_nonneg_left h2 hL0) ?_
    rw [h3]
    exact le_of_eq (by ring)
  have h5 := le_abs_self (obj g - obj f)
  linarith

end ObjectiveBound

/-! ## (b) Снап сбрасывает знаменатели

Точка сетки q/2^k имеет знаменатель ≤ 2^k: на границе grow
знаменатели признаков bounded, экспоненциальный компаундинг
(~×3.2 на grow, C506) начинается заново с k бит. -/
section DenominatorReset

/-- Любая точка рациональной сетки q/2^k (q целое) имеет
канонический знаменатель ≤ 2^k — bench-механика snap к q/2^k (banker's rounding к ближайшей точке
грида в scripts/bench_bridge.py, режим grow-snap)
возвращает ровно такие значения; сумма таких точек по
lcm-комбинаторике степеней двойки снова в гриде. -/
theorem snap_denominator_reset (q : ℤ) (k : ℕ) :
    (q / ((2 : ℤ) ^ (k : ℕ)) : ℚ).den ≤ 2 ^ k := by
  have h := Rat.den_dvd q ((2 : ℤ) ^ (k : ℕ))
  have hq : (q / ((2 : ℤ) ^ (k : ℕ)) : ℚ) =
      Rat.divInt q ((2 : ℤ) ^ (k : ℕ)) := by
    rw [Rat.divInt_eq_div]
    push_cast
    congr 1
  rw [hq]
  have h2 := Int.le_of_dvd (by positivity) h
  exact_mod_cast h2

end DenominatorReset

/-! ## (c) Телескоп certified-цикла

Каждый grow-цикл: certified fd-шаги дают obj_{i+1} ≤ obj_i
(drop > 0), снап даёт obj_{i+1} ≤ obj_i + b_i; итог по циклу —
obj_final ≤ obj_start + Σ b_i (grow-инвариант ТОЧНЫЙ, вклад 0). -/
section CycleSound

/-- Телескоп certified snap-цикла: если step-функция стартует
в o0 и каждая фаза i поднимает obj не более чем на b_i, то
финальное значение ≤ o0 + сумма bound'ов. Индукция по списку
bound'ов (bench-инстанс: 6 grow-событий, Σ bounds — точная
Fraction-сумма per-snap certified границ). -/
theorem grow_snap_cycle_sound (o0 : ℝ) (bs : List ℝ)
    (step : ℕ → ℝ) (h0 : step 0 ≤ o0)
    (hstep : ∀ i, i < bs.length →
      step (i + 1) ≤ step i + bs.getD i 0) :
    step bs.length ≤ o0 + bs.sum := by
  induction bs generalizing step o0 with
  | nil =>
    rw [List.length_nil, List.sum_nil]
    linarith
  | cons b tl ih =>
    have hb : step 1 ≤ step 0 + b := hstep 0 (by simp)
    have ih' := ih (step 0 + b) (fun j => step (j + 1)) hb
      (fun i hi => hstep (i + 1) (by simp [hi]))
    calc step (b :: tl).length ≤ (step 0 + b) + tl.sum := by
          simpa [List.length_cons, Nat.add_comm] using ih'
      _ ≤ o0 + (b + tl.sum) := by linarith [h0]
      _ = o0 + (b :: tl).sum := by rw [List.sum_cons]

end CycleSound

end Hagi.Theory.GrowSnap

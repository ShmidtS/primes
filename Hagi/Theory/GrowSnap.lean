/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Theory.GrowTrunkBlock

/-!
# GrowSnap — certified snap-политика при identity-grow

Bench mini-hagi5 измерил экспоненциальную стену повторяемого grow-цикла:
знаменатели дробей признаков растут ~×3.2 на grow-событие
(63 → 263 → 789 → 2366 цифр для глубин 2 → 5), глубина 6
проецировалась ~8000 цифр / ~150 s — честный вычислительный
предел Fraction-арифметики (не теоретический). Snap-политика снимает
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
  premise (`CertifiedBlock` / BlockLipschitz:
  композиция перемножает константы). Общая форма —
  `snap_preserves_objective_bound`;
* телескоп по циклу: если каждая фаза даёт
  obj_{i+1} ≤ obj_i + b_i (certified drop даёт вклад ≤ 0),
  то финал ≤ старт + Σ b_i — `grow_snap_cycle_sound`
  (индукция по списку bound'ов).

Cycle-соответствие: `scripts/bench_bridge.py --mode grow-snap`
исполняет ровно эту схему: repeated grow (γ=0 identity,
EXACT obj-инвариант на каждом событии, certified fd-шаги
блока) + snap-фаза после обучения каждого блока; run-time
assert'ы: obj_after_snap ≤ obj_before + bound (bound ≥ факт),
знаменатели ≤ 2^k на каждой границе, telescoped
obj_final ≤ obj_cycle_start + Σ bounds.

## Limits (что этот мост НЕ покрывает)

- **Certified-шаги** — measured (drop > 0)
  snap-BOUND certified, но не монотонность obj через снап
  (снап может поднять obj в пределах bound — честно
  репортируется: bound vs actual).
- **Per-block hLip premise** — премиза (как в контракте
  `CertifiedBlock`): bench-инстанс выставляет точный
  линейный bound для линейной головы; производные hLip
  (BlockLipschitz) — отдельный модуль.
- **Banker's rounding** — детерминизм Python-реализации
  (divmod + round-half-even на Fractions) — bench-факт,
  Lean-модель оперирует готовым snapped-значением из грида.
- **Глубина 8+** — bench-измерение бюджета (13 цифр
  знаменателей на границе против 2366 у глубины 5), не теорема.
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
(~×3.2 на grow) начинается заново с k бит. -/
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

/-! ## (d) Оптимальный k: certified trade-off err-bound vs биты

Выбор знаменатель-грида 2^k в snap-механике выше — ручной
(бенчмарк брал 2^40-класс). Модуль формализует выбор k
теорией: per-weight ошибка ≤ полуячейка 2^-(k+1) даёт obj-err
≤ L·d·2^-(k+1) (композиция с (a)), биты = d·(k+1). Монотонности
противоположные (err ↓, биты ↑) — Pareto-фронт параметризован k;
для бюджета ошибок ε минимальное допустимое k существует
(`snapK`, Nat.find: минимальность по построению) и при
L·d > ε выражается ЗАМКНУТОЙ ФОРМОЙ ⌈log₂(L·d/ε)⌉ − 1
(`snap_k_eq_ceil`, точной: обе стороны из feasibility +
minimality). Decision-правило: k* = snapK — certified err в
бюджете, минимальные биты (`snap_optimal_k`) — v3-машина
выбирает k теорией вместо ручного 2^40. -/


section OptimalK

/-- Биты снапа d весов на гриде 2^k: k+1 бит на вес
(знаменатель-грид 2^k + 1), d весов — d·(k+1) всего. -/
def snapBits (d k : ℕ) : ℕ := d * (k + 1)

/-- Допустимость k для бюджета ошибок ε: certified err-bound
L·d·2^-(k+1) ≤ ε в положительной форме (эквивалентность —
`snap_admissible_iff`). -/
def snapAdmissible (L d ε : ℝ) (k : ℕ) : Prop :=
    L * d ≤ ε * (2:ℝ) ^ (k + 1)

/-- Полуячейка грида 2^k как обратная Nat-степень: мостик между
отрицательно-показательной формой (`herr`) и положительной
формой допустимости. -/
lemma two_pow_cell_eq_inv (k : ℕ) :
    (2:ℝ) ^ (-(k:ℝ) - 1) = ((2:ℝ) ^ (k + 1))⁻¹ := by
  have h : (-(k:ℝ) - 1) = -(((k:ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h, Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- Допустимость k ⟺ certified err-граница в бюджете ε
(ε > 0): положительная и полуячеечная формы эквивалентны. -/
lemma snap_admissible_iff (L d ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    snapAdmissible L d ε k ↔
      L * d * (2:ℝ) ^ (-(k:ℝ) - 1) ≤ ε := by
  have hx : (0:ℝ) < (2:ℝ) ^ (k + 1) := by positivity
  rw [snapAdmissible, two_pow_cell_eq_inv, ← div_eq_mul_inv,
    div_le_iff₀ hx]

/-- (a) ДВУСТОРОННЯЯ certified граница obj-ошибки снапа
d весов: |obj g − obj f| ≤ L·d·2^-(k+1) — композиция ℓ¹-Lipschitz
премизы с per-weight полуячейкой; суммарная err-форма для
бюджетного анализа (`snap_preserves_objective_bound` —
односторонняя деградация, здесь — каноническая ошибка). -/
theorem snap_err_bound {n : ℕ} (obj : (Fin n → ℝ) → ℝ) (L : ℝ)
    (hL0 : 0 ≤ L)
    (k : ℕ) (hL : ∀ f g : Fin n → ℝ,
      |obj f - obj g| ≤ L * ∑ i, |f i - g i|)
    (f g : Fin n → ℝ)
    (herr : ∀ i, |f i - g i| ≤ (2:ℝ) ^ (-(k:ℝ) - 1)) :
    |obj g - obj f| ≤ L * n * (2:ℝ) ^ (-(k:ℝ) - 1) := by
  have h1 := hL g f
  have h2 : (∑ i, |g i - f i|) ≤
      (∑ _ : Fin n, (2:ℝ) ^ (-(k:ℝ) - 1)) :=
    Finset.sum_le_sum fun i _ => by simpa [abs_sub_comm] using herr i
  have h3 : (∑ _ : Fin n, (2:ℝ) ^ (-(k:ℝ) - 1)) =
      n * (2:ℝ) ^ (-(k:ℝ) - 1) := by
    simp [Finset.card_univ, nsmul_eq_mul]
  have h4 : L * (∑ i, |g i - f i|) ≤
      L * n * (2:ℝ) ^ (-(k:ℝ) - 1) := by
    refine le_trans (mul_le_mul_of_nonneg_left h2 hL0) ?_
    rw [h3]
    exact le_of_eq (by ring)
  exact le_trans h1 h4

/-- n ≤ 2^n: локальная база архимедовости степеней двойки. -/
lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h1 : (1:ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

/-- Степени двойки неограничены: любой n ограничен 2^m —
экзистенциальная база k*-поиска. -/
lemma two_pow_unbounded (n : ℕ) : ∃ m : ℕ, n ≤ 2 ^ m := by
  induction n with
  | zero => exact ⟨0, by omega⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    have h1 : (1:ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨m + 1, by rw [Nat.pow_succ]; omega⟩

/-- Существует допустимое k для любого бюджета ε > 0
(L·d ≥ 0): 2^(k+1) обгоняет L·d/ε. -/
lemma pow2_le_succ (n : ℕ) : (2:ℝ) ^ n ≤ (2:ℝ) ^ (n + 1) := by
  have heq : (2:ℝ) ^ (n + 1) = (2:ℝ) ^ n + (2:ℝ) ^ n := by
    rw [pow_succ, mul_two]
  rw [heq]
  have h8 : (0:ℝ) ≤ (2:ℝ) ^ n := by positivity
  linarith

lemma snap_admissible_exists (L d ε : ℝ) (hε : 0 < ε)
    (hLd : 0 ≤ L * d) : ∃ k : ℕ, snapAdmissible L d ε k := by
  obtain ⟨m, hm⟩ := two_pow_unbounded (Nat.ceil (L * d / ε))
  have hceil : L * d / ε ≤ ((Nat.ceil (L * d / ε) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have h2r : L * d / ε ≤ ((2 ^ m : ℕ) : ℝ) :=
    le_trans hceil (by exact_mod_cast hm)
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2:ℝ) ^ m := by
    push_cast
    rfl
  rw [hcast] at h2r
  refine ⟨m, ?_⟩
  unfold snapAdmissible
  calc L * d ≤ ε * (L * d / ε) := by
        field_simp
        exact le_rfl
    _ ≤ ε * (2:ℝ) ^ m := mul_le_mul_of_nonneg_left h2r hε.le
    _ ≤ ε * (2:ℝ) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (pow2_le_succ m) hε.le

open Classical in
/-- МИНИМАЛЬНОЕ допустимое k: certified выбор знаменатель-грида
2^k для бюджета ошибок ε (decision-правило v3-машины). -/
noncomputable def snapK (L d ε : ℝ) (hε : 0 < ε)
    (hLd : 0 ≤ L * d) : ℕ :=
  Nat.find (snap_admissible_exists L d ε hε hLd)

open Classical in
/-- k* допустимо: certified err-граница L·d·2^-(k*+1) ≤ ε. -/
theorem snap_k_admissible (L d ε : ℝ) (hε : 0 < ε)
    (hLd : 0 ≤ L * d) :
    snapAdmissible L d ε (snapK L d ε hε hLd) :=
  Nat.find_spec (snap_admissible_exists L d ε hε hLd)

open Classical in
/-- МИНИМАЛЬНОСТЬ (точность, не достаточность): любое допустимое
k не меньше k*. -/
theorem snap_k_min (L d ε : ℝ) (hε : 0 < ε) (hLd : 0 ≤ L * d)
    (k : ℕ) (h : snapAdmissible L d ε k) :
    snapK L d ε hε hLd ≤ k :=
  Nat.find_min' (snap_admissible_exists L d ε hε hLd) h

/-- Негатив-сторона Pareto: k < k* НАРУШАЕТ бюджет — err-граница
СТРОГО больше ε (иначе k было бы допустимым). -/
theorem snap_k_lt_violates (L d ε : ℝ) (hε : 0 < ε)
    (hLd : 0 ≤ L * d) (k : ℕ) (h : k < snapK L d ε hε hLd) :
    ε < L * d * (2:ℝ) ^ (-(k:ℝ) - 1) := by
  have hx : (0:ℝ) < (2:ℝ) ^ (k + 1) := by positivity
  have hnot : ¬ (L * d ≤ ε * (2:ℝ) ^ (k + 1)) := by
    intro hk
    have := snap_k_min L d ε hε hLd k hk
    omega
  rw [two_pow_cell_eq_inv, ← div_eq_mul_inv, lt_div_iff₀ hx]
  exact lt_of_not_ge hnot

/-- Биты монотонны по k: больше грид — больше бит на веса. -/
lemma snapBits_mono (d k k' : ℕ) (h : k ≤ k') :
    snapBits d k ≤ snapBits d k' :=
  Nat.mul_le_mul_left d (Nat.add_le_add_right h 1)

/-- Err-граница АНТИмонотонна по k: больше грид — меньше
полуячейка (Pareto-сторона err ↓). -/
lemma snap_cell_antitone (k k' : ℕ) (h : k ≤ k') :
    (2:ℝ) ^ (-(k':ℝ) - 1) ≤ (2:ℝ) ^ (-(k:ℝ) - 1) := by
  rw [two_pow_cell_eq_inv, two_pow_cell_eq_inv,
    inv_le_inv₀ (show (0:ℝ) < (2:ℝ) ^ (k' + 1) by positivity)
      (show (0:ℝ) < (2:ℝ) ^ (k + 1) by positivity)]
  exact_mod_cast
    (Nat.pow_le_pow_right (show (1:ℕ) ≤ 2 by norm_num)
      (show k + 1 ≤ k' + 1 by omega) :
      (2:ℕ) ^ (k + 1) ≤ (2:ℕ) ^ (k' + 1))

/-- (b) ЗАМКНУТАЯ ФОРМА k* (ТОЧНАЯ): при L·d > ε
минимальное допустимое k равно ⌈log₂(L·d/ε)⌉ − 1. Обе стороны
выведены из Nat.find-фактов (feasibility даёт ceil ≤ k*+1,
minimality даёт k* ≤ ceil−1), т.е. ТОЧНОСТЬ, не достаточность.
При L·d ≤ ε: k* = 0 (k = 0 допустим, `Nat.find` минимален) и
формула с усечённым вычитанием тоже даёт 0. -/
theorem snap_k_eq_ceil (L d ε : ℝ) (hε : 0 < ε) (hLd : ε < L * d) :
    snapK L d ε hε (by linarith : (0:ℝ) ≤ L * d)
      = Nat.ceil (Real.logb 2 (L * d / ε)) - 1 := by
  have hc0 : 0 < L * d / ε :=
    div_pos (by linarith : (0:ℝ) < L * d) hε
  have hlog0 : 0 < Real.logb 2 (L * d / ε) := by
    refine Real.logb_pos (by norm_num) ?_
    rw [one_lt_div hε]
    exact hLd
  have hceil1 : 1 ≤ Nat.ceil (Real.logb 2 (L * d / ε)) :=
    Nat.ceil_pos.mpr hlog0
  -- допустимость ↔ ceil-неравенство
  have hadm : ∀ k : ℕ, snapAdmissible L d ε k ↔
      Nat.ceil (Real.logb 2 (L * d / ε)) ≤ k + 1 := by
    intro k
    constructor
    · intro h
      have hcdiv : L * d / ε ≤ (2:ℝ) ^ (k + 1) := by
        rw [div_le_iff₀ hε, mul_comm ((2:ℝ) ^ (k + 1)) ε]; exact h
      exact (Nat.ceil_le (a := Real.logb 2 (L * d / ε))).2
        ((Real.logb_le_iff_le_rpow (b := 2)
          (x := L * d / ε) (y := (((k:ℕ)+1 : ℕ) : ℝ))
          (by norm_num) hc0).2
          (by rw [Real.rpow_natCast]; exact hcdiv))
    · intro h
      have h2 : Real.logb 2 (L * d / ε) ≤ (((k:ℕ)+1 : ℕ) : ℝ) :=
        (Nat.ceil_le (a := Real.logb 2 (L * d / ε))).1 h
      have h3 : L * d / ε ≤ (2:ℝ) ^ (((k:ℕ)+1 : ℕ) : ℝ) :=
        (Real.logb_le_iff_le_rpow (b := 2)
          (x := L * d / ε) (y := (((k:ℕ)+1 : ℕ) : ℝ))
          (by norm_num) hc0).1 h2
      rw [Real.rpow_natCast, div_le_iff₀ hε] at h3
      rw [mul_comm ((2:ℝ) ^ (k + 1)) ε] at h3
      exact h3
  -- ceil ≤ k*+1: k* допустимо
  have hge : Nat.ceil (Real.logb 2 (L * d / ε))
      ≤ snapK L d ε hε (by linarith : (0:ℝ) ≤ L * d) + 1 :=
    (hadm _).1 (snap_k_admissible L d ε hε
      (by linarith : (0:ℝ) ≤ L * d))
  -- k* ≤ ceil−1: k := ceil−1 допустимо, минимальность
  have hadm2 : snapAdmissible L d ε
      (Nat.ceil (Real.logb 2 (L * d / ε)) - 1) := by
    refine (hadm _).2 ?_
    omega
  have hle := snap_k_min L d ε hε
    (by linarith : (0:ℝ) ≤ L * d) _ hadm2
  omega

/-- (c) Pareto-фронт trade-off параметризован k: при
k ≤ k' биты не убывают, полуячейка не возрастает. -/
theorem snap_bits_err_tradeoff (d k k' : ℕ) (h : k ≤ k') :
    snapBits d k ≤ snapBits d k' ∧
      (2:ℝ) ^ (-(k':ℝ) - 1) ≤ (2:ℝ) ^ (-(k:ℝ) - 1) :=
  ⟨snapBits_mono d k k' h, snap_cell_antitone k k' h⟩

/-- DECISION-ПРАВИЛО (MAIN): выбери k* = snapK — certified
err-граница в бюджете ε И минимальные биты среди всех допустимых
k (замена ручного 2^40 в v3-машине). d передаётся и как ℝ-вес
(границы), и как ℕ (биты), связанные hd. -/
theorem snap_optimal_k (L d ε : ℝ) (dε : ℕ) (hd : (dε:ℝ) = d)
    (hε : 0 < ε) (hLd : 0 ≤ L * d) :
    L * d * (2:ℝ) ^ (-(((snapK L d ε hε hLd : ℕ) : ℝ)) - 1) ≤ ε ∧
    ∀ k : ℕ, snapAdmissible L d ε k →
      snapBits dε (snapK L d ε hε hLd) ≤ snapBits dε k := by
  refine ⟨?_, ?_⟩
  · exact (snap_admissible_iff L d ε hε (snapK L d ε hε hLd)).mp
      (snap_k_admissible L d ε hε hLd)
  · intro k hk
    exact snapBits_mono dε _ _ (snap_k_min L d ε hε hLd k hk)

end OptimalK

end Hagi.Theory.GrowSnap

import Mathlib
import Primes.Basic
import Primes.GapFrequency

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

/-! ## Prime summatory operator: eigenpair analysis -/

/-- Арифметическая функция на натуральных числах. -/
abbrev ArithmeticFunction := Nat → ℝ

/-- Оператор суммирования по простым: `(Af)(n) = Σ_{p≤n} f(p)`. -/
def primeSummatoryOperator (f : ArithmeticFunction) (n : Nat) : ℝ :=
  (Finset.range (n + 1)).sum fun p => if Nat.Prime p then f p else 0

/-- Собственная пара для оператора суммирования по простым. -/
def IsPrimeSummatoryEigenpair (f : ArithmeticFunction) (eigenvalue : ℝ) : Prop :=
  f ≠ 0 ∧ ∀ n : Nat, primeSummatoryOperator f n = eigenvalue * f n

/-- Разность `Af(n+1) - Af(n)` равна `f(n+1)` если `n+1` простое, иначе `0`. -/
theorem primeSummatoryOperator_succ_diff (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator f (n + 1) - primeSummatoryOperator f n =
      (if Nat.Prime (n + 1) then f (n + 1) else 0) := by
  unfold primeSummatoryOperator
  rw [show (n + 1) + 1 = n + 2 by omega, Finset.sum_range_succ]
  ring

/-- Любая собственная пара удовлетворяет локальной рекурсии:
при переходе от `n` к `n+1` добавляется только вклад `n+1`. -/
theorem primeSummatoryEigenpair_recurrence {f : ArithmeticFunction} {eigenvalue : ℝ}
    (h : IsPrimeSummatoryEigenpair f eigenvalue) (n : Nat) :
    eigenvalue * f (n + 1) =
      eigenvalue * f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  rw [← h.2 (n + 1), ← h.2 n]; unfold primeSummatoryOperator
  rw [show (n + 1) + 1 = n + 2 by omega, Finset.sum_range_succ]

/-- Собственная пара с собственным значением 0: `f` обращается в нуль на всех простых. -/
theorem primeSummatoryEigenpair_zero_eigenvalue
    {f : ArithmeticFunction} (h : IsPrimeSummatoryEigenpair f 0) :
    ∀ p : Nat, Nat.Prime p → f p = 0 := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hrec := primeSummatoryEigenpair_recurrence h (p - 1)
  rw [show (p - 1) + 1 = p by omega] at hrec
  simp only [zero_mul, if_pos hp, zero_add] at hrec
  exact hrec.symm

/-- **Полная характеризация собственного пространства для 0**: `(f, 0)` — eigenpair
  ⟺ `f ≠ 0` и `f` зануляется на всех простых. -/
theorem primeSummatoryEigenpair_zero_iff
    (f : ArithmeticFunction) :
    IsPrimeSummatoryEigenpair f 0 ↔
      f ≠ 0 ∧ ∀ p : Nat, Nat.Prime p → f p = 0 := by
  refine ⟨fun h => ⟨h.1, primeSummatoryEigenpair_zero_eigenvalue h⟩, ?_⟩
  rintro ⟨hfne, hfzero⟩
  refine ⟨hfne, ?_⟩
  intro n
  unfold primeSummatoryOperator
  have hzero : ∀ p ∈ Finset.range (n + 1), (if Nat.Prime p then f p else 0 : ℝ) = 0 := by
    intro p hp
    by_cases hpr : Nat.Prime p
    · rw [if_pos hpr]; exact hfzero p hpr
    · rw [if_neg hpr]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_mul]

/-- При ненулевом собственном значении `f` постоянна между простыми. -/
theorem primeSummatoryEigenpair_const_between_primes
    {f : ArithmeticFunction} {ev : ℝ} (h : IsPrimeSummatoryEigenpair f ev)
    (hev : ev ≠ 0) (n : Nat) (hn : ¬Nat.Prime (n + 1)) :
    f (n + 1) = f n := by
  have hrec := primeSummatoryEigenpair_recurrence h n
  rw [if_neg hn, add_zero] at hrec
  exact mul_left_cancel₀ hev hrec

/-- При простом `n+1` скачок: `(ev - 1) · f(n+1) = ev · f(n)`. -/
theorem primeSummatoryEigenpair_jump_at_prime
    {f : ArithmeticFunction} {ev : ℝ} (h : IsPrimeSummatoryEigenpair f ev)
    (n : Nat) (hn : Nat.Prime (n + 1)) :
    (ev - 1) * f (n + 1) = ev * f n := by
  have hrec := primeSummatoryEigenpair_recurrence h n
  rw [if_pos hn] at hrec
  linear_combination hrec

/-! ## Spectral theorem: no nonzero eigenvalue other than possibly 1 -/

/-- Для `ev ≠ 0, 1` eigenpair не существует: `f = 0`, противоречие с `f ≠ 0`.
Доказательство: `f(2) = 0` (из `Af(2) = ev·f(2) = f(2)`), затем индукция:
при простых `jump` даёт `f(p) = 0`, между простыми `const` даёт `f = f(prev) = 0`. -/
theorem primeSummatoryEigenpair_no_nonzero_nonone_eigenvalue
    {f : ArithmeticFunction} {ev : ℝ}
    (h : IsPrimeSummatoryEigenpair f ev) (hev : ev ≠ 0) (hev1 : ev ≠ 1) : False := by
  have hf2 : f 2 = 0 := by
    have hAf2 := h.2 2
    unfold primeSummatoryOperator at hAf2
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hAf2
    simp only [Finset.sum_range_one, if_neg (by decide : ¬Nat.Prime 0),
      if_neg (by decide : ¬Nat.Prime 1), if_pos (by decide : Nat.Prime 2),
      zero_add, add_zero] at hAf2
    have h1 : (1 - ev) * f 2 = 0 := by linear_combination hAf2
    exact (mul_eq_zero.mp h1).resolve_left fun h => hev1 (sub_eq_zero.mp h).symm
  have hf1 : f 1 = 0 := by
    have hj := primeSummatoryEigenpair_jump_at_prime h 1 (by decide : Nat.Prime 2)
    rw [show 1 + 1 = 2 by omega, hf2] at hj
    have h1 : ev * f 1 = 0 := by
      have hzero : (ev - 1) * (0 : ℝ) = 0 := by ring
      linarith [hj, hzero]
    exact (mul_eq_zero.mp h1).resolve_left hev
  have hf0 : f 0 = 0 := by
    have hc := primeSummatoryEigenpair_const_between_primes h hev 0 (by decide : ¬Nat.Prime 1)
    rw [show 0 + 1 = 1 by omega] at hc
    exact hc.symm.trans hf1
  have hforall : ∀ n, f n = 0 := by
    intro n
    induction n with
    | zero => exact hf0
    | succ n ih =>
      by_cases hp : Nat.Prime (n + 1)
      · have hj := primeSummatoryEigenpair_jump_at_prime h n hp
        rw [show f n = (0 : ℝ) from ih] at hj
        rw [show ev * (0 : ℝ) = 0 by ring] at hj
        exact (mul_eq_zero.mp hj).resolve_left fun h => hev1 (sub_eq_zero.mp h)
      · exact (primeSummatoryEigenpair_const_between_primes h hev n hp).trans ih
  exact h.1 (by funext n; exact hforall n)

/-! ## Excluding eigenvalue 1 via Euclid's theorem -/

private lemma eigenpair_ev_one_impossible {f : ArithmeticFunction} {ev : ℝ}
    (h : IsPrimeSummatoryEigenpair f ev) (hev : ev = 1) : False := by
  have hev_ne : ev ≠ 0 := by rw [hev]; norm_num
  have hfpred : ∀ p : Nat, Nat.Prime p → 2 ≤ p → f (p - 1) = 0 := by
    intro p hp hp2
    have hj := primeSummatoryEigenpair_jump_at_prime h (p - 1) (by rw [show p - 1 + 1 = p from by omega]; exact hp)
    rw [show (p - 1) + 1 = p by omega, hev, show (1 - 1 : ℝ) = 0 from by norm_num,
        zero_mul, one_mul] at hj
    exact hj.symm
  have hf0 : f 0 = 0 := by
    have hAf0 := h.2 0
    unfold primeSummatoryOperator at hAf0
    rw [Finset.range_one, Finset.sum_singleton, if_neg (by decide : ¬Nat.Prime 0),
      hev, one_mul] at hAf0
    exact hAf0.symm
  have hf1 : f 1 = 0 := by
    have hAf1 := h.2 1
    unfold primeSummatoryOperator at hAf1
    rw [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      if_neg (by decide : ¬Nat.Prime 0), if_neg (by decide : ¬Nat.Prime 1),
      zero_add, hev, one_mul] at hAf1
    exact hAf1.symm
  have hforall : ∀ n, f n = 0 := by
    intro n
    match n with
    | 0 => exact hf0
    | 1 => exact hf1
    | n + 2 =>
      obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (n + 3)
      have hfp : f (p - 1) = 0 := hfpred p hp_prime (by omega)
      have hback : ∀ j, j ≤ p - 1 - (n + 2) → f (p - 1 - j) = 0 := by
        intro j hj
        induction j with
        | zero => exact hfp
        | succ j ih =>
          by_cases hpr : Nat.Prime (p - 1 - j)
          · rw [← show (p - 1 - j) - 1 = p - 1 - (j + 1) from by omega,
                hfpred (p - 1 - j) hpr (by omega)]
          · have hc := primeSummatoryEigenpair_const_between_primes h hev_ne
              (p - 2 - j) (by rw [show p - 2 - j + 1 = p - 1 - j from by omega]; exact hpr)
            rw [show p - 2 - j + 1 = p - 1 - j from by omega] at hc
            rw [show p - 1 - (j + 1) = p - 2 - j from by omega, ← hc]
            exact ih (by omega)
      have hkey := hback (p - 1 - (n + 2)) (by omega)
      rw [show p - 1 - (p - 1 - (n + 2)) = n + 2 from by omega] at hkey
      exact hkey
  exact h.1 (by funext n; exact hforall n)

/-- **Спектр оператора суммирования по простым тривиален: единственное собственное значение — 0.**

Для любого eigenpair `(f, ev)`:
- `ev ≠ 0, 1` → `f = 0` (индукция), противоречие.
- `ev = 1` → для каждого простого `p`, `f(p-1) = 0`; для каждого `n`, берём простое `p > n+2`,
  обратная индукция от `p-1` к `n` даёт `f(n) = 0`; `f = 0` — противоречие.
- Следовательно `ev = 0`. -/
theorem primeSummatoryEigenpair_only_zero_eigenvalue
    {f : ArithmeticFunction} {ev : ℝ} (h : IsPrimeSummatoryEigenpair f ev) : ev = 0 := by
  by_cases hev : ev = 0
  · exact hev
  by_cases hev1 : ev = 1
  · exact absurd (eigenpair_ev_one_impossible h hev1) (by trivial)
  · exact absurd (primeSummatoryEigenpair_no_nonzero_nonone_eigenvalue h hev hev1) (by trivial)

/-! ## Range structure: evaluation, non-surjectivity, image characterization -/

/-- `Af(0) = 0`: нет простых ≤ 0. -/
theorem primeSummatoryOperator_eval_zero (f : ArithmeticFunction) :
    primeSummatoryOperator f 0 = 0 := by
  unfold primeSummatoryOperator
  rw [Finset.range_one, Finset.sum_singleton, if_neg (by decide)]

/-- При простом `p`: `Af(p) = Af(p-1) + f(p)`. -/
theorem primeSummatoryOperator_eval_prime (f : ArithmeticFunction) (p : Nat) (hp : Nat.Prime p) :
    primeSummatoryOperator f p = primeSummatoryOperator f (p - 1) + f p := by
  have h := primeSummatoryOperator_succ_diff f (p - 1)
  have hp2 := hp.two_le
  rw [show (p - 1) + 1 = p from by omega, if_pos hp] at h
  linear_combination h

/-- При непростом `n > 0`: `Af(n) = Af(n-1)`. -/
theorem primeSummatoryOperator_eval_nonprime (f : ArithmeticFunction) (n : Nat)
    (hn : ¬Nat.Prime n) (hn1 : 0 < n) :
    primeSummatoryOperator f n = primeSummatoryOperator f (n - 1) := by
  have h := primeSummatoryOperator_succ_diff f (n - 1)
  rw [show (n - 1) + 1 = n from by omega, if_neg hn] at h
  linear_combination h

/-- **`A - I` не сюръективен**: `g(2) = 0` для любого `g` из образа `A - I`,
поэтому `g ≡ 1` не лежит в образе. Значит `1` принадлежит residual spectrum. -/
theorem primeSummatoryOperator_minus_I_not_surjective :
    ¬ ∃ f : ArithmeticFunction, ∀ n, primeSummatoryOperator f n - f n = 1 := by
  rintro ⟨f, hf⟩
  have h2 := hf 2
  unfold primeSummatoryOperator at h2
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h2
  simp only [Finset.sum_range_one, if_neg (by decide : ¬Nat.Prime 0),
    if_neg (by decide : ¬Nat.Prime 1), if_pos (by decide : Nat.Prime 2),
    zero_add, add_zero] at h2
  linarith

/-- **Образ `A` в точности состоит из функций с `g(0) = 0`, постоянных между простыми.**
Это полная характеризация образа оператора суммирования по простым:
`g ∈ range(A) ⟺ g(0) = 0 ∧ ∀ n > 0, ¬Prime n → g(n) = g(n-1)`. -/
theorem primeSummatoryOperator_range_iff (g : ArithmeticFunction) :
    (∃ f, ∀ n, primeSummatoryOperator f n = g n) ↔
      g 0 = 0 ∧ ∀ n, 0 < n → ¬Nat.Prime n → g n = g (n - 1) := by
  refine ⟨fun ⟨f, hf⟩ => ?_, fun ⟨hg0, hg_const⟩ => ?_⟩
  · refine ⟨(hf 0).symm.trans (primeSummatoryOperator_eval_zero f), ?_⟩
    intro n hn1 hn
    rw [← hf n, ← hf (n - 1), primeSummatoryOperator_eval_nonprime f n hn hn1]
  · set f : ArithmeticFunction := fun n => if Nat.Prime n then g n - g (n - 1) else 0 with hf
    refine ⟨f, ?_⟩
    intro n
    induction n with
    | zero =>
      unfold primeSummatoryOperator
      rw [Finset.range_one, Finset.sum_singleton, if_neg (by decide)]
      exact hg0.symm
    | succ n ih =>
      have hdiff := primeSummatoryOperator_succ_diff f n
      by_cases hp : Nat.Prime (n + 1)
      · have hfval : f (n + 1) = g (n + 1) - g n := by
          change (if Nat.Prime (n + 1) then g (n + 1) - g n else 0) = g (n + 1) - g n
          rw [if_pos hp]
        rw [if_pos hp, hfval] at hdiff
        have hAf : primeSummatoryOperator f (n + 1) = primeSummatoryOperator f n + (g (n + 1) - g n) := by
          linear_combination hdiff
        rw [hAf, ih]; ring
      · have hfval : f (n + 1) = 0 := by
          change (if Nat.Prime (n + 1) then g (n + 1) - g n else 0) = 0
          rw [if_neg hp]
        rw [if_neg hp] at hdiff
        have hAf : primeSummatoryOperator f (n + 1) = primeSummatoryOperator f n := by
          linear_combination hdiff
        rw [hAf, ih]
        exact (hg_const (n + 1) (by omega) hp).symm

/-! ## Iterated operator: A²f = double sum over primes -/

/-- `A²f(n) = Σ_{p≤n, prime} Σ_{q≤p, prime} f(q)` — двойная сумма по простым. -/
theorem primeSummatoryOperator_sq_eq_double_sum (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator (primeSummatoryOperator f) n =
      ((Finset.range (n + 1)).filter Nat.Prime).sum fun p =>
        ((Finset.range (p + 1)).filter Nat.Prime).sum fun q => f q := by
  have h_outer : primeSummatoryOperator (primeSummatoryOperator f) n =
    (Finset.range (n + 1)).sum (fun p => if Nat.Prime p then primeSummatoryOperator f p else 0) := rfl
  rw [h_outer, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  have h_inner : primeSummatoryOperator f p =
    (Finset.range (p + 1)).sum (fun q => if Nat.Prime q then f q else 0) := rfl
  rw [h_inner, ← Finset.sum_filter]

/-- **A²f(n) = Σ_{q≤n, prime} f(q) · |{primes p : q ≤ p ≤ n}|**
— явная формула для итерированного оператора.
Перестановка двойной суммы: `Σ_p Σ_{q≤p} = Σ_q Σ_{p≥q}`. -/
theorem primeSummatoryOperator_sq (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator (primeSummatoryOperator f) n =
      ((Finset.range (n + 1)).filter Nat.Prime).sum fun q =>
        (((Finset.Icc q n).filter Nat.Prime).card : ℝ) * f q := by
  rw [primeSummatoryOperator_sq_eq_double_sum]
  set S := (Finset.range (n + 1)).filter Nat.Prime with hS
  -- Step 1: rewrite inner range as S.filter (fun q => q ≤ p)
  have h_eq1 : S.sum (fun p => ((Finset.range (p + 1)).filter Nat.Prime).sum (fun q => f q)) =
               S.sum (fun p => (S.filter (fun q => q ≤ p)).sum (fun q => f q)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_range] at hp
    have hp_le : p ≤ n := Nat.le_of_lt_succ hp.1
    have h_eq : ((Finset.range (p + 1)).filter Nat.Prime) = S.filter (fun q => q ≤ p) := by
      ext q
      constructor
      · rintro h
        rw [Finset.mem_filter, Finset.mem_range] at h
        obtain ⟨hq, hprime⟩ := h
        rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, hprime⟩, Nat.le_of_lt_succ hq⟩
      · rintro h
        rw [Finset.mem_filter] at h
        rw [hS, Finset.mem_filter, Finset.mem_range] at h
        obtain ⟨⟨_, hprime⟩, hq_le⟩ := h
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le hq_le, hprime⟩
    rw [h_eq]
  rw [h_eq1]
  -- Step 2: convert filtered sum to if-then-else
  have h_eq2 : S.sum (fun p => (S.filter (fun q => q ≤ p)).sum (fun q => f q)) =
               S.sum (fun p => S.sum (fun q => if q ≤ p then f q else 0)) := by
    apply Finset.sum_congr rfl
    intro p _; rw [Finset.sum_filter]
  rw [h_eq2, Finset.sum_comm]
  -- Step 3: extract f(q) from inner sum
  have h_eq3 : S.sum (fun q => S.sum (fun p => if q ≤ p then f q else 0)) =
               S.sum (fun q => (((Finset.Icc q n).filter Nat.Prime).card : ℝ) * f q) := by
    apply Finset.sum_congr rfl
    intro q _hq
    rw [← Finset.sum_filter]
    have h_card_eq : (S.filter (fun p => q ≤ p)) = ((Finset.Icc q n).filter Nat.Prime) := by
      ext p
      constructor
      · rintro h
        rw [Finset.mem_filter] at h
        obtain ⟨h1, h2⟩ := h
        rw [hS, Finset.mem_filter] at h1
        obtain ⟨h1a, h1b⟩ := h1
        rw [Finset.mem_range] at h1a
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h2, Nat.le_of_lt_succ h1a⟩, h1b⟩
      · rintro h
        rw [Finset.mem_filter] at h
        obtain ⟨h1, h2⟩ := h
        rw [Finset.mem_Icc] at h1
        obtain ⟨h1a, h1b⟩ := h1
        rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨Nat.lt_succ_of_le h1b, h2⟩, h1a⟩
    rw [h_card_eq, Finset.sum_const]
    simp
  rw [h_eq3]

/-! ## Jordan structure: ker(A²) = ker(A) and spectral decomposition -/

/-- `Af = 0` (для всех `n`) ⟺ `f` обращается в нуль на всех простых.
Версия `primeSummatoryEigenpair_zero_iff` без требования `f ≠ 0`. -/
theorem primeSummatoryOperator_eq_zero_iff (f : ArithmeticFunction) :
    (∀ n, primeSummatoryOperator f n = 0) ↔ (∀ p, Nat.Prime p → f p = 0) := by
  refine ⟨fun hf p hp => ?_, fun hf n => ?_⟩
  · have h := primeSummatoryOperator_eval_prime f p hp
    rw [hf p, hf (p - 1)] at h
    linarith
  · unfold primeSummatoryOperator
    have hzero : ∀ p ∈ Finset.range (n + 1), (if Nat.Prime p then f p else 0 : ℝ) = 0 := by
      intro p _; by_cases hpr : Nat.Prime p
      · rw [if_pos hpr]; exact hf p hpr
      · rw [if_neg hpr]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]

/-- Если `Af` обращается в нуль на всех простых, то `Af = 0` везде:
`Af` — ступенчатая функция (постоянная между простыми), поэтому
нуль на простых влечёт нуль на всём `Nat`. -/
theorem primeSummatoryOperator_vanishes_on_primes_imp_zero (f : ArithmeticFunction)
    (hf : ∀ p, Nat.Prime p → primeSummatoryOperator f p = 0) :
    ∀ n, primeSummatoryOperator f n = 0 := by
  intro n
  induction n with
  | zero => exact primeSummatoryOperator_eval_zero f
  | succ n ih =>
    by_cases hp : Nat.Prime (n + 1)
    · exact hf (n + 1) hp
    · have h := primeSummatoryOperator_eval_nonprime f (n + 1) hp (by omega)
      have : primeSummatoryOperator f (n + 1) = primeSummatoryOperator f n := h
      rw [this, ih]

/-- **ker(A²) = ker(A)**: алгебраическая кратность собственного значения 0
равна геометрической. Jordan block для 0 имеет размер 1 — нет нетривиальных
жордановых цепей.

Доказательство:
- `←`: `Af = 0 → A²f = A(0) = 0`.
- `→`: `A²f = 0 → A(Af) = 0 → Af` обращается в нуль на простых (по char ker(A))
  → `Af = 0` везде (ступенчатость) → `f ∈ ker(A)`. -/
theorem primeSummatoryOperator_ker_sq_eq_ker (f : ArithmeticFunction) :
    (∀ n, primeSummatoryOperator (primeSummatoryOperator f) n = 0) ↔
    (∀ n, primeSummatoryOperator f n = 0) := by
  refine ⟨fun hf => ?_, fun hf n => ?_⟩
  · have hAf_vanishes : ∀ p, Nat.Prime p → primeSummatoryOperator f p = 0 :=
      (primeSummatoryOperator_eq_zero_iff (primeSummatoryOperator f)).mp hf
    exact primeSummatoryOperator_vanishes_on_primes_imp_zero f hAf_vanishes
  · have hzero : ∀ p ∈ Finset.range (n + 1),
        (if Nat.Prime p then primeSummatoryOperator f p else 0 : ℝ) = 0 := by
      intro p _; by_cases hpr : Nat.Prime p
      · rw [if_pos hpr, hf p]
      · rw [if_neg hpr]
    have h_unfolding : primeSummatoryOperator (primeSummatoryOperator f) n =
        (Finset.range (n + 1)).sum (fun p => if Nat.Prime p then primeSummatoryOperator f p else 0) := rfl
    rw [h_unfolding, Finset.sum_congr rfl hzero, Finset.sum_const_zero]

/-- **A - I инъективен**: если `Af = f`, то `f = 0`.
Собственное значение 1 не существует, поэтому `A - I` — мономорфизм.
Значит `1` принадлежит residual spectrum (не сюръективен, но инъективен). -/
theorem primeSummatoryOperator_Af_eq_f_imp_f_eq_zero (f : ArithmeticFunction)
    (hf : ∀ n, primeSummatoryOperator f n = f n) : f = 0 := by
  by_contra hf_ne
  have h : IsPrimeSummatoryEigenpair f 1 := ⟨hf_ne, by intro n; rw [hf n, one_mul]⟩
  exact absurd (eigenpair_ev_one_impossible h rfl) (by trivial)

/-- **Полная спектральная декомпозиция A**:
- Point spectrum: `{0}` (eigenspace = {f : f|_primes = 0, f ≠ 0})
- Residual spectrum: `{1}` (A - I injective, not surjective)
- Continuous spectrum: `∅` (для λ ≠ 0, 1: A - λI injective)
- Jordan: ker(A²) = ker(A) — block size 1 для eigenvalue 0

Следствие: `σ(A) = {0, 1}`, спектр дискретный, непрерывной части нет. -/
theorem primeSummatoryOperator_Af_eq_lambda_f_imp_f_eq_zero (f : ArithmeticFunction) (ev : ℝ)
    (hev : ev ≠ 0) (hev1 : ev ≠ 1)
    (hf : ∀ n, primeSummatoryOperator f n = ev * f n) : f = 0 := by
  by_contra hf_ne
  exact primeSummatoryEigenpair_no_nonzero_nonone_eigenvalue ⟨hf_ne, hf⟩ hev hev1

/-! ## Connection to prime counting function -/

/-- **A[1] = π**: применение оператора к постоянной функции 1
даёт функцию подсчёта простых чисел. -/
theorem primeSummatoryOperator_apply_one (n : Nat) :
    primeSummatoryOperator (fun _ => (1 : ℝ)) n = (primeCountingExact n : ℝ) := by
  have h_rfl : primeSummatoryOperator (fun _ => (1 : ℝ)) n =
      (Finset.range (n + 1)).sum (fun p => if Nat.Prime p then (1 : ℝ) else 0) := rfl
  rw [h_rfl, ← Finset.sum_filter]
  unfold primeCountingExact
  rw [Finset.card_eq_sum_ones]
  push_cast
  rfl

end
end PrimeGaps

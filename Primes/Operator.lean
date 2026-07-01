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
    -- hAf2 : f 2 = ev * f 2
    have h1 : (1 - ev) * f 2 = 0 := by linear_combination hAf2
    have h2 : 1 - ev ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hev1; exact hev1 rfl
    exact (mul_eq_zero.mp h1).resolve_left h2
  have hf1 : f 1 = 0 := by
    have hj := primeSummatoryEigenpair_jump_at_prime h 1 (by decide : Nat.Prime 2)
    rw [show 1 + 1 = 2 by omega] at hj
    rw [hf2] at hj
    -- hj : (ev - 1) * 0 = ev * f 1
    have h1 : ev * f 1 = 0 := by
      have : (ev - 1) * (0 : ℝ) = 0 := by ring
      linarith [hj, this]
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
        have h00 : ev * (0 : ℝ) = 0 := by ring
        rw [h00] at hj
        have hev1' : ev - 1 ≠ 0 := by
          intro h; rw [sub_eq_zero.mp h] at hev1; exact hev1 rfl
        exact (mul_eq_zero.mp hj).resolve_left hev1'
      · have hc := primeSummatoryEigenpair_const_between_primes h hev n hp
        rw [hc]; exact ih
  exact h.1 (by funext n; exact hforall n)

/-! ## Excluding eigenvalue 1 via Euclid's theorem -/

private lemma eigenpair_ev_one_impossible {f : ArithmeticFunction} {ev : ℝ}
    (h : IsPrimeSummatoryEigenpair f ev) (hev : ev = 1) : False := by
  have hev_ne : ev ≠ 0 := by rw [hev]; norm_num
  have hfpred : ∀ p : Nat, Nat.Prime p → 2 ≤ p → f (p - 1) = 0 := by
    intro p hp hp2
    have hj := primeSummatoryEigenpair_jump_at_prime h (p - 1) (by
      have h1 : p - 1 + 1 = p := by omega
      rw [h1]; exact hp)
    rw [show (p - 1) + 1 = p by omega, hev] at hj
    rw [show (1 - 1 : ℝ) = 0 from by norm_num, zero_mul, one_mul] at hj
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
      have hge : n + 2 ≤ p - 1 := by omega
      have hback : ∀ j, j ≤ p - 1 - (n + 2) → f (p - 1 - j) = 0 := by
        intro j hj
        induction j with
        | zero => exact hfp
        | succ j ih =>
          have hjm : p - 1 - j ≥ n + 2 := by omega
          by_cases hpr : Nat.Prime (p - 1 - j)
          · have hge2 : 2 ≤ p - 1 - j := by omega
            have hpred := hfpred (p - 1 - j) hpr hge2
            -- hpred : f ((p-1-j) - 1) = 0
            -- Goal: f (p - 1 - (j + 1)) = 0
            -- (p-1-j) - 1 = p - 1 - (j + 1) = p - 2 - j
            have heq : (p - 1 - j) - 1 = p - 1 - (j + 1) := by omega
            rw [← heq, hpred]
          · have hc := primeSummatoryEigenpair_const_between_primes h hev_ne
              (p - 2 - j) (by
                have h1 : p - 2 - j + 1 = p - 1 - j := by omega
                rw [h1]; exact hpr)
            rw [show p - 2 - j + 1 = p - 1 - j by omega] at hc
            -- hc : f (p - 1 - j) = f (p - 2 - j)
            -- ih : f (p - 1 - j) = 0
            -- Goal: f (p - 1 - (j + 1)) = 0
            -- p - 1 - (j + 1) = p - 2 - j
            have heq : p - 1 - (j + 1) = p - 2 - j := by omega
            have hj' : j ≤ p - 1 - (n + 2) := by omega
            rw [heq, hc.symm, ih hj']
      have hkey := hback (p - 1 - (n + 2)) (by omega)
      have hn' : p - 1 - (p - 1 - (n + 2)) = n + 2 := by omega
      rw [hn'] at hkey
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

end
end PrimeGaps

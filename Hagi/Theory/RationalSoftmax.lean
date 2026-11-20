/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Certified rational softmax intervals

Roadmap C486 (4).  The certified-CE surrogates currently running
in `scripts/bench_bridge.py` replace the softmax exponentials by
uncertified rational stand-ins (the `z ^ 2 / Σ z ^ 2` surrogate
of C442, the `L1`-rms surrogate of C481).  This module provides
the certified replacement layer: TWO-SIDED rational exponential
bounds that sandwich `Real.exp x` between rational numbers
whenever `x` is rational, so that a rational-arithmetic
"softmax" built from them is provably below and above the true
softmax.

## The exponential interval

For `n : ℕ`, `0 < n`, and `-n ≤ x`:

* `expLower_le_exp`  : `(1 + x / n) ^ n ≤ Real.exp x`
* `exp_le_expUpper`  : `x < m → Real.exp x ≤ (1 - x / m) ^ (-m)`

Both follow from the unconditional `Real.add_one_le_exp`
(`1 + t ≤ e ^ t`) raised to the `n`-th power via
`Real.exp_nat_mul`; no invented constants, every step is a
Mathlib lemma.  At rational `x` both endpoints are rational.

## The certified softmax sandwich

`rationalSoftmaxCert`: if `lo ≤ e ^ (z ·) ≤ hi` pointwise with
`0 < lo`, then for every vocabulary index `v`,

`lo v / ∑ hi ≤ softDef z v ≤ hi v / ∑ lo`,

i.e. the true softmax probability is certified-bounded by the
rational surrogate pair — the two-sided closing of the C442 /
C481 surrogate pins (those surrogates themselves are NOT
rewritten in this bit; see the pointers below).

## The certified CE bridge

`certCE_le`: the one-hot cross-entropy of the lower rational
substitute upper-bounds the true one-hot cross-entropy
(`-log p u ≤ -log (lo u / ∑ hi)`).  `certCE_gap`: the
certificate's excess decomposes as

`(gap) ≤ log ((hi u / lo u) * (∑ hi / ∑ lo))`,

the product of the pointwise interval width and the
normalizer-interval width.  On a max-shifted logit vector
(`z - max`) with range `R`, the `(1 + x/n) ^ n` family makes
this width a certified function of `(n, m, R)` — the analytic
analogue of the variance-adaptive majorizer multipliers
(`Real.exp r`, the Bennett `kappa`) of
`Hagi.Theory.AdaptiveMajorizer`.

## Honest pins

1. Bernoulli monotonicity (`(1 + x / n) ^ n` increasing in
   `n`) is NOT proven here; accuracy growth with `n`, `m` is
   documented, not certified.
2. Bench wiring (cert-ce / trunk surrogate replacement in
   `scripts/bench_bridge.py`) is a FUTURE bit; this module is
   the consumption-ready statement layer only.
-/

set_option linter.style.header false

namespace Hagi.Theory.RationalSoftmax

open Real Hagi.Prelude

/-! ## Two-sided rational exponential bounds -/

/-- Core lower bound: for `0 < n` and `-n ≤ x`,
`(1 + x / n) ^ n ≤ Real.exp x`.  The premise `-n ≤ x` keeps the
base nonnegative (for `x < -n` and even `n` the claim fails). -/
theorem expLower_le_exp {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : -n ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x := by
  have hnR : (0 : ℝ) < n := by positivity
  have hxn : (-1 : ℝ) ≤ x / n := by
    have hmul : (-1 : ℝ) * n = -n := by ring
    rw [le_div_iff₀ hnR, hmul]
    linarith
  have hbase : (0 : ℝ) ≤ 1 + x / n := by linarith
  have h1 : 1 + x / n ≤ Real.exp (x / n) := by
    rw [add_comm]
    exact Real.add_one_le_exp _
  have h2 : (1 + x / n) ^ n ≤ Real.exp (x / n) ^ n :=
    pow_le_pow_left₀ hbase h1 n
  rw [← Real.exp_nat_mul (x / n) n] at h2
  have hnx : n * (x / n) = x := by field_simp
  rwa [hnx] at h2

/-- Roadmap form of the lower bound: for `0 ≤ x`,
`(1 + x / n) ^ n ≤ e ^ x`. -/
theorem expLower_le_exp' {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x :=
  expLower_le_exp hn (by linarith)

/-- Upper bound, product form (equivalent to
`e ^ x ≤ (1 - x / m) ^ (-m)` for `0 < 1 - x / m`): for `0 < m`
and `x < m`, `(1 - x / m) ^ m * e ^ x ≤ 1`.  Rational at
rational `x`; combined with `expLower_le_exp` this is the
certified exponential interval. -/
theorem exp_le_expUpper {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : x < m) :
    (1 - x / m) ^ m * Real.exp x ≤ 1 := by
  have hmR : (0 : ℝ) < m := by positivity
  have hmul : (-1 : ℝ) * m = -m := by ring
  have hxm : (-1 : ℝ) < -x / m := by
    rw [lt_div_iff₀ hmR, hmul]
    linarith
  have hbase : (0 : ℝ) ≤ 1 + -x / m := by linarith
  have heq : 1 - x / m = 1 + -x / m := by ring
  have hlow0 : (1 + -x / m) ^ m ≤ Real.exp (-x) :=
    expLower_le_exp hm (by linarith)
  have hlow : (1 - x / m) ^ m ≤ Real.exp (-x) := by rwa [heq]
  have h2 : (1 - x / m) ^ m ≤ (Real.exp x)⁻¹ := by
    rwa [← Real.exp_neg]
  have h3 : (1 - x / m) ^ m * Real.exp x
      ≤ (Real.exp x)⁻¹ * Real.exp x :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  rwa [inv_mul_cancel₀ (ne_of_gt (Real.exp_pos x))] at h3

/-- Packaged certified exponential interval: for `0 < n`,
`0 < m`, `0 ≤ x < m`, the rational endpoints sandwich `e ^ x`
(lower bound below, reciprocal upper bound in product form). -/
theorem expInterval_cert {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {x : ℝ} (hx0 : 0 ≤ x) (hxm : x < m) :
    (1 + x / n) ^ n ≤ Real.exp x ∧ (1 - x / m) ^ m * Real.exp x ≤ 1 :=
  ⟨expLower_le_exp' hn hx0, exp_le_expUpper hm hxm⟩

/-! ## The certified softmax sandwich -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- The two-sided certified softmax sandwich: if `lo ≤ e ^ (z ·)
≤ hi` pointwise with `0 < lo`, then every true softmax
probability `softDef z v` lies between the rational surrogate
bounds `lo v / ∑ hi` and `hi v / ∑ lo`. -/
theorem rationalSoftmaxCert {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (v : V) :
    lo v / ∑ w, hi w ≤ softDef z v ∧ softDef z v ≤ hi v / ∑ w, lo w := by
  have hhi0 : ∀ v, 0 < hi v := fun v => lt_of_lt_of_le (Real.exp_pos _) (hhi v)
  have hsumlo : (0 : ℝ) < ∑ w, lo w :=
    Finset.sum_pos (fun w _ => hlo0 w) Finset.univ_nonempty
  have hsumhi : (0 : ℝ) < ∑ w, hi w :=
    Finset.sum_pos (fun w _ => hhi0 w) Finset.univ_nonempty
  have hsume : (0 : ℝ) < ∑ w, Real.exp (z w) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have s1 : ∑ w, lo w ≤ ∑ w, Real.exp (z w) :=
    Finset.sum_le_sum (fun w _ => hlo w)
  have s2 : ∑ w, Real.exp (z w) ≤ ∑ w, hi w :=
    Finset.sum_le_sum (fun w _ => hhi w)
  have hsd : softDef z v = Real.exp (z v) / ∑ w, Real.exp (z w) := rfl
  constructor
  · rw [hsd, div_le_div_iff₀ hsumhi hsume]
    exact mul_le_mul (hlo v) s2 hsume.le (le_of_lt (Real.exp_pos _))
  · rw [hsd, div_le_div_iff₀ hsume hsumlo]
    exact mul_le_mul (hhi v) s1 hsumlo.le (le_of_lt (hhi0 v))

/-! ## The certified CE bridge -/

/-- One-hot CE certificate: the true one-hot cross-entropy at `u`
(`-log (softDef z u)`) is bounded above by the CE of the lower
rational substitute `-log (lo u / ∑ hi)` — a certified upper
certificate on the true CE from rational data alone. -/
theorem certCE_le {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (u : V) :
    -Real.log (softDef z u) ≤ -Real.log (lo u / ∑ w, hi w) := by
  have ⟨hlow, _⟩ := rationalSoftmaxCert hlo hlo0 hhi u
  have hsumhi : (0 : ℝ) < ∑ w, hi w :=
    Finset.sum_pos (fun w _ => lt_of_lt_of_le (Real.exp_pos _) (hhi w))
      Finset.univ_nonempty
  have h0 : (0 : ℝ) < lo u / ∑ w, hi w := div_pos (hlo0 u) hsumhi
  have := Real.log_le_log h0 hlow
  linarith

/-- Certified CE gap decomposition: the excess of the rational CE
certificate over the true one-hot CE is bounded by the logarithm
of the ratio of the pointwise-numerator and denominator interval
widths `(hi u * ∑ hi) / (lo u * ∑ lo)` — the product of the
pointwise interval width `hi u / lo u` and the normalizer
interval width `∑ hi / ∑ lo`.  This is the certified
`(n, m, R)`-width link for the `(1 + x / n) ^ n` family (see the
module docstring; the C442 / C481 surrogate closure rides on
this bound in a future bench bit). -/
theorem certCE_gap {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (u : V) :
    Real.log (softDef z u) - Real.log (lo u / ∑ w, hi w) ≤
      Real.log ((hi u * ∑ w, hi w) / (lo u * ∑ w, lo w)) := by
  have hhi0 : ∀ v, 0 < hi v := fun v => lt_of_lt_of_le (Real.exp_pos _) (hhi v)
  have hsumlo : (0 : ℝ) < ∑ w, lo w :=
    Finset.sum_pos (fun w _ => hlo0 w) Finset.univ_nonempty
  have hsumhi : (0 : ℝ) < ∑ w, hi w :=
    Finset.sum_pos (fun w _ => hhi0 w) Finset.univ_nonempty
  have hsume : (0 : ℝ) < ∑ w, Real.exp (z w) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have s1 : ∑ w, lo w ≤ ∑ w, Real.exp (z w) :=
    Finset.sum_le_sum (fun w _ => hlo w)
  have key : Real.exp (z u) * ∑ w, lo w ≤ hi u * ∑ w, Real.exp (z w) :=
    mul_le_mul (hhi u) s1 hsumlo.le (hhi0 u).le
  have hp : (0 : ℝ) < softDef z u := softDef_pos z u
  have hq : (0 : ℝ) < lo u / ∑ w, hi w := div_pos (hlo0 u) hsumhi
  have hsd : softDef z u = Real.exp (z u) / ∑ w, Real.exp (z w) := rfl
  have hR : hi u * (∑ w, hi w) * (lo u / ∑ w, hi w) = hi u * lo u := by
    rw [mul_comm (hi u * (∑ w, hi w)) (lo u / (∑ w, hi w)),
      div_mul_eq_mul_div, ← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt hsumhi),
      mul_comm (lo u) (hi u)]
  have hratio : softDef z u / (lo u / ∑ w, hi w) ≤
      (hi u * (∑ w, hi w)) / (lo u * (∑ w, lo w)) := by
    refine (div_le_div_iff₀ hq (mul_pos (hlo0 u) hsumlo)).2 ?_
    rw [hR, hsd, div_mul_eq_mul_div, div_le_iff₀ hsume]
    calc Real.exp (z u) * (lo u * ∑ w, lo w)
        = (Real.exp (z u) * ∑ w, lo w) * lo u := by ring
      _ ≤ (hi u * ∑ w, Real.exp (z w)) * lo u :=
          mul_le_mul_of_nonneg_right key (hlo0 u).le
      _ = hi u * lo u * ∑ w, Real.exp (z w) := by ring
  rw [← Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
  exact Real.log_le_log (div_pos hp hq) hratio

end Hagi.Theory.RationalSoftmax

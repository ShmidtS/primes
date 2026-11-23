/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Hagi.Cert.CertifiedArgmax
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Softmax — the certified rational exp-interval canon (→)

One canonical module for the certified softmax sandwich family
(merged from RationalSoftmax.lean + SandwichMonotone.lean +
BandTightening.lean; namespaces preserved, Continual.lean
precedent). The concept is described ONCE here: `Real.exp x` is
sandwiched between RATIONAL endpoints `(1 + x / n) ^ n ≤ e ^ x ≤
(1 - x / m) ^ (-m)` (valid for `0 < n`, `0 < m`, `0 ≤ x < m`;
rational at rational `x`), so a rational-arithmetic softmax built
from them is provably below and above the true softmax.

* The exponential interval and the certified softmax / CE bridge
  (`Hagi.Theory.RationalSoftmax`): the two-sided
  rational exponential bounds, `rationalSoftmaxCert`, and the
  one-hot CE certificates `certCE_le` / `certCE_gap`.
* Monotonicity in the LOGIT and certified prediction
  (`Hagi.Theory.SandwichMonotone`): the rational walls are
  monotone in `x`, disjoint sandwich intervals certify the argmax
  (the Bernoulli-in-`n` pin remained open — closed one layer
  up by BandTightening).
* Summed `p̂` anti-monotonicity, exactly characterized:
  the TOTAL lower estimate is anti-monotone when only the
  denominator walls of ONE band are refined
  (`sum_phat_anti_mono_single_domain`); when the walls move
  with the logits the total is NOT anti-monotone
  honest pin, now a formal counterexample inside the certified
  band (`band_mix_counterex`, `phat_total_not_anti_mono`).
* Monotonicity in the DENOMINATOR and band tightening
  (`Hagi.Theory.BandTightening`): `(1 + x / n) ^ n` is
  nondecreasing in `n` (the closed pin, Lagrange MVT), the
  band width shrinks under wall refinement, and adaptive
  calibration certifies the midpoint argmax.
-/

/-! ## RationalSoftmax — the exp interval and the certified softmax/CE bridge -/

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
module docstring; the surrogate closure rides on
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

/-! ## SandwichMonotone — logit monotonicity and certified prediction -/

namespace Hagi.Theory.SandwichMonotone

open Real Hagi.Prelude Hagi.Theory.RationalSoftmax

/-! ## Monotonicity of the rational exponential bounds -/

/-- The lower rational bound is monotone in the logit: for
fixed `n`, `0 < n`, `-n ≤ x ≤ x'`, `(1 + x/n) ^ n` is
nondecreasing in `x` (monotone nonnegative base raised by
`pow_le_pow_left₀`). -/
theorem expLower_mono {n : ℕ} (hn : 0 < n) {x x' : ℝ}
    (hx : -n ≤ x) (hxx : x ≤ x') :
    (1 + x / n) ^ n ≤ (1 + x' / n) ^ n := by
  have hnR : (0 : ℝ) < n := by positivity
  have hbase0 : (0 : ℝ) ≤ 1 + x / n := by
    have h : (-1 : ℝ) ≤ x / n := by
      rw [le_div_iff₀ hnR]
      have hmul : (-1 : ℝ) * n = -n := by ring
      rw [hmul]; exact hx
    linarith
  have hbase : 1 + x / n ≤ 1 + x' / n := by
    have h : x / n ≤ x' / n := div_le_div_of_nonneg_right hxx hnR.le
    linarith
  exact pow_le_pow_left₀ hbase0 hbase n

/-- The upper rational bound is nondecreasing in the logit:
for fixed `m`, `0 < m`, `x ≤ x' < m`, the reciprocal base
shrinks, so `(1 - x'/m) ^ m ≤ (1 - x/m) ^ m`. -/
theorem expUpper_mono {m : ℕ} (hm : 0 < m) {x x' : ℝ}
    (hxx : x ≤ x') (hx' : x' < m) :
    (1 - x' / m) ^ m ≤ (1 - x / m) ^ m := by
  have hmR : (0 : ℝ) < m := by positivity
  have hbase0 : (0 : ℝ) ≤ 1 - x' / m := by
    have h : x' / m < 1 := by
      rw [div_lt_iff₀ hmR, one_mul]; exact hx'
    linarith
  have hbase : 1 - x' / m ≤ 1 - x / m := by
    have h : x / m ≤ x' / m := div_le_div_of_nonneg_right hxx hmR.le
    linarith
  exact pow_le_pow_left₀ hbase0 hbase m

/-- The product-form upper bound in relation form: for
`0 < m` and `x < m`, `e ^ x ≤ 1 / (1 - x/m) ^ m` (the inverse
of the shrinking base).  This is the `hi` shape used by the
numeric example below. -/
theorem exp_le_expUpper_inv {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : x < m) : Real.exp x ≤ 1 / (1 - x / m) ^ m := by
  have hmR : (0 : ℝ) < m := by positivity
  have hpos : (0 : ℝ) < 1 - x / m := by
    have h : x / m < 1 := by
      rw [div_lt_iff₀ hmR, one_mul]; exact hx
    linarith
  have h := exp_le_expUpper hm hx
  rw [le_div_iff₀ (pow_pos hpos m)]
  calc Real.exp x * (1 - x / m) ^ m
      = (1 - x / m) ^ m * Real.exp x := mul_comm _ _
    _ ≤ 1 := h

/-! ## Sandwich bounds: anti-monotonicity and the honest pin -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Anti-monotonicity in the competitors' logits: if one
competitor upper bound grows (`hi j ≤ hi' j`) while the
numerator is unchanged, the lower sandwich estimate of class
`v` shrinks (the denominator only grows).  Monotonicity of the
normalized estimate in its OWN logit is NOT claimed — numerator
and denominator move together there (module docstring). -/
theorem sandwich_lower_anti_mono {lo hi hi' : V → ℝ}
    (hlo0 : ∀ v, 0 < lo v) (hhi0 : ∀ v, 0 < hi v)
    (hhi'0 : ∀ v, 0 < hi' v)
    (hle : ∀ j, hi j ≤ hi' j) (v : V) :
    lo v / ∑ w, hi' w ≤ lo v / ∑ w, hi w := by
  have hsum : (0 : ℝ) < ∑ w, hi w :=
    Finset.sum_pos (fun w _ => hhi0 w) Finset.univ_nonempty
  have hsum' : (0 : ℝ) < ∑ w, hi' w :=
    Finset.sum_pos (fun w _ => hhi'0 w) Finset.univ_nonempty
  have hsumle : ∑ w, hi w ≤ ∑ w, hi' w :=
    Finset.sum_le_sum (fun j _ => hle j)
  rw [div_le_div_iff₀ hsum' hsum]
  exact mul_le_mul_of_nonneg_left hsumle (le_of_lt (hlo0 v))

/-- single-domain total lift: summing the pointwise
anti-monotonicity over ALL classes, the TOTAL lower sandwich
estimate inherits it — as long as the refinement touches only
the denominator walls (`hi ≤ hi'` pointwise from ONE band,
numerator `lo` FIXED).  This is the domain condition under
which summed `p̂`-monotonicity HOLDS; outside it the walls
move with the argument and the total need not be
anti-monotone (`band_mix_counterex` below).  Proof is the
induction-from-pointwise lift: `Finset.sum_le_sum` over
`sandwich_lower_anti_mono`. -/
theorem sum_phat_anti_mono_single_domain {lo hi hi' : V → ℝ}
    (hlo0 : ∀ v, 0 < lo v) (hhi0 : ∀ v, 0 < hi v)
    (hhi'0 : ∀ v, 0 < hi' v) (hle : ∀ j, hi j ≤ hi' j) :
    ∑ v, lo v / ∑ w, hi' w ≤ ∑ v, lo v / ∑ w, hi w := by
  exact Finset.sum_le_sum (fun v _ =>
    sandwich_lower_anti_mono hlo0 hhi0 hhi'0 hle v)

/-! ## The mixed-domain negative (counterexample, formalization) -/

/-- Bernoulli lower wall with `n = 1`: `loN1 x = 1 + x`. -/
noncomputable def loN1 (x : ℝ) : ℝ := 1 + x

/-- Bernoulli upper wall with `m = 3`: `hiM3 x = (1 - x/3)⁻³`,
valid (as an upper exp wall) for `x < 3`. -/
noncomputable def hiM3 (x : ℝ) : ℝ := 1 / (1 - x / 3) ^ 3

/-- The TOTAL lower sandwich estimate on `Fin 2` when the
walls MOVE with the logits: `totalLo z = ∑ v, loN1 (z v) /
∑ w, hiM3 (z w)`.  This is the mixed-domain object whose
anti-monotonicity FAILS (`band_mix_counterex`). -/
noncomputable def totalLo (z : Fin 2 → ℝ) : ℝ :=
  ∑ v, loN1 (z v) / ∑ w, hiM3 (z w)

/-- The negative, formalized: inside a fully
CERTIFIED band (`1 + x ≤ e ^ x ≤ (1 - x/3)⁻³` on every
logit), with nested logits `z ≤ z'` in the valid domain
`[0, 3)`, the total lower estimate can still GROW:
`z = (0, 2)` gives `totalLo z = 1/7`, `z' = (1, 2)` gives
`totalLo z' = 40/243`, and `1/7 < 40/243`.  The numerator
wall `loN1 (z v)` and the denominator contribution `hiM3
(z v)` rise together for the moving class, and the balance
depends on the companion logit — so no summed
anti-monotonicity theorem exists under these (weak,
pointwise-nested) hypotheses.  Together with
`sum_phat_anti_mono_single_domain` this CLOSES the pinned
open question with an exact characterization: summed `p̂`
anti-monotonicity holds exactly when the refinement moves
only the denominator walls of one band. -/
theorem band_mix_counterex :
    ∃ z z' : Fin 2 → ℝ,
      (∀ v, 0 ≤ z v) ∧ (∀ j, z j ≤ z' j) ∧ (∀ j, z' j < 3) ∧
      (∀ v, loN1 (z v) ≤ Real.exp (z v) ∧
        Real.exp (z v) ≤ hiM3 (z v)) ∧
      (∀ v, loN1 (z' v) ≤ Real.exp (z' v) ∧
        Real.exp (z' v) ≤ hiM3 (z' v)) ∧
      totalLo z < totalLo z' := by
  refine ⟨![0, 2], ![1, 2], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> norm_num
  · intro v; fin_cases v
    · constructor
      · have h := Real.add_one_le_exp 0
        norm_num [loN1] <;> linarith
      · exact exp_le_expUpper_inv (m := 3) (by norm_num) (by norm_num)
    · constructor
      · have h := Real.add_one_le_exp 2
        norm_num [loN1] <;> linarith
      · exact exp_le_expUpper_inv (m := 3) (by norm_num) (by norm_num)
  · intro v; fin_cases v
    · constructor
      · have h := Real.add_one_le_exp 1
        norm_num [loN1] <;> linarith
      · exact exp_le_expUpper_inv (m := 3) (by norm_num) (by norm_num)
    · constructor
      · have h := Real.add_one_le_exp 2
        norm_num [loN1] <;> linarith
      · exact exp_le_expUpper_inv (m := 3) (by norm_num) (by norm_num)
  · simp only [totalLo, loN1, hiM3, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- Direct negation of summed anti-monotonicity in the mixed
domain: under the weak hypotheses that suffice pointwise
(nonnegative nested logits inside the band `[0, 3)`), the
conclusion `totalLo z' ≤ totalLo z` is NOT derivable —
`band_mix_counterex` is a counterexample. -/
theorem phat_total_not_anti_mono :
    ¬ ∀ (z z' : Fin 2 → ℝ), (∀ v, 0 ≤ z v) → (∀ j, z j ≤ z' j) →
      (∀ j, z' j < 3) → totalLo z' ≤ totalLo z := by
  intro h
  obtain ⟨z, z', hz0, hle, hlt3, _, _, hlt⟩ := band_mix_counterex
  have hanti := h z z' hz0 hle hlt3
  linarith

/-! ## Certified prediction from disjoint sandwich intervals -/

/-- Disjoint sandwich intervals certify the TRUE softmax
ordering: `hi a / ∑ lo < lo b / ∑ hi` implies
`softDef z a < softDef z b` (three sandwich links:
upper bound of `a`, separation, lower bound of `b`). -/
theorem sandwich_gap_cert {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (a b : V)
    (hsep : hi a / ∑ w, lo w < lo b / ∑ w, hi w) :
    softDef z a < softDef z b := by
  have ⟨_, hha⟩ := rationalSoftmaxCert hlo hlo0 hhi a
  have ⟨hlb, _⟩ := rationalSoftmaxCert hlo hlo0 hhi b
  exact lt_of_le_of_lt hha (lt_of_lt_of_le hsep hlb)

/-- The rational midpoint of the certified sandwich interval
of class `v`. -/
noncomputable def sandwichMid (lo hi : V → ℝ) (v : V) : ℝ :=
  (lo v / ∑ w, hi w + hi v / ∑ w, lo w) / 2

/-- The midpoint surrogate is accurate to half the certified
interval width: `|sandwichMid lo hi v - softDef z v|` is
bounded by `(hi v / ∑ lo - lo v / ∑ hi) / 2` (directly from
`rationalSoftmaxCert`). -/
theorem sandwich_mid_acc {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (v : V) :
    |sandwichMid lo hi v - softDef z v| ≤
      (hi v / ∑ w, lo w - lo v / ∑ w, hi w) / 2 := by
  have ⟨hlow, hhigh⟩ := rationalSoftmaxCert hlo hlo0 hhi v
  unfold sandwichMid
  rw [abs_le]
  constructor <;> linarith

omit [Nonempty V] in
/-- Certified prediction via the canonical strict argmax: with
a uniform accuracy `ε` of the midpoint estimates against the
true softmax and a certified gap `2 * ε < softDef z b -
softDef z a` for every competitor `a`, the midpoint argmax
equals `b` (application of
`Hagi.Data.CertifiedArgmax.certified_argmax_strict`). -/
theorem certified_pred {z lo hi : V → ℝ} {ε : ℝ} {b : V}
    (hacc : ∀ a, |sandwichMid lo hi a - softDef z a| ≤ ε)
    (hgap : ∀ a, a ≠ b → 2 * ε < softDef z b - softDef z a) :
    ∀ a, a ≠ b → sandwichMid lo hi a < sandwichMid lo hi b :=
  Hagi.Data.CertifiedArgmax.certified_argmax_strict
    (v := softDef z) (est := sandwichMid lo hi) hacc (imax := b) hgap

/-- Certified prediction from pairwise disjointness, no `ε`:
if every competitor's upper sandwich endpoint is below the
predicted class's lower endpoint, then BOTH the true softmax
ordering and the midpoint-surrogate ordering certify `b` as
the argmax. -/
theorem certified_pred_sep {z lo hi : V → ℝ} {b : V}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v)
    (hsep : ∀ a, a ≠ b → hi a / ∑ w, lo w < lo b / ∑ w, hi w) :
    ∀ a, a ≠ b → softDef z a < softDef z b ∧
      sandwichMid lo hi a < sandwichMid lo hi b := by
  intro a ha
  have ⟨hla, hha⟩ := rationalSoftmaxCert hlo hlo0 hhi a
  have ⟨hlb, hhb⟩ := rationalSoftmaxCert hlo hlo0 hhi b
  have horder := sandwich_gap_cert hlo hlo0 hhi a b (hsep a ha)
  refine ⟨horder, ?_⟩
  unfold sandwichMid
  have h1 : lo a / ∑ w, hi w ≤ hi a / ∑ w, lo w := le_trans hla hha
  have h2 : lo b / ∑ w, hi w ≤ hi b / ∑ w, lo w := le_trans hlb hhb
  have h3 := hsep a ha
  linarith

/-! ## Numeric example: the sanity case is certified -/

/-- Powers of the sanity case `z = (0, 1, 2)`, `n = m = 10`,
as exact rationals: the lower bounds `(11/10) ^ 10` and
`(6/5) ^ 10` and the upper bounds `(10/9) ^ 10` and
`(5/4) ^ 10` (inverse form of the shrinking bases). -/
example : (11 / 10 : ℝ) ^ 10 = 25937424601 / 10000000000 := by norm_num

example : (6 / 5 : ℝ) ^ 10 = 60466176 / 9765625 := by norm_num

example : ((9 / 10 : ℝ)⁻¹) ^ 10 = 10000000000 / 3486784401 := by
  norm_num

example : ((8 / 10 : ℝ)⁻¹) ^ 10 = 9765625 / 1048576 := by
  norm_num

/-- First separation (classes 0 and 1): the upper endpoint of
class 0 (whose logit is 0, so both its bounds equal 1) is
strictly below the lower endpoint of class 1 — exact rational
certificates. -/
theorem sandwich_sep01 :
    (1 : ℝ) / (1 + 25937424601 / 10000000000
        + 60466176 / 9765625)
      < (25937424601 / 10000000000 : ℝ) / (1
        + 10000000000 / 3486784401 + 9765625 / 1048576) := by
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 1
      + 25937424601 / 10000000000 + 60466176 / 9765625)
      (by norm_num : (0 : ℝ) < 1 + 10000000000 / 3486784401
      + 9765625 / 1048576)]
  norm_num

/-- Second separation (classes 1 and 2): the upper endpoint of
class 1 is strictly below the lower endpoint of class 2 —
exact rational certificates. -/
theorem sandwich_sep12 :
    (10000000000 / 3486784401 : ℝ) / (1 + 25937424601 / 10000000000
        + 60466176 / 9765625)
      < (60466176 / 9765625 : ℝ) / (1
        + 10000000000 / 3486784401 + 9765625 / 1048576) := by
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 1
      + 25937424601 / 10000000000 + 60466176 / 9765625)
      (by norm_num : (0 : ℝ) < 1 + 10000000000 / 3486784401
      + 9765625 / 1048576)]
  norm_num

end Hagi.Theory.SandwichMonotone

/-! ## BandTightening — Bernoulli monotonicity in n and band tightening -/

namespace Hagi.Theory.BandTightening

open Real Hagi.Prelude Hagi.Theory.RationalSoftmax
  Hagi.Theory.SandwichMonotone Set

/-! ## The scalar MVT sign fact -/

/-- Helper: `log (1 + v) - v / (1 + v)`, whose sign governs
the derivative of `t ↦ t * log (1 + x / t)`. -/
noncomputable def auxG (v : ℝ) : ℝ := Real.log (1 + v) - v / (1 + v)

/-- The scalar sign fact: for `-1 < u`, `u ≠ 0`,
`log (1 + u) - u / (1 + u) > 0`.  Lagrange MVT on `[0, u]`
(or `[u, 0]`) for `auxG` with `auxG 0 = 0` and
`(auxG)′ v = v / (1 + v) ^ 2`: the interior point `c` lies
strictly between `0` and `u`, so `u * c > 0` and
`auxG u = c * u / (1 + c) ^ 2 > 0`. -/
theorem log_add_one_sub_div_pos {u : ℝ} (h1 : -1 < u)
    (h0 : u ≠ 0) : 0 < auxG u := by
  have hg0 : auxG 0 = 0 := by
    unfold auxG
    norm_num
  have hd : ∀ v, -1 < v → HasDerivAt auxG (v / (1 + v) ^ 2) v := by
    intro v hv
    have hne : (1 : ℝ) + v ≠ 0 := by linarith
    have ha : HasDerivAt (fun w => (1 : ℝ) + w) (1 : ℝ) v :=
      (hasDerivAt_const_add_iff 1).mpr (hasDerivAt_id v)
    have hb : HasDerivAt (fun w => Real.log ((1 : ℝ) + w))
        ((1 + v)⁻¹ * 1) v :=
      (Real.hasDerivAt_log hne).comp v ha
    have hc : HasDerivAt (fun w => w / ((1 : ℝ) + w))
        ((1 * (1 + v) - v * 1) / (1 + v) ^ 2) v :=
      (hasDerivAt_id v).div ha hne
    have hsum := hb.sub hc
    unfold auxG
    convert hsum using 1
    field_simp
    ring
  have hdiff : DifferentiableOn ℝ auxG (Ioi (-1 : ℝ)) := by
    intro v hv
    exact ((hd v hv).differentiableAt).differentiableWithinAt
  have hcontIoi : ContinuousOn auxG (Ioi (-1 : ℝ)) :=
    hdiff.continuousOn
  have hcont : ∀ a b : ℝ, -1 < a → ContinuousOn auxG (Icc a b) := by
    intro a b ha
    refine hcontIoi.mono ?_
    intro v hv
    simp only [mem_Icc] at hv
    simp only [mem_Ioi]
    exact lt_of_lt_of_le ha hv.1
  have hdioo : ∀ a b : ℝ, a < b → -1 < a →
      ∀ v ∈ Ioo a b, HasDerivAt auxG (v / (1 + v) ^ 2) v := by
    intro a b hab ha v hv
    simp only [mem_Ioo] at hv
    exact hd v (lt_of_lt_of_le ha (le_of_lt hv.1))
  rcases lt_or_gt_of_ne h0 with hun | hun
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope auxG
      (fun v => v / (1 + v) ^ 2) hun (hcont u 0 h1) (hdioo u 0 hun h1)
    rw [hg0] at hce
    have hc0 : c < 0 := hc.2
    have hc1 : -1 < c := lt_of_lt_of_le h1 (le_of_lt hc.1)
    have hs : (1 : ℝ) + c ≠ 0 := by linarith
    have hz : auxG u = c / (1 + c) ^ 2 * u := by
      rw [hce]
      field_simp
      ring
    have huc : (0 : ℝ) < u * c := mul_pos_of_neg_of_neg hun hc0
    rw [hz]
    have hfin : (0 : ℝ) < c * u / (1 + c) ^ 2 :=
      div_pos (by linarith : (0 : ℝ) < c * u) (by positivity)
    have heq : c / (1 + c) ^ 2 * u = c * u / (1 + c) ^ 2 := by
      field_simp
    linarith
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope auxG
      (fun v => v / (1 + v) ^ 2) hun (hcont 0 u (by norm_num))
      (hdioo 0 u hun (by norm_num))
    rw [hg0] at hce
    have hc0 : 0 < c := hc.1
    have hs : (1 : ℝ) + c ≠ 0 := by linarith
    have hz : auxG u = c / (1 + c) ^ 2 * u := by
      rw [hce]
      field_simp
      ring
    rw [hz]
    have hfin : (0 : ℝ) < c * u / (1 + c) ^ 2 :=
      div_pos (by positivity) (by positivity)
    have heq : c / (1 + c) ^ 2 * u = c * u / (1 + c) ^ 2 := by
      field_simp
    linarith

/-! ## Bernoulli monotonicity (the pin, closed) -/

/-- The Bernoulli sequence is nondecreasing: for `0 < n ≤ m`
and `-n ≤ x`, `(1 + x/n) ^ n ≤ (1 + x/m) ^ m`
lower rational exponential bound grows with its denominator.
Degenerate walls first (`x = -n`: left side `0`; `x = 0`:
both sides `1`), then Lagrange MVT for
`t ↦ t * log (1 + x * t⁻¹)` on `[n, m]`: the derivative at
the interior point is `auxG (x / c) > 0` unless `x = 0`. -/
theorem bernoulliLower_mono {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    {x : ℝ} (hx : -(n : ℝ) ≤ x) :
    (1 + x / n) ^ n ≤ (1 + x / m) ^ m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hn hnm)
  rcases eq_or_lt_of_le hx with hx | hx
  · -- degenerate wall: x = -n, left side 0
    subst hx
    have hn1 : (1 : ℝ) + -(n : ℝ) / n = 0 := by
      rw [neg_div, div_self hnR.ne']
      ring
    have hm1 : (0 : ℝ) ≤ 1 + -(n : ℝ) / m := by
      rw [neg_div]
      have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
      have hle : (n : ℝ) / m ≤ 1 := by
        rw [div_le_iff₀ hmR]
        linarith
      linarith
    rw [hn1, zero_pow hn.ne']
    exact pow_nonneg hm1 m
  rcases eq_or_lt_of_le hnm with heq | hlt
  · subst heq
    exact le_rfl
  rcases eq_or_ne x 0 with hx0 | hx0
  · -- x = 0: both sides 1
    simp only [hx0, zero_div, add_zero, one_pow]
    exact le_rfl
  -- strict case: -n < x, n < m, x ≠ 0
  have hbn : (0 : ℝ) < 1 + x / n := by
    have h1 : -1 < x / n := by
      rw [lt_div_iff₀ hnR]
      have hmul : (-1 : ℝ) * n = -n := by ring
      rw [hmul]
      exact hx
    linarith
  have hbm : (0 : ℝ) < 1 + x / m := by
    have h1 : -1 < x / m := by
      rw [lt_div_iff₀ hmR]
      have hmul : (-1 : ℝ) * m = -m := by ring
      rw [hmul]
      have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith
    linarith
  have hcx : x ≠ 0 := hx0
  -- MVT for F t = t * log (1 + x * t⁻¹) on [n, m]
  set F : ℝ → ℝ := fun t => t * Real.log (1 + x * t⁻¹) with hF
  have hFd : ∀ t, (0 : ℝ) < t → -t < x →
      HasDerivAt F (Real.log (1 + x * t⁻¹)
        - (x * t⁻¹) / (1 + x * t⁻¹)) t := by
    intro t ht htx
    have ht1 : -1 < x * t⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ ht]
      have hmul : (-1 : ℝ) * t = -t := by ring
      rw [hmul]
      exact htx
    have hpos : (0 : ℝ) < 1 + x * t⁻¹ := by linarith
    have hne : (1 : ℝ) + x * t⁻¹ ≠ 0 := by linarith
    have htne : t ≠ 0 := ht.ne'
    have hinv : HasDerivAt (fun s => x * s⁻¹)
        (x * (-(t ^ 2)⁻¹)) t :=
      (hasDerivAt_inv htne).const_mul x
    have hadd : HasDerivAt (fun s => (1 : ℝ) + x * s⁻¹)
        (x * (-(t ^ 2)⁻¹)) t :=
      (hasDerivAt_const_add_iff 1).mpr hinv
    have hlog : HasDerivAt (fun s => Real.log (1 + x * s⁻¹))
        ((1 + x * t⁻¹)⁻¹ * (x * (-(t ^ 2)⁻¹))) t := by
      have h := (Real.hasDerivAt_log hne).comp t hadd
      simpa only [Function.comp_def] using h
    have hmulD := (hasDerivAt_id t).mul hlog
    convert hmulD using 1
    · rfl
    field_simp
    simp only [id_eq]
    ring
  have hFcont : ContinuousOn F (Icc (n : ℝ) (m : ℝ)) := by
    have hnx : (-x : ℝ) < n := by linarith
    have hdiff : DifferentiableOn ℝ F (Ioi (max 0 (-x))) := by
      intro t ht
      simp only [mem_Ioi] at ht
      have ht0 : (0 : ℝ) < t :=
        lt_of_le_of_lt (le_max_left 0 (-x)) ht
      have htx : -t < x := by
        have h1 : -x < t := lt_of_le_of_lt (le_max_right 0 (-x)) ht
        linarith
      exact ((hFd t ht0 htx).differentiableAt).differentiableWithinAt
    refine (hdiff.continuousOn).mono ?_
    intro t ht
    simp only [mem_Icc] at ht
    simp only [mem_Ioi, max_lt_iff]
    have ht0 : (0 : ℝ) < t :=
      lt_of_lt_of_le hnR ht.1
    have htx : -x < t := lt_of_lt_of_le hnx ht.1
    exact ⟨ht0, htx⟩
  have hFdioo : ∀ t ∈ Ioo ((n : ℝ)) ((m : ℝ)),
      HasDerivAt F (Real.log (1 + x * t⁻¹)
        - (x * t⁻¹) / (1 + x * t⁻¹)) t := by
    intro t ht
    simp only [mem_Ioo] at ht
    refine hFd t (by linarith) ?_
    linarith
  obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope F
    (fun t => Real.log (1 + x * t⁻¹)
      - (x * t⁻¹) / (1 + x * t⁻¹)) (by exact_mod_cast hlt)
    hFcont hFdioo
  simp only [mem_Ioo] at hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hcx1 : -c < x := by
    have h1 : -((n : ℝ)) < x := by linarith
    linarith
  have hu0 : x * c⁻¹ ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hcx, (inv_ne_zero (ne_of_gt hcpos))⟩
  have hune : -1 < x * c⁻¹ := by
    rw [← div_eq_mul_inv, lt_div_iff₀ hcpos]
    have hmul : (-1 : ℝ) * c = -c := by ring
    rw [hmul]
    exact hcx1
  have hgd : (0 : ℝ) < auxG (x * c⁻¹) :=
    log_add_one_sub_div_pos hune hu0
  have hba : (m : ℝ) - (n : ℝ) ≠ 0 := by
    have : ((n : ℝ) < m) := by exact_mod_cast hlt
    linarith
  have hFz : F (m : ℝ) - F ((n : ℝ))
      = ((m : ℝ) - (n : ℝ)) * auxG (x * c⁻¹) := by
    have h4 := hce
    unfold auxG
    rw [h4]
    field_simp
  have hFmono : F ((n : ℝ)) < F ((m : ℝ)) := by
    have h1 : (0 : ℝ) < (m : ℝ) - (n : ℝ) := by
      have : ((n : ℝ) < m) := by exact_mod_cast hlt
      linarith
    have h2 : (0 : ℝ) < ((m : ℝ) - (n : ℝ))
        * auxG (x * c⁻¹) :=
      mul_pos h1 hgd
    linarith
  -- lift through log/exp
  have hpn : (0 : ℝ) < (1 + x / n) ^ n := pow_pos hbn n
  have hpm : (0 : ℝ) < (1 + x / m) ^ m := pow_pos hbm m
  rw [← Real.exp_log hpn, ← Real.exp_log hpm,
    Real.log_pow, Real.log_pow, Real.exp_le_exp]
  rw [hF] at hFmono
  simp only [] at hFmono
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at hFmono
  exact hFmono.le

/-- The upper bound base INCREASES: for `0 < m ≤ k` and
`x < m`, `(1 - x/m) ^ m ≤ (1 - x/k) ^ k` — so the upper
rational wall `(1 - x/m) ^ (-m)` of the sandwich
SHRINKS as `m` grows (its denominator grows)
(`bernoulliLower_mono` at `-x`; the premise `-m ≤ -x` is
`x ≤ m`, implied by `x < m`). -/
theorem expUpper_base_mono {m k : ℕ} (hm : 0 < m)
    (hmk : m ≤ k) {x : ℝ} (hx : x < m) :
    (1 - x / m) ^ m ≤ (1 - x / k) ^ k := by
  have h1 : (1 : ℝ) - x / k = 1 + (-x) / k := by ring
  have h2 : (1 : ℝ) - x / m = 1 + (-x) / m := by ring
  rw [h1, h2]
  have hxk : -((m : ℝ)) ≤ -x := by
    have hxm : (x : ℝ) < m := by exact_mod_cast hx
    linarith
  exact bernoulliLower_mono hm hmk hxk

/-! ## Band width monotonicity and adaptive calibration -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- The normalized certified band width of class `v` in the
 bench: the width of the sandwich interval
`[lo v / ∑ hi, hi v / ∑ lo]`. -/
noncomputable def bandWidth (lo hi : V → ℝ) (v : V) : ℝ :=
  hi v / ∑ w, lo w - lo v / ∑ w, hi w

/-- Tighter rational walls give narrower certified bands:
with `lo ≤ lo'` and `hi' ≤ hi` pointwise (all positive), the
refined band width `bandWidth lo' hi' v` never exceeds the
coarse one `bandWidth lo hi v`. -/
theorem bandWidth_mono {lo hi lo' hi' : V → ℝ}
    (hlo0 : ∀ v, 0 < lo v) (hlo'0 : ∀ v, 0 < lo' v)
    (hhi0 : ∀ v, 0 < hi v) (hhi'0 : ∀ v, 0 < hi' v)
    (h1 : ∀ v, lo v ≤ lo' v) (h3 : ∀ v, hi' v ≤ hi v)
    (v : V) :
    bandWidth lo' hi' v ≤ bandWidth lo hi v := by
  have hslo : (0 : ℝ) < ∑ w, lo w :=
    Finset.sum_pos (fun w _ => hlo0 w) Finset.univ_nonempty
  have hslo' : (0 : ℝ) < ∑ w, lo' w :=
    Finset.sum_pos (fun w _ => hlo'0 w) Finset.univ_nonempty
  have hshi : (0 : ℝ) < ∑ w, hi w :=
    Finset.sum_pos (fun w _ => hhi0 w) Finset.univ_nonempty
  have hshi' : (0 : ℝ) < ∑ w, hi' w :=
    Finset.sum_pos (fun w _ => hhi'0 w) Finset.univ_nonempty
  have hs1 : ∑ w, lo w ≤ ∑ w, lo' w :=
    Finset.sum_le_sum (fun j _ => h1 j)
  have hs3 : ∑ w, hi' w ≤ ∑ w, hi w :=
    Finset.sum_le_sum (fun j _ => h3 j)
  have ht1 : hi' v / ∑ w, lo' w ≤ hi v / ∑ w, lo w := by
    rw [div_le_div_iff₀ hslo' hslo]
    exact mul_le_mul (h3 v) hs1 hslo.le (hhi0 v).le
  have ht2 : lo v / ∑ w, hi w ≤ lo' v / ∑ w, hi' w := by
    rw [div_le_div_iff₀ hshi hshi']
    exact mul_le_mul (h1 v) hs3 hshi'.le (hlo'0 v).le
  unfold bandWidth
  linarith

/-- Adaptive calibration theorem: if every class's certified
band is at most `2 * ε` wide (`bandWidth / 2 ≤ ε`), then any
true softmax gap strictly above `2 * ε` certifies the
midpoint argmax — how much denominator precision `n, m` must
buy for a certified prediction. -/
theorem cert_pred_adaptive {z lo hi : V → ℝ} {ε : ℝ} {b : V}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v)
    (hε : ∀ v, bandWidth lo hi v / 2 ≤ ε)
    (hgap : ∀ a, a ≠ b → 2 * ε < softDef z b - softDef z a) :
    ∀ a, a ≠ b → sandwichMid lo hi a < sandwichMid lo hi b := by
  refine certified_pred ?_ hgap
  intro a
  have hacc := sandwich_mid_acc hlo hlo0 hhi a
  have hwa := hε a
  unfold bandWidth at hwa
  obtain ⟨hl1, hl2⟩ := abs_le.mp hacc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Refinement preserves certification: if the calibration
premise `cert_pred_adaptive` holds for the coarse walls
`(lo, hi)` at level `ε`, and the refined walls `(lo', hi')`
are only tighter in the `bandWidth_mono` sense while still
sandwiching the truth, the same `ε` certifies at
`(lo', hi')` — doubling `n, m` never un-certifies. -/
theorem cert_pred_adaptive_mono {z lo hi lo' hi' : V → ℝ}
    {ε : ℝ} {b : V}
    (hlo' : ∀ v, lo' v ≤ Real.exp (z v))
    (hlo'0 : ∀ v, 0 < lo' v)
    (hhi' : ∀ v, Real.exp (z v) ≤ hi' v)
    (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) (hhi'0 : ∀ v, 0 < hi' v)
    (h1 : ∀ v, lo v ≤ lo' v) (h3 : ∀ v, hi' v ≤ hi v)
    (hε : ∀ v, bandWidth lo hi v / 2 ≤ ε)
    (hgap : ∀ a, a ≠ b → 2 * ε < softDef z b - softDef z a) :
    ∀ a, a ≠ b → sandwichMid lo' hi' a < sandwichMid lo' hi' b := by
  have hhi0 : ∀ v, 0 < hi v := fun v =>
    lt_of_lt_of_le (Real.exp_pos (z v)) (hhi v)
  refine cert_pred_adaptive hlo' hlo'0 hhi' ?_ hgap
  intro v
  have hmono := bandWidth_mono hlo0 hlo'0 hhi0 hhi'0 h1 h3 v
  have he := hε v
  unfold bandWidth at hmono he
  unfold bandWidth
  linarith

/-! ## Numeric sanity -/

/-- Bernoulli sanity from the bench shape: the max-shift
lower bounds tighten from `n = 4` to `n = 8` at `x = -2`
(`(1/2) ^ 4 ≤ (3/4) ^ 8`), an instance of the closed pin. -/
example : (1 + (-(2 : ℝ)) / 4) ^ 4 ≤ (1 + (-(2 : ℝ)) / 8) ^ 8 :=
  bernoulliLower_mono (by norm_num) (by norm_num) (by norm_num)

/-- Upper wall sanity: `(1 - 2/4) ^ 4 ≤ (1 - 2/8) ^ 8` — the
upper bound base grows as `m` goes from `4` to `8`, so the
reciprocal wall shrinks. -/
example : (1 - (2 : ℝ) / 4) ^ 4 ≤ (1 - (2 : ℝ) / 8) ^ 8 :=
  expUpper_base_mono (m := 4) (by norm_num) (by norm_num)
    (by norm_num)

end Hagi.Theory.BandTightening


/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.RationalSoftmax
import Hagi.Cert.CertifiedArgmax
import Mathlib.Tactic

/-!
# Sandwich monotonicity and certified prediction

Roadmap C495, closing the C489 pin "Bernoulli-монотонность не
доказана" in the honest direction: the BOUNDS of the C489
certified softmax sandwich are monotone in their own logit
variable, and a disjointness condition on the sandwich
intervals certifies the argmax (the prediction) — both the true
softmax ordering and the ordering of the rational midpoint
surrogate.

## Monotonicity of the exponential bounds

For fixed `n`, `0 < n`, `x ≤ x'`, `-n ≤ x`:

* `expLower_mono` : `(1 + x/n) ^ n ≤ (1 + x'/n) ^ n`
* `expUpper_mono` : `(1 - x'/m) ^ m ≤ (1 - x/m) ^ m` (`x' < m`)
* `exp_le_expUpper_inv` : `e ^ x ≤ 1 / (1 - x/m) ^ m`

The base `1 + x/n` is monotone in `x` and stays nonnegative,
then `pow_le_pow_left₀` lifts the monotonicity to the power.
This is monotonicity in the LOGIT, not the Bernoulli
monotonicity in `n` (accuracy growth with `n`, m) — that pin
of C489 remains open.

## Honest negative

The NORMALIZED sandwich estimate `lo v / ∑ hi` is NOT claimed
monotone in its own logit `z v`: the numerator `lo v` and the
denominator contribution `hi v` grow together with `z v`, so
no total monotonicity follows from the bound monotonicity.
What does hold is anti-monotonicity in the OTHER logits
(`sandwich_lower_anti_mono`): a larger competitor bound shrinks
the lower estimate through the denominator.

## Certified prediction

If the sandwich intervals of two classes are disjoint,

`hi a / ∑ lo < lo b / ∑ hi`,

then `sandwich_gap_cert` gives the true ordering
`softDef z a < softDef z b` (three sandwich links).  The
midpoint surrogate `sandwichMid v = (lo v / ∑ hi +
hi v / ∑ lo) / 2` is `sandwich_mid_acc`-accurate to half the
interval width, so `certified_pred` — an application of
`Hagi.Data.CertifiedArgmax.certified_argmax_strict` with a
uniform accuracy `ε` — recovers the certified argmax, and
`certified_pred_sep` derives the same certification directly
from pairwise disjointness.  The numeric example
`sandwich_disjoint_example` instantiates the C489 sanity case
`z = (0, 1, 2)`, `n = m = 10`: both separations hold with
exact rationals, so the prediction (class 2) is certified.
-/

set_option linter.style.header false

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

/-- The C489 product-form upper bound in relation form: for
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

/-! ## Numeric example: the C489 sanity case is certified -/

/-- Powers of the sanity case `z = (0, 1, 2)`, `n = m = 10`,
as exact rationals: the lower bounds `(11/10) ^ 10` and
`(6/5) ^ 10` and the upper bounds `(10/9) ^ 10` and
`(5/4) ^ 10` (inverse form of the C489 shrinking bases). -/
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

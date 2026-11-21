/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.SandwichMonotone
import Mathlib.Tactic

/-!
# Adaptive sandwich band tightening

Roadmap C502, top-1 of the C501 roadmap: the C489/C497
certified softmax sandwich `(1 + x/n) ^ n ≤ e ^ x` tightens
as the denominators `n, m` GROW.  This module closes the
long-standing C489 pin "Bernoulli-монотонность не доказана":
`(1 + x/n) ^ n` is nondecreasing in `n` (the Bernoulli
sequence), proved here by a Lagrange mean value argument on
`t ↦ t * log (1 + x / t)`; the sign step is the scalar fact
`log (1 + u) - u / (1 + u) > 0` for `-1 < u ≠ 0`.

## Bernoulli monotonicity (the C489 pin, closed)

* `log_add_one_sub_div_pos` : the scalar MVT sign fact.
* `bernoulliLower_mono` : `0 < n ≤ m`, `-n ≤ x` imply
  `(1 + x/n) ^ n ≤ (1 + x/m) ^ m` — the lower rational
  exponential bound INCREASES with the denominator.
* `expUpper_base_mono` : `0 < m ≤ k`, `x < m` imply
  `(1 - x/m) ^ m ≤ (1 - x/k) ^ k` — the upper bound base
  INCREASES, so the reciprocal upper bound shrinks as the
  denominator grows: both sandwich walls move in, the
  certified band tightens.

## Band width monotonicity and adaptive calibration

* `bandWidth` : the normalized certified band width
  `hi v / ∑ lo - lo v / ∑ hi` of the C495/C497 bench.
* `bandWidth_mono` : if `lo ≤ lo'` and `hi' ≤ hi` pointwise
  (with `lo' ≤ e ^ · ≤ hi'` sandwiched), the refined band is
  never wider than the coarse one.
* `cert_pred_adaptive` : calibration theorem — with a uniform
  half-width bound `bandWidth / 2 ≤ ε` and true softmax gaps
  `2ε < softDef z b - softDef z a`, the rational midpoint
  argmax certifies `b` (application of the C495
  `certified_pred` with the accuracy from
  `sandwich_mid_acc`).
* `cert_pred_adaptive_mono` : band refinement (`bandWidth`
  only shrinking) preserves an existing certification — the
  certificate is monotone under doubling `n, m`.

## Numeric sanity

`bernoulliExample`: `(1 - 2/4) ^ 4 ≤ (1 - 2/8) ^ 8` — the
max-shifted lower bounds of the C497 bench tighten from
`n = 4` to `n = 8` by the closed Bernoulli pin.

## Honest pins

1. The Python side (`--mode vs-trainer`, C502 update) doubles
   `n = m` at EVALUATION time only (training certificate
   unchanged); whether bands actually separate is a property
   of the trained model, not a theorem.
2. `expUpper_base_mono` is `bernoulliLower_mono` at `-x`;
   no independent upper-wall calculus is needed.
-/

set_option linter.style.header false

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

/-! ## Bernoulli monotonicity (the C489 pin, closed) -/

/-- The Bernoulli sequence is nondecreasing: for `0 < n ≤ m`
and `-n ≤ x`, `(1 + x/n) ^ n ≤ (1 + x/m) ^ m` — the C489
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
rational wall `(1 - x/m) ^ (-m)` of the C489 sandwich
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
C495/C497 bench: the width of the sandwich interval
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

/-- Bernoulli sanity from the C497 bench shape: the max-shift
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

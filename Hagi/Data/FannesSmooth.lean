/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.AntiCollapse
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# FannesSmooth: entropy continuity in the non-singular regime (R157 remainder, part 2)

The FULL Fannes bound `|H(p) − H(q)| ≤ τ·log(V−1) + h₂(τ)`
remains open (the singular h₂ term needs the zero-mass
rearrangement machinery absent from Mathlib). This module
closes the SMOOTH part of the remainder: on the interior of
the simplex (both distributions δ-separated from the
boundary), entropy is Lipschitz in total variation with an
EXPLICIT constant — via the mean-value bound for log.

**Results.**

* `abs_log_sub_le` — the log increment bound:
  `|log a − log b| ≤ |a − b| / min a b` for positive `a, b`.

* `entropy_lipschitz_smooth` — SMOOTH FANNES: for
  probability vectors `p, q` on `V` with all masses in
  `[δ, 1]` (δ > 0),

  `|H(p) − H(q)| ≤ (2/δ + 2·log(1/δ)) · TV(p, q)`.

  Combined with the Pinsker routing already in the corpus
  (R157 part 1), the Fannes program is complete EXCEPT the
  singular-boundary h₂ term — the honest boundary, unchanged.
-/

namespace Hagi.Data

open Finset Real

variable {V : Type} [Fintype V] [Nonempty V]

/-- The entropy of a probability vector. -/
noncomputable def ent (p : V → ℝ) : ℝ := -∑ v, p v * Real.log (p v)

/-- R198 prelude bridge: ent IS the canonical Prelude.entDef. -/
theorem ent_eq_entDef (p : V → ℝ) : ent p = Hagi.Prelude.entDef p := rfl

/-- Total variation distance (half-L1). -/
noncomputable def tvDist (p q : V → ℝ) : ℝ := (∑ v, |p v - q v|) / 2

/-- R198 prelude bridge: tvDist IS the canonical Prelude.tvDef. -/
theorem tvDist_eq_tvDef (p q : V → ℝ) : tvDist p q = Hagi.Prelude.tvDef p q := rfl

/-- **The log increment bound**: for positive `a ≤ b`,
`log b − log a ≤ (b − a)/a` (the mean-value bound for log);
symmetrically, `|log a − log b| ≤ |a − b| / min a b`. -/
theorem log_sub_le_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hle : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  rw [← Real.log_div (ne_of_gt hb) (ne_of_gt ha),
    show (b - a) / a = b / a - 1 from by field_simp]
  exact Real.log_le_sub_one_of_pos (div_pos hb ha)

theorem abs_log_sub_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  rcases le_total a b with hab | hba
  · have hmin : min a b = a := min_eq_left hab
    rw [hmin]
    have habs : |b - a| = b - a := abs_of_nonneg (sub_nonneg_of_le hab)
    have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    have habsl : |Real.log a - Real.log b| = Real.log b - Real.log a := by
      rw [abs_of_nonpos (by have : Real.log b - Real.log a ≥ 0 := sub_nonneg.mpr h1; linarith)]
      ring
    rw [habsl]
    calc Real.log b - Real.log a ≤ (b - a) / a := log_sub_le_div a b ha hb hab
      _ = |b - a| / a := by rw [habs]
      _ = |a - b| / a := by rw [abs_sub_comm]
  · have hmin : min a b = b := min_eq_right hba
    rw [hmin]
    have habs : |a - b| = a - b := abs_of_nonneg (sub_nonneg_of_le hba)
    have h1 : Real.log b ≤ Real.log a := Real.log_le_log hb hba
    have habsl : |Real.log a - Real.log b| = Real.log a - Real.log b := by
      rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    rw [habsl]
    calc Real.log a - Real.log b ≤ (a - b) / b := log_sub_le_div b a hb ha hba
      _ = |a - b| / b := by rw [habs]

/-- **Smooth Fannes**: on the δ-interior of the simplex the
entropy is Lipschitz in total variation with the explicit
constant `2/δ + 2·log(1/δ)` — the non-singular half of the
Fannes program. The singular h₂ term (zero-mass boundary)
remains open, as documented. -/
theorem entropy_lipschitz_smooth (p q : V → ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1)
    (hp : ∀ v, delta ≤ p v) (hq : ∀ v, delta ≤ q v)
    (hp1 : ∀ v, p v ≤ 1) (hq1 : ∀ v, q v ≤ 1) :
    |ent p - ent q| ≤ (2 / delta + 2 * Real.log (1 / delta)) * tvDist p q := by
  -- the log magnitude bound on the interior
  have hlogb : ∀ v, |Real.log (q v)| ≤ Real.log (1 / delta) := by
    intro v
    have hqpos : 0 < q v := lt_of_lt_of_le hdelta (hq v)
    have hle1 : Real.log (q v) ≤ 0 := by
      have := Real.log_le_log hqpos (hq1 v)
      simpa using this
    have hge : Real.log delta ≤ Real.log (q v) :=
      Real.log_le_log hdelta (hq v)
    have hinv : Real.log (1 / delta) = -Real.log delta := by
      have h1 : (1 / delta) = delta⁻¹ := one_div delta
      rw [h1]
      exact Real.log_inv delta
    rw [abs_of_nonpos hle1, hinv]
    linarith
  -- the decomposition: ent p - ent q = sum (q-p) log q + sum p (log q - log p)
  have hdecomp : ent p - ent q
      = (∑ v, (q v - p v) * Real.log (q v))
        + (∑ v, p v * (Real.log (q v) - Real.log (p v))) := by
    unfold ent
    rw [neg_sub_neg (a := ∑ v, p v * Real.log (p v)) (b := ∑ v, q v * Real.log (q v)),
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hdecomp]
  -- the two components
  set L := ∑ v, |q v - p v| with hL
  have hA : |∑ v, (q v - p v) * Real.log (q v)| ≤ Real.log (1 / delta) * L := by
    calc |∑ v, (q v - p v) * Real.log (q v)|
        ≤ ∑ v, |(q v - p v) * Real.log (q v)| :=
          Finset.abs_sum_le_sum_abs (fun v => (q v - p v) * Real.log (q v)) Finset.univ
      _ ≤ ∑ v, |q v - p v| * Real.log (1 / delta) := by
          refine Finset.sum_le_sum fun v _ => ?_
          calc |(q v - p v) * Real.log (q v)| ≤ |q v - p v| * |Real.log (q v)| :=
                (abs_mul _ _).le
            _ ≤ |q v - p v| * Real.log (1 / delta) :=
                mul_le_mul_of_nonneg_left (hlogb v) (abs_nonneg _)
      _ = Real.log (1 / delta) * L := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  have hstep : ∀ v : V,
      |q v - p v| / min (p v) (q v) ≤ |q v - p v| / delta := by
    intro v
    have hp0 : 0 < p v := lt_of_lt_of_le hdelta (hp v)
    have hq0 : 0 < q v := lt_of_lt_of_le hdelta (hq v)
    have hm : delta ≤ min (p v) (q v) := le_min (hp v) (hq v)
    have hmin0 : 0 < min (p v) (q v) := by positivity
    rw [div_le_div_iff₀ hmin0 hdelta]
    nlinarith [abs_nonneg (q v - p v)]
  have hB : ∑ v, p v * |Real.log (q v) - Real.log (p v)| ≤ (1 / delta) * L := by
    calc ∑ v, p v * |Real.log (q v) - Real.log (p v)|
        ≤ ∑ v, p v * (|q v - p v| / min (p v) (q v)) := by
          refine Finset.sum_le_sum fun v _ => ?_
          refine le_trans (mul_le_mul_of_nonneg_left
            (abs_log_sub_le (q v) (p v) (lt_of_lt_of_le hdelta (hq v))
              (lt_of_lt_of_le hdelta (hp v))) (le_trans hdelta.le (hp v))) ?_
          rw [min_comm]
      _ ≤ ∑ v, p v * (|q v - p v| / delta) := by
          refine Finset.sum_le_sum fun v _ => ?_
          exact mul_le_mul_of_nonneg_left (hstep v) (le_trans hdelta.le (hp v))
      _ ≤ (1 / delta) * L := by
          have hsum : ∑ v, p v * (|q v - p v| / delta)
              ≤ ∑ v, (1:ℝ) * (|q v - p v| / delta) := by
            refine Finset.sum_le_sum fun v _ => ?_
            exact mul_le_mul_of_nonneg_right (hp1 v) (by positivity)
          have hsimp : ∑ v, (1:ℝ) * (|q v - p v| / delta)
              = (1 / delta) * ∑ v, |q v - p v| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun v _ => by ring
          exact le_trans hsum (by rw [hL]; exact le_of_eq hsimp)
  -- combine
  have hsplit : (2 / delta + 2 * Real.log (1 / delta)) * tvDist p q
      = Real.log (1 / delta) * L + (1 / delta) * L := by
    rw [tvDist, hL]
    field_simp
    simp only [abs_sub_comm]
    ring
  calc |∑ v, (q v - p v) * Real.log (q v)
        + ∑ v, p v * (Real.log (q v) - Real.log (p v))|
      ≤ |∑ v, (q v - p v) * Real.log (q v)|
        + |∑ v, p v * (Real.log (q v) - Real.log (p v))| :=
          abs_add_le _ _
    _ ≤ |∑ v, (q v - p v) * Real.log (q v)|
        + ∑ v, p v * |Real.log (q v) - Real.log (p v)| := by
          refine add_le_add (le_refl _) ?_
          refine le_trans (Finset.abs_sum_le_sum_abs
            (fun v => p v * (Real.log (q v) - Real.log (p v))) Finset.univ) ?_
          refine Finset.sum_le_sum fun v _ => ?_
          rw [abs_mul, abs_of_nonneg (le_trans hdelta.le (hp v))]
    _ ≤ Real.log (1 / delta) * L + (1 / delta) * L := add_le_add hA hB
    _ = (2 / delta + 2 * Real.log (1 / delta)) * tvDist p q := hsplit.symm

end Hagi.Data

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.PoEBound

set_option relaxedAutoImplicit false

/-!
# The logit-gradient carrier and its row facts

`logitGrad` is the per-context row of the logit-gradient matrix of the
cross-entropy loss: `softmax (z c) − N c`, where `N c` is the empirical
next-token distribution for context `c` (one-hot target or frequencies).
It generalizes the single-context residual shape of `ceResidual`
(Model/CEDescent) to arbitrary sub-probability `N`.

The carrier is a plain function `C → V → ℝ`; the square complex matrix
view needed by the Flywheel SVD API is built only in
`Hagi.Contracts.GradientBottleneck`.

Main results (row facts, all from existing `Hagi.Energy.smax` lemmas):

* `logitGrad_row_sum_zero` — rows sum to zero when `N` rows are
  probability vectors.
* `logitGrad_pos_off_target` — off the one-hot target the gradient is
  strictly positive.
* `smax_lt_one` — a single softmax entry is below one whenever another
  token exists (the only genuinely new row-level lemma).
* `logitGrad_neg_at_target` — at the one-hot target the gradient is
  strictly negative, provided another token exists. The `∃ w ≠ t c`
  premise is an explicit data premise: with singleton vocabulary
  softmax is identically one and the target entry is zero, not
  negative.
* `abs_logitGrad_row_le_two` — each row carries absolute mass at most
  two for sub-probability `N` (nonnegative entries, row sum ≤ 1).
-/

open scoped BigOperators

namespace Hagi.Contracts.LogitGrad

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
variable {C : Type} [DecidableEq C]

/-- Softmax-then-subtract: per-context row of the logit-gradient
matrix, `smax (z c) − N c`, with `N c` the empirical next-token
distribution (one-hot or frequencies) for context `c`. -/
noncomputable def logitGrad (z : C → V → ℝ) (N : C → V → ℝ)
    (c : C) (v : V) : ℝ :=
  Hagi.Energy.smax (z c) v - N c v

/-- Row sums vanish when `N` rows are probability vectors. -/
theorem logitGrad_row_sum_zero (z : C → V → ℝ) (N : C → V → ℝ)
    (hN : ∀ c, ∑ v, N c v = 1) (c : C) :
    ∑ v, logitGrad z N c v = 0 := by
  simp only [logitGrad]
  rw [Finset.sum_sub_distrib, Hagi.Energy.smax_sum_one, hN c]
  ring

/-- Off the empirical one-hot target the logit gradient is strictly
positive. -/
theorem logitGrad_pos_off_target (z : C → V → ℝ) (t : C → V)
    (c : C) {v : V} (hvt : v ≠ t c) :
    0 < logitGrad z (fun c' v' => if v' = t c' then 1 else 0) c v := by
  show 0 < Hagi.Energy.smax (z c) v
        - (if v = t c then (1:ℝ) else 0)
  rw [ite_eq_right (fun h => hvt h), sub_zero]
  exact Hagi.Energy.smax_pos (z c) v

/-- A single softmax entry is strictly below one whenever some other
token exists. -/
theorem smax_lt_one (x : V → ℝ) {v : V} (hw : ∃ w, w ≠ v) :
    Hagi.Energy.smax x v < 1 := by
  obtain ⟨w, hwv⟩ := hw
  have hsum : Hagi.Energy.smax x v + Hagi.Energy.smax x w
      ≤ ∑ u ∈ Finset.univ, Hagi.Energy.smax x u :=
    Finset.add_le_sum
      (fun u _ => Hagi.Energy.smax_nonneg x u)
      (Finset.mem_univ v) (Finset.mem_univ w) hwv.symm
  rw [Hagi.Energy.smax_sum_one] at hsum
  have : Hagi.Energy.smax x w > 0 := Hagi.Energy.smax_pos x w
  linarith

/-- At the empirical one-hot target the logit gradient is strictly
negative, provided another token exists (explicit data premise;
singleton vocabulary makes the entry zero instead). -/
theorem logitGrad_neg_at_target (z : C → V → ℝ) (t : C → V)
    (c : C) (hw : ∃ w : V, w ≠ t c) :
    logitGrad z (fun c' v' => if v' = t c' then 1 else 0) c (t c) < 0 := by
  show Hagi.Energy.smax (z c) (t c)
        - (if (t c) = t c then (1:ℝ) else 0) < 0
  rw [ite_eq_left (rfl : (t c) = t c)]
  have : Hagi.Energy.smax (z c) (t c) < 1 := smax_lt_one (z c) hw
  linarith

/-- Each row of the logit gradient carries absolute mass at most two
for sub-probability `N` (nonnegative entries, row sum at most one). -/
theorem abs_logitGrad_row_le_two (z : C → V → ℝ) (N : C → V → ℝ)
    (hN0 : ∀ c v, 0 ≤ N c v) (hN1 : ∀ c, ∑ v, N c v ≤ 1) (c : C) :
    ∑ v, |logitGrad z N c v| ≤ 2 := by
  have h1 : ∀ v : V, |logitGrad z N c v|
      ≤ Hagi.Energy.smax (z c) v + N c v := by
    intro v
    exact abs_sub_le_iff.mpr ⟨by
      linarith [Hagi.Energy.smax_nonneg (z c) v, hN0 c v],
      by linarith [Hagi.Energy.smax_nonneg (z c) v, hN0 c v]⟩
  calc ∑ v, |logitGrad z N c v|
      ≤ ∑ v, (Hagi.Energy.smax (z c) v + N c v) :=
        Finset.sum_le_sum fun v _ => h1 v
    _ = 1 + ∑ v, N c v := by
        rw [Finset.sum_add_distrib, Hagi.Energy.smax_sum_one]
    _ ≤ 2 := by linarith [hN1 c]

end Hagi.Contracts.LogitGrad

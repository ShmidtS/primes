/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# the PAC-Bayes core (roadmap #5) — Gibbs variational inequality

The change-of-measure lemma underlying every PAC-Bayes bound,
proved DETERMINISTICALLY on a finite hypothesis class:
`log_weighted_jensen` + `gibbs_variational`:
  E_q f ≤ KL(q‖p) + ln E_p e^f
With a per-hypothesis Hoeffding step this yields PAC-Bayes
generalization; that last probabilistic step stays external
(h_emp_) — the deterministic core is here.
-/

open Finset Real

namespace Hagi.Data

/-- Weighted Jensen for log (tangent route): ln y ≤ y/m − 1
+ ln m at m > 0; weighted sum with Σq = 1 gives
Σ q ln x ≤ ln Σ qx. -/
theorem log_weighted_jensen {ι : Type} [Fintype ι] [Nonempty ι] (q x : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = 1) (hx : ∀ i, 0 < x i) :
    ∑ i, q i * Real.log (x i) ≤ Real.log (∑ i, q i * x i) := by
  set m := ∑ i, q i * x i with hm
  have hmpos : 0 < m := by
    have h0 : (0:ℝ) ≤ ∑ i, q i * x i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hq i).le (hx i).le
    by_contra hlt
    push Not at hlt
    rw [hm] at hlt
    have heq0 : ∑ i, q i * x i = 0 := le_antisymm hlt h0
    have hzero : ∀ i ∈ (Finset.univ : Finset ι), q i * x i = 0 :=
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hq i).le (hx i).le) |>.mp heq0
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hzi := hzero i (Finset.mem_univ i)
    have hpos := mul_pos (hq i) (hx i)
    rw [hzi] at hpos
    exact absurd hpos (by norm_num)
  have htan : ∀ i, Real.log (x i) ≤ x i / m - 1 + Real.log m := by
    intro i
    have h1 : Real.log (x i / m) ≤ x i / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hx i) hmpos)
    have h2 : Real.log (x i / m) = Real.log (x i) - Real.log m := by
      rw [Real.log_div (hx i).ne' hmpos.ne']
    linarith
  have hw : ∀ i, q i * Real.log (x i) ≤ q i * (x i / m - 1 + Real.log m) :=
    fun i => mul_le_mul_of_nonneg_left (htan i) (hq i).le
  have hsumle := Finset.sum_le_sum (s := Finset.univ)
    (f := fun i => q i * Real.log (x i))
    (g := fun i => q i * (x i / m - 1 + Real.log m)) (fun i _ => hw i)
  have hsplit : ∑ i, q i * (x i / m - 1 + Real.log m)
      = (∑ i, q i * x i) / m - (∑ i, q i) + (∑ i, q i) * Real.log m := by
    have e1 : ∑ i : ι, q i * (x i / m - 1 + Real.log m)
        = ∑ i : ι, (q i * x i / m - q i + q i * Real.log m) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1]
    have e2 : ∑ i : ι, q i * x i / m = (∑ i : ι, q i * x i) / m :=
      Eq.symm (Finset.sum_div (s := Finset.univ) (f := fun i => q i * x i) m)
    have e3 : ∑ i : ι, q i = 1 := hsum
    have e4 : ∑ i : ι, q i * Real.log m = (∑ i : ι, q i) * Real.log m :=
      (Finset.sum_mul (s := Finset.univ) (f := q) (a := Real.log m)).symm
    have esub : ∑ i : ι, (q i * x i / m - q i)
        = (∑ i : ι, q i * x i / m) - (∑ i : ι, q i) :=
      sum_sub_distrib (fun i : ι => q i * x i / m) (fun i : ι => q i)
    have eadd : ∑ i : ι, (q i * x i / m - q i + q i * Real.log m)
        = ∑ i : ι, (q i * x i / m - q i) + ∑ i : ι, q i * Real.log m :=
      sum_add_distrib (f := fun i => q i * x i / m - q i)
        (g := fun i => q i * Real.log m)
    rw [eadd, esub, e2, e4]
  rw [hsplit, hsum, one_mul] at hsumle
  rw [hm] at hsumle
  have hdivle : (∑ i, q i * x i) / m ≤ 1 := by
    rw [div_le_one hmpos, hm]
  have hfin : ∑ i, q i * Real.log (x i) ≤ Real.log m := by linarith
  rw [hm]
  exact hfin

/-- **The Gibbs variational inequality (roadmap #5, PAC-Bayes
core)**: for any posterior weights q and prior weights p on
a finite hypothesis class, and any values f,

  E_q f ≤ KL(q‖p) + ln E_p e^f

—the change-of-measure lemma underlying every PAC-Bayes
bound. Proof: pointwise f_i − ln(q_i/p_i) = ln(p_i e^{f_i}
/ q_i); the q-weighted sum of the right side is ≤ ln Σ p e^f
by log_weighted_jensen (concavity). With Hoeffding per
hypothesis this yields the PAC-Bayes generalization bound;
that last probabilistic step stays external (h_emp_). -/
theorem gibbs_variational {ι : Type} [Fintype ι] [Nonempty ι]
    (q p : ι → ℝ) (f : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hqs : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (_hps : ∑ i, p i = 1) :
    (∑ i, q i * f i)
      ≤ (∑ i, q i * Real.log (q i / p i))
        + Real.log (∑ i, p i * Real.exp (f i)) := by
  set x : ι → ℝ := fun i => p i * Real.exp (f i) / q i with hx
  have hxp : ∀ i, 0 < x i := by
    intro i
    rw [hx]
    exact div_pos (mul_pos (hp i) (Real.exp_pos (f i))) (hq i)
  -- pointwise identity
  have hpt : ∀ i, f i - Real.log (q i / p i) = Real.log (x i) := by
    intro i
    rw [hx]
    have hL : Real.log (q i / p i) = Real.log (q i) - Real.log (p i) :=
      Real.log_div (hq i).ne' (hp i).ne'
    have hR : Real.log (p i * Real.exp (f i) / q i)
        = Real.log (p i) + f i - Real.log (q i) := by
      rw [Real.log_div (mul_pos (hp i) (Real.exp_pos (f i))).ne' (hq i).ne']
      rw [Real.log_mul (hp i).ne' (Real.exp_pos (f i)).ne']
      rw [Real.log_exp]
    rw [hL, hR]
    ring
  -- Jensen on x with weights q
  have hj := log_weighted_jensen q x hq hqs hxp
  -- chain: E_q f - KL = E_q log x <= log (Σ q x) = log (Σ p e^f)
  have hqx : ∑ i, q i * x i = ∑ i, p i * Real.exp (f i) := by
    have e1 : ∑ i : ι, q i * x i = ∑ i : ι, (p i * Real.exp (f i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hx]
      change q i * (p i * Real.exp (f i) / q i) = p i * Real.exp (f i)
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ (p i * Real.exp (f i)) (hq i).ne'
    exact e1
  rw [hqx] at hj
  -- finish: E_q f = E_q (f - log(q/p)) + E_q log(q/p) <= ln Σ p e^f + KL
  have hsplit : ∑ i, q i * f i
      = ∑ i, q i * (f i - Real.log (q i / p i)) + ∑ i, q i * Real.log (q i / p i) := by
    rw [← sum_add_distrib (f := fun i => q i * (f i - Real.log (q i / p i)))
      (g := fun i => q i * Real.log (q i / p i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hswitch : ∑ i, q i * (f i - Real.log (q i / p i))
      = ∑ i, q i * Real.log (x i) := by
    exact Finset.sum_congr rfl (fun i _ => by rw [hpt i])
  rw [hswitch] at hsplit
  linarith

end Hagi.Data

namespace Hagi
export Hagi.Data (log_weighted_jensen gibbs_variational)
end Hagi

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# The concat==child invariant and the `scale = 1/n` temperature correction

* `concatCols_identical` — the concat head of `n` copies of `W`
  applied to the stacked states of `n` copies of `x` is
  `(n : ℝ) • (W *ᵥ x)`.
* `concat_unique_identity_scale` — a scale `s` reproducing the
  child at a coordinate where the child's logit is nonzero must
  equal `1 / (n : ℝ)`.
* `temperature_softmax_eq_forces_const` /
  `temperature_changes_softmax` — if rescaled logits (`c ≠ 1`)
  produce the same softmax distribution, the logits were constant.
-/

open scoped Matrix

namespace Hagi.Core

section Concat

variable {o m : Type*} [Fintype o] [Fintype m]

/-- The column-concatenation of `n` copies of the child head `W`
(the merged head of `n` identical children). -/
def concatCols (n : ℕ) (W : Matrix o m ℝ) :
    Matrix o (Fin n × m) ℝ :=
  fun j p => W j p.2

omit [Fintype o] in
/-- The concatenated head of `n` copies of `W`, applied to the
stacked states of `n` copies of `x`, yields `(n : ℝ) • (W *ᵥ x)`. -/
theorem concatCols_identical (n : ℕ) (W : Matrix o m ℝ) (x : m → ℝ) :
    concatCols n W *ᵥ (fun p => x p.2) = (n : ℝ) • (W *ᵥ x) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, concatCols]
  rw [Fintype.sum_prod_type]
  have step1 : ∀ i : Fin n, ∑ y : m, W j (i, y).2 * x (i, y).2
      = ∑ y : m, W j y * x y := fun i =>
    Finset.sum_congr rfl fun y _ => rfl
  rw [Finset.sum_congr rfl (fun i _ => step1 i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp [Matrix.mulVec, dotProduct]

omit [Fintype o] in
/-- Pointwise form of `Hagi.concatCols_identical`. -/
theorem concatCols_identical_apply (n : ℕ) (W : Matrix o m ℝ) (x : m → ℝ)
    (j : o) :
    (concatCols n W *ᵥ (fun p => x p.2)) j = (n : ℝ) * (W *ᵥ x) j := by
  have h := congrFun (concatCols_identical n W x) j
  rw [h, Pi.smul_apply, smul_eq_mul]

omit [Fintype o] in
/-- If the scale `s` rescales the merged logits to the child's logit
at a coordinate `j` where `(W *ᵥ x) j ≠ 0`, then `s = 1 / (n : ℝ)`. -/
theorem concat_unique_identity_scale (n : ℕ) (hn : 0 < n)
    (W : Matrix o m ℝ) (x : m → ℝ) (j : o)
    (hx : (W *ᵥ x) j ≠ 0) (s : ℝ)
    (hs : s * (concatCols n W *ᵥ (fun p => x p.2)) j = (W *ᵥ x) j) :
    s = 1 / (n : ℝ) := by
  rw [concatCols_identical_apply, ← mul_assoc] at hs
  have h2' : s * (n : ℝ) = 1 :=
    mul_right_cancel₀ hx (by rw [one_mul]; exact hs)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have h3 : s = (n : ℝ)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hn').mp h2'
  rw [h3, inv_eq_one_div]

end Concat

section Temperature

variable {k : Type*} [Fintype k] [Nonempty k]

/-- If `c ≠ 1` and rescaling the logits by `c` leaves the softmax
distribution unchanged, then the logits are constant: `z a = z b`
for all `a, b`. -/
theorem temperature_softmax_eq_forces_const (c : ℝ) (z : k → ℝ)
    (hc : c ≠ 1)
    (h : (fun i => Real.exp (c * z i) / ∑ l, Real.exp (c * z l))
      = (fun i => Real.exp (z i) / ∑ l, Real.exp (z l))) :
    ∀ a b : k, z a = z b := by
  have hS1 : (0 : ℝ) < ∑ l, Real.exp (z l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hSc : (0 : ℝ) < ∑ l, Real.exp (c * z l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hfun : ∀ i : k,
      Real.exp (c * z i) * (∑ l, Real.exp (z l))
        = Real.exp (z i) * (∑ l, Real.exp (c * z l)) := by
    intro i
    have hfuni := congrFun h i
    rw [div_eq_div_iff (ne_of_gt hSc) (ne_of_gt hS1)] at hfuni
    exact hfuni
  intro a b
  by_contra hne
  have ha := hfun a
  have hb := hfun b
  have key0 : (Real.exp (c * z a) * Real.exp (z b)
      - Real.exp (z a) * Real.exp (c * z b))
      * (∑ l, Real.exp (z l)) = 0 := by
    linear_combination Real.exp (z b) * ha - Real.exp (z a) * hb
  have key : Real.exp (c * z a) * Real.exp (z b)
      = Real.exp (z a) * Real.exp (c * z b) := by
    rcases mul_eq_zero.mp key0 with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 (ne_of_gt hS1)
  have hexp : Real.exp (c * z a + z b) = Real.exp (z a + c * z b) := by
    rw [Real.exp_add, Real.exp_add]
    exact key
  have heq : c * z a + z b = z a + c * z b := Real.exp_injective hexp
  have hzero : (c - 1) * (z a - z b) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hc
  · exact absurd (sub_eq_zero.mp h2) hne

/-- If `c ≠ 1` and the logits are non-constant, rescaling by `c`
changes the softmax distribution. -/
theorem temperature_changes_softmax (c : ℝ) (z : k → ℝ) (hc : c ≠ 1)
    (hne : ∃ a b : k, z a ≠ z b) :
    (fun i => Real.exp (c * z i) / ∑ l, Real.exp (c * z l))
      ≠ (fun i => Real.exp (z i) / ∑ l, Real.exp (z l)) := by
  intro hcontra
  obtain ⟨a, b, hab⟩ := hne
  exact hab (temperature_softmax_eq_forces_const c z hc hcontra a b)

end Temperature

/-! ## The log-sum-exp convexity and the ensemble theorem -/

section Ensemble

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Log-sum-exp of a logit vector (the log-normalizer of softmax). -/
noncomputable def lse (z : k → ℝ) : ℝ := Real.log (∑ v, Real.exp (z v))

theorem exp_sum_pos (z : k → ℝ) : 0 < ∑ v, Real.exp (z v) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Midpoint convexity of `lse`:
`lse ((z₁ + z₂)/2) ≤ (lse z₁ + lse z₂)/2`, by Cauchy-Schwarz on
`exp((z₁+z₂)/2) = exp(z₁/2)·exp(z₂/2)`. The general weighted form
is not formalized here. -/
theorem lse_midpoint_le (z₁ z₂ : k → ℝ) :
    lse ((z₁ + z₂) / 2) ≤ (lse z₁ + lse z₂) / 2 := by
  have hfg : ∀ v : k,
      Real.exp (z₁ v / 2) * Real.exp (z₂ v / 2)
        = Real.exp ((z₁ v + z₂ v) / 2) := by
    intro v
    rw [← Real.exp_add]
    congr 1
    field_simp
  have hf2 : ∀ v : k,
      Real.exp (z₁ v / 2) ^ 2 = Real.exp (z₁ v) := by
    intro v
    rw [pow_two, ← Real.exp_add]
    congr 1
    norm_num
  have hg2 : ∀ v : k,
      Real.exp (z₂ v / 2) ^ 2 = Real.exp (z₂ v) := by
    intro v
    rw [pow_two, ← Real.exp_add]
    congr 1
    norm_num
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun v => Real.exp (z₁ v / 2)) (fun v => Real.exp (z₂ v / 2))
  rw [Finset.sum_congr rfl fun v _ => hf2 v,
    Finset.sum_congr rfl fun v _ => hg2 v] at hcauchy
  have hlhs : ∑ v, Real.exp (z₁ v / 2) * Real.exp (z₂ v / 2)
      = ∑ v, Real.exp ((z₁ v + z₂ v) / 2) :=
    Finset.sum_congr rfl fun v _ => hfg v
  rw [hlhs] at hcauchy
  -- hcauchy : (∑ exp mid) ^ 2 ≤ (∑ exp z₁) * (∑ exp z₂)
  set P := ∑ v, Real.exp (z₁ v) with hP
  set Q := ∑ v, Real.exp (z₂ v) with hQ
  set A := ∑ v, Real.exp ((z₁ v + z₂ v) / 2) with hA
  have hApos : 0 < A := exp_sum_pos ((z₁ + z₂) / 2)
  have hstep : A ≤ Real.sqrt (P * Q) := by
    rw [← Real.sqrt_mul_self (le_of_lt hApos), ← pow_two]
    exact Real.sqrt_le_sqrt hcauchy
  have hlog : Real.log A ≤ (Real.log P + Real.log Q) / 2 := by
    have h1 : Real.log A ≤ Real.log (Real.sqrt (P * Q)) :=
      Real.log_le_log hApos hstep
    have h2 : Real.log (Real.sqrt (P * Q)) = (Real.log P + Real.log Q) / 2 := by
      rw [Real.log_sqrt (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    rw [h2] at h1
    exact h1
  unfold lse at hlog ⊢
  exact hlog

/-- The cross-entropy of a logit vector `z` against a one-hot target
`t`: `CE t z = lse z − z t`. -/
noncomputable def ceOneHot (t : k) (z : k → ℝ) : ℝ := lse z - z t

/-- The ensemble bound for two children:
`ceOneHot t ((z₁ + z₂)/2) ≤ (ceOneHot t z₁ + ceOneHot t z₂)/2`.
Jensen for `lse`; the linear target term cancels. -/
theorem ensemble_ce_le_mean (t : k) (z₁ z₂ : k → ℝ) :
    ceOneHot t ((z₁ + z₂) / 2) ≤ (ceOneHot t z₁ + ceOneHot t z₂) / 2 := by
  unfold ceOneHot
  have hmid := lse_midpoint_le z₁ z₂
  have hz : ((z₁ + z₂) / 2) t = (z₁ t + z₂ t) / 2 := by simp
  rw [hz]
  have hmean : ((lse z₁ - z₁ t) + (lse z₂ - z₂ t)) / 2
      = (lse z₁ + lse z₂) / 2 - (z₁ t + z₂ t) / 2 := by ring
  rw [hmean]
  linarith

end Ensemble

section GeneralN

variable {k : Type*} [Fintype k] [Nonempty k] {N : ℕ} [NeZero N]

/-- General-N ensemble bound for `lse`:
`lse (fun v => (∑ a, z a v) / N) ≤ (∑ a, lse (z a)) / N`, by the
pointwise weighted AM-GM applied to `t a v = exp (z a v) / S a`.
The two-leaf case is `ensemble_ce_le_mean`. -/
theorem lse_mean_le_mean_lse (z : Fin N → k → ℝ) :
    lse (fun v => (∑ a, z a v) / N)
      ≤ (∑ a, lse (z a)) / N := by
  -- normalization: S a = ∑_v exp (z a v) > 0, t a v = exp (z a v)/S a
  set S : Fin N → ℝ := fun a => ∑ v, Real.exp (z a v) with hS
  have hSpos : ∀ a, 0 < S a := fun a => exp_sum_pos (z a)
  set t : Fin N → k → ℝ := fun a v => Real.exp (z a v) / S a with ht
  -- pointwise AM-GM: ∏_a (t a v)^(1/N) ≤ (1/N)∑_a t a v
  have htpos : ∀ a v, 0 < t a v := by
    intro a v
    unfold t
    exact div_pos (Real.exp_pos _) (hSpos a)
  have hamgm : ∀ v : k,
      ∏ a, (t a v) ^ ((1:ℝ)/N) ≤ ∑ a, (1/(N:ℝ)) * t a v := fun v =>
    Real.geom_mean_le_arith_mean_weighted
      (Finset.univ : Finset (Fin N)) (fun _ => 1/(N:ℝ)) (fun a => t a v)
      (fun a _ => by positivity)
      (by simp)
      (fun a _ => le_of_lt (htpos a v))
  -- the per-child mass is 1
  have hmass : ∀ a, ∑ v, t a v = 1 := by
    intro a
    simp only [ht, ← Finset.sum_div]
    exact div_self (ne_of_gt (hSpos a))
  -- the Hoelder split of the merged summand
  have hsplit : ∀ v : k,
      Real.exp ((∑ a, z a v) / N)
        = (∏ a, (S a) ^ ((1:ℝ)/N)) * ∏ a, (t a v) ^ ((1:ℝ)/N) := by
    intro v
    have e1 : (∑ a, z a v) / N = ∑ a, z a v / N :=
      Finset.sum_div _ _ _
    rw [e1, Real.exp_sum]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    -- exp (z a v / N) = (S a)^(1/N) * (t a v)^(1/N)
    have hst : S a * t a v = Real.exp (z a v) := by
      simp only [ht]
      exact mul_div_cancel₀ _ (ne_of_gt (hSpos a))
    rw [← Real.mul_rpow (le_of_lt (hSpos a)) (by positivity : (0:ℝ) ≤ t a v),
      hst, Real.rpow_def_of_pos (Real.exp_pos (z a v)), Real.log_exp]
    congr 1
    field_simp
  -- E ≤ ∏ (S a)^(1/N)
  have hE : ∑ v, Real.exp ((∑ a, z a v) / N)
      ≤ ∏ a, (S a) ^ ((1:ℝ)/N) := by
    have h1 : ∑ v, Real.exp ((∑ a, z a v) / N)
        = (∏ a, (S a) ^ ((1:ℝ)/N))
          * ∑ v, ∏ a, (t a v) ^ ((1:ℝ)/N) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => hsplit v
    rw [h1]
    have h2 : ∑ v, ∏ a, (t a v) ^ ((1:ℝ)/N) ≤ 1 := by
      calc ∑ v, ∏ a, (t a v) ^ ((1:ℝ)/N)
          ≤ ∑ v, ∑ a, (1/(N:ℝ)) * t a v :=
            Finset.sum_le_sum fun v _ => hamgm v
        _ = ∑ a, ∑ v, (1/(N:ℝ)) * t a v := Finset.sum_comm
        _ = ∑ a, (1/(N:ℝ)) * ∑ v, t a v := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact (Finset.mul_sum Finset.univ (t a) ((1:ℝ)/N)).symm
        _ = ∑ a, (1/(N:ℝ)) * 1 :=
            Finset.sum_congr rfl fun a _ => by rw [hmass a]
        _ = 1 := by simp
    have hpos : (0:ℝ) < ∏ a, (S a) ^ ((1:ℝ)/N) :=
      Finset.prod_pos fun a _ => Real.rpow_pos_of_pos (hSpos a) _
    calc (∏ a, (S a) ^ ((1:ℝ)/N)) * ∑ v, ∏ a, (t a v) ^ ((1:ℝ)/N)
        ≤ (∏ a, (S a) ^ ((1:ℝ)/N)) * 1 :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      _ = ∏ a, (S a) ^ ((1:ℝ)/N) := by ring
  -- log both sides
  unfold lse
  have hlog := Real.log_le_log (exp_sum_pos _) hE
  rw [Real.log_prod (fun a _ =>
    ne_of_gt (Real.rpow_pos_of_pos (hSpos a) _)),
    Finset.sum_congr rfl fun a _ => Real.log_rpow (hSpos a) _] at hlog
  -- hlog : log (∑ exp zMean) ≤ ∑ (1/N) * log (S a)
  -- goal : log (∑ exp zMean) ≤ (∑ lse (z a)) / N
  -- (1/N) * log (S a) = lse (z a) / N, since log (S a) = lse (z a)
  have hconv : ∑ a, (1/(N:ℝ)) * Real.log (S a)
      = (∑ a, lse (z a)) / N := by
    have h1 : ∀ a : Fin N, (1/(N:ℝ)) * Real.log (S a) = lse (z a) / N := by
      intro a
      change (1/(N:ℝ)) * Real.log (∑ v, Real.exp (z a v))
          = Real.log (∑ v, Real.exp (z a v)) / N
      rw [div_eq_mul_inv, mul_comm]
      field_simp
    rw [Finset.sum_div, Finset.sum_congr rfl fun a _ => h1 a]
  rw [hconv] at hlog
  exact hlog

/-- General-N ensemble bound for the cross-entropy:
`ceOneHot t (mean of the z a) ≤ (∑ a, ceOneHot t (z a)) / N`. -/
theorem ensemble_ce_le_mean_general (t : k) (z : Fin N → k → ℝ) :
    ceOneHot t (fun v => (∑ a, z a v) / N)
      ≤ (∑ a, ceOneHot t (z a)) / N := by
  have hlse := lse_mean_le_mean_lse z
  unfold ceOneHot
  have ht : (fun v => (∑ a, z a v) / N) t = (∑ a, z a t) / N := rfl
  have hlin : (∑ a, ceOneHot t (z a)) / N
      = (∑ a, (lse (z a) - z a t)) / N := by
    have : ∀ a : Fin N, ceOneHot t (z a) = lse (z a) - z a t := by
      intro a
      unfold ceOneHot
      rfl
    rw [Finset.sum_congr rfl fun a _ => this a]
  have hsplit : (∑ a, (lse (z a) - z a t)) / N
      = (∑ a, lse (z a)) / N - (∑ a, z a t) / N := by
    rw [Finset.sum_sub_distrib, sub_div, Finset.sum_div]
  rw [ht, hsplit]
  linarith

end GeneralN

/-! ## Head multiplicity: the selection gap as a mass bound -/

section HeadMultiplicity

variable {k : Type*} [Fintype k] [Nonempty k]

/-- The softmax probability of a coordinate. -/
noncomputable def softmaxP (z : k → ℝ) (a : k) : ℝ :=
  Hagi.Prelude.softDef z a

/-- If `z b + g ≤ z a`, then the softmax masses satisfy
`softmaxP z a ≥ Real.exp g * softmaxP z b`. -/
theorem softmax_gap_mass_ratio (z : k → ℝ) (a b : k) (g : ℝ)
    (hz : z b + g ≤ z a) :
    softmaxP z a ≥ Real.exp g * softmaxP z b := by
  show Real.exp (z a) / ∑ l, Real.exp (z l)
      ≥ Real.exp g * (Real.exp (z b) / ∑ l, Real.exp (z l))
  have hpos : (0:ℝ) < ∑ l, Real.exp (z l) := exp_sum_pos z
  have hA : Real.exp (z b + g) ≤ Real.exp (z a) :=
    Real.exp_le_exp.mpr hz
  rw [Real.exp_add] at hA
  -- goal: exp(za)/S ≥ exp g * exp(zb)/S
  field_simp
  linarith

end HeadMultiplicity

end Hagi.Core

namespace Hagi
export Hagi.Core (concatCols concatCols_identical concatCols_identical_apply concat_unique_identity_scale temperature_softmax_eq_forces_const temperature_changes_softmax lse exp_sum_pos lse_midpoint_le ceOneHot ensemble_ce_le_mean lse_mean_le_mean_lse ensemble_ce_le_mean_general softmaxP softmax_gap_mass_ratio)
end Hagi

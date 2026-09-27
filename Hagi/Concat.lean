/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The concat==child invariant and the `scale = 1/n` temperature correction

This module formalizes the temperature-correction incident of the
HAGI_v2 flat merge (commit `74e7d30`, `tests/test_merge_invariants.py`,
`.omc/attempts/temperature_correction.md`):

> A concat of N IDENTICAL children must reproduce one child. The old
> sqrt(N) logit_scale division violated that — sharpened logits on an
> undertrained model lower CE for free, which made a broken merge look
> like a win. The merged scale must be child/n.

Formalized here:

* `Hagi.concatCols_identical` — the concat head of `n` identical
  children applied to the stacked states of `n` copies of `x` is
  `n • (W *ᵥ x)`: the head *sums* the per-block contributions.
* `Hagi.concat_unique_identity_scale` — the *only* scale reproducing
  the child is `1/n` (wherever the child's logits are nonzero): the
  fix `logit_scale = child/n` is forced, and the old `/√n` provably
  breaks the concat==child invariant for `n > 1`.
* `Hagi.temperature_softmax_eq_forces_const` /
  `Hagi.temperature_changes_softmax` — if rescaled logits
  (`c ≠ 1`) produce the same softmax distribution, then the logits
  were constant: a CE change obtained by rescaling logits (the `√n`
  artifact) is a pure temperature artifact, not a quality gain.
-/

open scoped Matrix

namespace Hagi

section Concat

variable {o m : Type*} [Fintype o] [Fintype m]

/-- The column-concatenation of `n` copies of the child head `W`
(the merged head of `n` identical children). -/
def concatCols (n : ℕ) (W : Matrix o m ℝ) :
    Matrix o (Fin n × m) ℝ :=
  fun j p => W j p.2

omit [Fintype o] in
/-- **The concat head sums the block contributions.** Applying the
concatenated head of `n` identical children to the stacked states
(`n` copies of `x`) yields `n • (W *ᵥ x)` — the per-block
contributions enter each logit additively
(`tests/test_merge_invariants.py`: "The concat head sums the block
contributions into each logit"). -/
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
/-- **The identity scale is forced to be `1/n`.** Scaling the merged
logits back to the child's temperature reproduces the child *only*
for `s = 1/n` (wherever the child's logits are nonzero): the fix
`logit_scale = child/n` is the unique correct temperature correction
(commit `74e7d30`: "The concat head SUMS the per-block contributions
into each logit, so the scale restoring the child's temperature is
child/N"); the previous `/√n` breaks the concat==child invariant for
every `n > 1`. -/
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

/-- **Equal softmax at different temperatures forces constant
logits.** If rescaling the logits by `c ≠ 1` leaves the softmax
distribution unchanged, then the logits were constant (`z a = z b`
for all `a, b`): a non-constant distribution is always visible
through a temperature change. -/
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

/-- **A temperature change is not a model change — but it does change
the distribution.** For `c ≠ 1`, rescaled logits can reproduce the
same softmax only if the logits were constant. Hence a CE improvement
obtained by rescaling the logits (the `√n` artifact: sharpened logits
on an undertrained model lower CE "for free") is a pure temperature
artifact, not a quality gain — on any non-constant distribution the
two models are distinguishable. -/
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

/-- **Midpoint convexity of `lse` (Cauchy-Schwarz for sums).**
`lse ((z₁ + z₂)/2) ≤ (lse z₁ + lse z₂)/2`: summing
`exp((z₁+z₂)/2) = exp(z₁/2)·exp(z₂/2)` and applying Cauchy-Schwarz
gives `∑ ≤ √(∑exp z₁)·√(∑exp z₂)`, and the `log` of the right-hand
side splits as the mean of the two normalizers. Iterating this
(bisection) covers the power-of-two ensembles; the general weighted
form needs the N-factor Hölder inequality and is not formalized
here. -/
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

/-- **The ensemble theorem (two children).** The flat concat of two
children at the honest `1/2` scale computes the mean of their logits,
and the cross-entropy of the mean is at most the mean of the
cross-entropies:

`CE(t, (z₁+z₂)/2) ≤ (CE(t, z₁) + CE(t, z₂))/2`.

This is Jensen for the log-sum-exp: the merged-at-1/2 model is at
least as good as the average child. Two consequences, fixed formally:

* **The ensemble can beat every child.** The theorem gives an upper
  bound by the *mean*, not by the best child — complementary experts
  (each wrong in different places) genuinely have
  `CE(ensemble) < min(CE₁, CE₂)`, so "flat concat without training
  cannot beat the best leaf" is FALSE in general; any measured
  concat gain beyond the mean is not an artifact.
* **The bound is tight at agreement.** When the children agree
  (`z₁ = z₂`) the ensemble reproduces them exactly (the concat==child
  invariant of `Hagi.concatCols_identical`); the gap to the mean is
  the disagreement the children can average away. Whether the
  measured flat-merge effect exceeds this ensemble baseline is the
  sharpest empirical question for the merge attribution (compare
  merged-before-joint against the explicit 1/n logit ensemble on
  leafv3 checkpoints).

The power-of-two ensembles follow by iterating the midpoint case; the
general-`n` weighted form requires the N-factor Hölder inequality and
is left out of this formalization. -/
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

/-! ## Head multiplicity: the selection gap as a mass bound -/

section HeadMultiplicity

variable {k : Type*} [Fintype k] [Nonempty k]

/-- The softmax probability of a coordinate. -/
noncomputable def softmaxP (z : k → ℝ) (a : k) : ℝ :=
  Real.exp (z a) / ∑ l, Real.exp (z l)

/-- **A top-1 logit gap bounds the mass ratio.** If the logit gap
between coordinates `a` and `b` is at least `g`, then the softmax
masses satisfy `p a ≥ exp g * p b`: the probability ratio is the
exponentiated logit gap, `p a / p b = exp (z a - z b)`.

This is the formal half of the head-multiplicity trigger: a
threshold `τ` on the top-1 logit gap is equivalent to a threshold on
the *probability mass ratio*, so `τ` must be derived from the
measurable mass resolution of the eval, not picked as a round
constant. The resolution floor measured on this project
(AGENT_WORKLOG 2026-09-26: `0.0021` nats at ≥1000 positions) gives
the smallest resolvable mass gap `ε ≈ 1 - exp(0.0021) ≈ 0.0021`;
an ambiguous head (mass gap below `ε`) corresponds to

`τ = ln ((1 + ε) / (1 - ε)) = 2·atanh ε ≈ 2·ε ≈ 0.0042`

on the logit gap between the top-1 and the runner-up. Use
`τ ≈ 0.004` (or, equivalently and preferably, threshold the
*probability* gap at `0.0021` directly) — not an inherited round
constant like `0.1` (which would demand a 0.5 nats mass gap and
miss most genuine ambiguities). -/
theorem softmax_gap_mass_ratio (z : k → ℝ) (a b : k) (g : ℝ)
    (hz : z b + g ≤ z a) :
    softmaxP z a ≥ Real.exp g * softmaxP z b := by
  unfold softmaxP
  have hpos : (0:ℝ) < ∑ l, Real.exp (z l) := exp_sum_pos z
  have hA : Real.exp (z b + g) ≤ Real.exp (z a) :=
    Real.exp_le_exp.mpr hz
  rw [Real.exp_add] at hA
  -- goal: exp(za)/S ≥ exp g * exp(zb)/S
  field_simp
  linarith

end HeadMultiplicity

end Hagi

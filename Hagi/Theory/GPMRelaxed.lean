/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.GPM
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# GPM relaxed projection — honest forgetting/progress trade-off (C498)

The C494 observation: exact GPM (`Hagi.Step.gpm_zero_forgetting`,
zero forgetting when the step is orthogonal to the FULL span of
old inputs) degenerates when the span grows to the whole
dimension — every step is projected away (the gpm2 bench phase
was all HOLD). The continual literature (Saha et al., ICLR'21)
truncates the basis to the top-k spectral directions; A-GEM
(Chaudhry et al., ICLR'19) projects only on gradient conflict.

This module is the honest theory of the compromise, on an
ABSTRACT projection `P` (no spectral construction enters any
proof — only linearity of `dotProduct` does):

* rank-truncated GPM: `gpmOrthP` — each step row is orthogonal
  to the PROJECTED old inputs `P *ᵥ xs k`; forgetting on old
  input `x` is then bounded by `‖row‖ · sigmaTail P x` where
  `sigmaTail P x = ‖x − P·x‖` is the tail energy leakage
  (`rank_trunc_forgetting_bound`). Instance `P = 1` recovers
  exact zero forgetting (`gpm_full_zero`); instance `P = 0`
  (no projection) has UNBOUNDED forgetting
  (`rank_zero_unbounded`, quantitative form of the C485
  negative `naive_step_can_forget`).
* A-GEM conditional projection: `agemStep` applies the free
  step when `⟨g, g_old⟩ ≥ 0` (no first-order interference) and
  the orthogonalized step on conflict; the applied rule ALWAYS
  has non-negative first-order old-interference
  (`agem_step_nonneg_interf`).
* The trade-off theorem `gpm_tradeoff`: under one orthogonality
  hypothesis, BOTH forgetting on old inputs AND progress on a
  new input are controlled by the SAME tail mechanism —
  shrinking the tail shrinks forgetting but also shrinks the
  admissible progress; when the tail of the new input is zero,
  NO admissible step makes progress on it
  (`gpm_hold_when_covered` — the machine-checked form of the
  C494 all-HOLD phenomenon).

Honest pins (bench-side, not theorems): `P` is built by exact
rational Gram–Schmidt (the C485 bench pattern `Q = I − Σ u uᵀ/(u·u)`);
SVD is never constructed (it is irrational in general); the tail
budget is compared in SQUARES (`sigmaTail² = ‖x − Px‖²` is a
sum of squares of rationals — exact Fraction arithmetic); the
cert-rule for the truncation rank is: minimal `k` with
`max_old sigmaTail² ≤ ε²` (a measurable rational threshold).

Layer decision: Theory (7) — consumes the GPM step theory
(`Hagi.Step.GPM`, layer 5); same pattern as the C485 bridge
`Hagi.Theory.ContinualBench`.
-/

open scoped Matrix

namespace Hagi.Theory.GPMRelaxed

variable {m n K : ℕ}

/-- Euclidean norm on `Fin n → ℝ` via `dotProduct`
(noncomputable: `Real.sqrt`; the bench compares SQUARES,
which are rational). -/
noncomputable def nrm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- Tail energy leakage of projection `P` on input `x`:
`sigmaTail P x = ‖x − P·x‖`. At `P = 1` it is zero (exact
GPM); at `P = 0` it is `‖x‖` (no projection). -/
noncomputable def sigmaTail {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ := nrm (x - P *ᵥ x)

/-- Relaxed GPM orthogonality: each row of the step `ΔW` is
orthogonal to the PROJECTED old inputs `P *ᵥ xs k` (top-k
subspace version of `Hagi.Step.gpmOrth`). -/
def gpmOrthP (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ) :
    Prop := ∀ i k, ΔW i ⬝ᵥ (P *ᵥ xs k) = 0

/-- Cauchy–Schwarz for `dotProduct` (corpus pattern,
`Hagi/Step/Joint.lean`). -/
theorem cs_abs {n : ℕ} (v w : Fin n → ℝ) :
    |v ⬝ᵥ w| ≤ nrm v * nrm w := by
  have hcauchy : (v ⬝ᵥ w)^2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
    have hconv : (∑ i, v i ^ 2) = ∑ i, v i * v i :=
      Finset.sum_congr rfl fun i _ => pow_two (v i)
    have hconv2 : (∑ i, w i ^ 2) = ∑ i, w i * w i :=
      Finset.sum_congr rfl fun i _ => pow_two (w i)
    rw [hconv, hconv2] at h
    exact h
  have hsq : |v ⬝ᵥ w| * |v ⬝ᵥ w| ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
    rw [abs_mul_abs_self (v ⬝ᵥ w), ← pow_two (v ⬝ᵥ w)]
    exact hcauchy
  have h4 : Real.sqrt (|v ⬝ᵥ w| * |v ⬝ᵥ w|)
      ≤ Real.sqrt ((v ⬝ᵥ v) * (w ⬝ᵥ w)) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul_self (abs_nonneg (v ⬝ᵥ w))] at h4
  rw [Real.sqrt_mul (by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)] at h4
  exact h4

/-- Pure linear algebra: any residual `r ⬝ᵥ x` equals the dot
product with the tail `x − P·x` up to the projected part. No
projection property of `P` is used. -/
theorem dot_split {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (r x : Fin n → ℝ) :
    r ⬝ᵥ x = r ⬝ᵥ (P *ᵥ x) + r ⬝ᵥ (x - P *ᵥ x) := by
  rw [dotProduct_sub]
  ring

/-- **rank_trunc_forgetting_bound (C498)**: a rank-truncated
GPM step (rows orthogonal to the projected old inputs,
`gpmOrthP`) changes the response on old input `xs k` by at
most `‖row‖ · sigmaTail` — the forgetting budget is the tail
energy leakage, NOT zero (honest trade-off: at `P = 1` the
tail vanishes and so does forgetting). -/
theorem rank_trunc_forgetting_bound
    (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (horth : gpmOrthP ΔW xs P) (i : Fin m) (k : Fin K) :
    |ΔW i ⬝ᵥ xs k| ≤ nrm (ΔW i) * sigmaTail P (xs k) := by
  have hsplit : ΔW i ⬝ᵥ xs k = ΔW i ⬝ᵥ (xs k - P *ᵥ xs k) := by
    have h := dot_split P (ΔW i) (xs k)
    rw [horth i k, zero_add] at h
    exact h
  rw [hsplit]
  exact cs_abs _ _

/-- **rank_trunc_output_bound (C498)**: the per-row output
change on an old input under a rank-truncated GPM step is
bounded by `‖row‖ · sigmaTail` (the matrix form of
`rank_trunc_forgetting_bound`; via `mulVec_eq_dotProduct`). -/
theorem rank_trunc_output_bound
    (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (horth : gpmOrthP ΔW xs P) (i : Fin m) (k : Fin K) :
    |((W + ΔW) *ᵥ xs k) i - (W *ᵥ xs k) i|
      ≤ nrm (ΔW i) * sigmaTail P (xs k) := by
  have hsplit : ((W + ΔW) *ᵥ xs k) i - (W *ᵥ xs k) i
      = ΔW i ⬝ᵥ xs k := by
    rw [Matrix.add_mulVec, Pi.add_apply, Hagi.Step.mulVec_eq_dotProduct,
      Hagi.Step.mulVec_eq_dotProduct]
    ring
  rw [hsplit]
  exact rank_trunc_forgetting_bound ΔW xs P horth i k

/-- **sigmaTail_one_zero (C498)**: at the full projection
`P = 1` the tail energy leakage is exactly zero. -/
theorem sigmaTail_one_zero {n : ℕ} (x : Fin n → ℝ) :
    sigmaTail (1 : Matrix (Fin n) (Fin n) ℝ) x = 0 := by
  unfold sigmaTail nrm
  rw [Matrix.one_mulVec, sub_self]
  simp

/-- **gpm_full_zero (C498)**: at the full projection `P = 1`
the relaxed condition `gpmOrthP` degenerates to exact
`gpmOrth`, so the instance `k = full` of the truncation family
recovers the exact zero-forgetting theory
(`Hagi.Step.gpm_zero_forgetting`). Generalization is strict:
`rank_trunc_forgetting_bound` at `P = 1` gives a zero bound
via `sigmaTail_one_zero`. -/
theorem gpm_full_zero (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (horth : gpmOrthP ΔW xs (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Hagi.Step.gpmOrth ΔW xs := by
  intro i k
  have h := horth i k
  rwa [Matrix.one_mulVec] at h

/-- **rank_zero_unbounded (C498)**: the k = 0 negative —
WITHOUT projection (P = 0) forgetting is unbounded: for every
budget `C > 0` there is an old input and a unit-norm step row
achieving response change exactly `C`. The qualitative C485
negative `naive_step_can_forget` is the special case `C = 1`;
here the magnitude is arbitrary (unit step, scaled input). -/
theorem rank_zero_unbounded (C : ℝ) (hC : 0 < C) :
    ∃ (xs : Fin 1 → (Fin 2 → ℝ)) (ΔW : Matrix (Fin 1) (Fin 2) ℝ),
      gpmOrthP ΔW xs (0 : Matrix (Fin 2) (Fin 2) ℝ)
        ∧ |ΔW 0 ⬝ᵥ xs 0| = C ∧ nrm (ΔW 0) = 1 := by
  refine ⟨fun _ j => if j = 0 then C else 0,
    Matrix.of fun _ j => if j = 0 then 1 else 0, ?_, ?_, ?_⟩
  · intro i k
    rw [Matrix.zero_mulVec]
    simp [dotProduct]
  · norm_num [dotProduct, Matrix.of_apply, Fin.sum_univ_two]
    linarith
  · simp [nrm, dotProduct, Matrix.of_apply, Real.sqrt_one]

/-- **agemStep (C498, def)**: the A-GEM conditional projection —
the step is FREE when the current gradient does not conflict
with the old gradient (`0 ≤ g ⬝ᵥ g_old`; first-order old-loss
change `−η·⟨g, g_old⟩ ≤ 0`), and is orthogonalized onto
`g_old^⊥` (one Gram–Schmidt iteration) on conflict. -/
noncomputable def agemStep {n : ℕ} (g g_old : Fin n → ℝ) : Fin n → ℝ :=
  if 0 ≤ g ⬝ᵥ g_old then g
  else g - (g ⬝ᵥ g_old / (g_old ⬝ᵥ g_old)) • g_old

/-- **agem_step_nonneg_interf (C498)**: the applied A-GEM rule
ALWAYS has non-negative first-order old-interference: in the
free branch by hypothesis, in the conflict branch exactly zero
(orthogonalized). Together with the free-branch reading this
is the conditional-projection guarantee: interference is never
positive first order. -/
theorem agem_step_nonneg_interf {n : ℕ} (g g_old : Fin n → ℝ)
    (hne : g_old ⬝ᵥ g_old ≠ 0) :
    0 ≤ agemStep g g_old ⬝ᵥ g_old := by
  unfold agemStep
  split
  · assumption
  · rename_i hneg
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    linarith

/-- **gpm_tradeoff (C498)**: the honest trade-off — under ONE
relaxed-orthogonality hypothesis (rows orthogonal to the
projected old inputs, and to the projected new input), BOTH
sides of the continual compromise are controlled by the SAME
tail mechanism: forgetting on each old input AND progress on
the new input are each at most `‖row‖ · sigmaTail` on the
respective input. Shrinking the tail (larger truncation rank)
shrinks forgetting but equally shrinks admissible progress;
the ε² compromise is exact, not asymptotic. -/
theorem gpm_tradeoff (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (x_new : Fin n → ℝ) (i : Fin m)
    (horth : gpmOrthP ΔW xs P)
    (hnew : ΔW i ⬝ᵥ (P *ᵥ x_new) = 0) :
    (∀ k : Fin K, |ΔW i ⬝ᵥ xs k| ≤ nrm (ΔW i) * sigmaTail P (xs k))
      ∧ |ΔW i ⬝ᵥ x_new| ≤ nrm (ΔW i) * sigmaTail P x_new := by
  constructor
  · intro k
    exact rank_trunc_forgetting_bound ΔW xs P horth i k
  · have hsplit : ΔW i ⬝ᵥ x_new = ΔW i ⬝ᵥ (x_new - P *ᵥ x_new) := by
      have h := dot_split P (ΔW i) x_new
      rw [hnew, zero_add] at h
      exact h
    rw [hsplit]
    exact cs_abs _ _

/-- **gpm_hold_when_covered (C498)**: the machine-checked form
of the C494 all-HOLD phenomenon — when the projection covers
the new input (`sigmaTail P x_new = 0`, span reached the new
directions), EVERY admissible step has exactly zero progress
on it: no step is both admissible and useful, so the method
HOLDs. Zero forgetting at full coverage and zero progress at
new-input coverage are the two faces of the same tail. -/
theorem gpm_hold_when_covered (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (x_new : Fin n → ℝ) (i : Fin m)
    (horth : gpmOrthP ΔW xs P)
    (hnew : ΔW i ⬝ᵥ (P *ᵥ x_new) = 0)
    (hcover : sigmaTail P x_new = 0) :
    ΔW i ⬝ᵥ x_new = 0 := by
  have hbound := (gpm_tradeoff ΔW xs P x_new i horth hnew).2
  rw [hcover, mul_zero] at hbound
  exact le_antisymm (abs_le.mp hbound).2 (abs_le.mp hbound).1

end Hagi.Theory.GPMRelaxed

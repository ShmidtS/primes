/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Hagi.Core.Hadamard

open scoped Matrix
set_option linter.style.header false

/-!
# Speedrun — exact readout-credit identities of forward-only boosting

Integration of the speedrun recipe (qlabs-eng/noise,
`train/speedrun/run.py`, Track 2: stagewise forward-only training
of the residual stream; every learning signal is a MEASURED change
of a loss caused by a perturbation at the site it trains).

What is formalized here (pure finite-sum identities, no
approximation):

* `cePartition_move` — moving ONE logit `j` by `δ` changes the
  softmax partition by exactly one term
  (`Z + exp(z_j + δ) − exp(z_j)`) — run.py:
  "moving one logit changes the partition function by one term";
* `ceLogit_move_change` — the RUN.PY CLOSED FORM: the CE-loss
  change of a single-logit move equals the target shift (only if
  `j` is the target) plus
  `log (1 + w_j * (exp δ − 1))` with `w_j = exp(z_j)/Z` of the
  CLEAN forward — "nothing is differentiated": the perturbed loss
  is evaluated exactly from the clean probabilities;
* `head_probe_linear` — the readout-probe identity: a linear head
  at the probed stream is the clean logits plus a precomputed
  direction, so each probe costs ONE head evaluation (the
  "readout credit" exactness).

Honest boundary: the runtime applies a soft cap `15 * tanh(z/15)`
to the logits; these identities are stated for the uncapped logits
(the cap is a bounded-range bridge hypothesis, `h_emp_` territory).
-/

namespace Hagi.Pretraining

open Finset

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The cross-entropy readout loss of logits `z` at target `y`:
`-z_y + log ∑ exp z_i` (uncapped). -/
noncomputable def ceLogit (z : k → ℝ) (y : k) : ℝ :=
  -z y + Real.log (∑ i, Real.exp (z i))

/-- **Partition identity of a single-logit move** (run.py):
bumping coordinate `j` by `δ` changes the softmax partition by
exactly one term. -/
theorem cePartition_move (z : k → ℝ) (j : k) (δ : ℝ) :
    (∑ i, Real.exp (Function.update z j (z j + δ) i))
      = (∑ i, Real.exp (z i)) + Real.exp (z j + δ) - Real.exp (z j) := by
  classical
  have hsplit : ∑ i, Real.exp (Function.update z j (z j + δ) i)
      = Real.exp (Function.update z j (z j + δ) j)
        + ∑ i ∈ Finset.univ.erase j,
          Real.exp (Function.update z j (z j + δ) i) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  have hbase : ∑ i, Real.exp (z i)
      = Real.exp (z j) + ∑ i ∈ Finset.univ.erase j, Real.exp (z i) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  have hsame : ∑ i ∈ Finset.univ.erase j,
      Real.exp (Function.update z j (z j + δ) i)
      = ∑ i ∈ Finset.univ.erase j, Real.exp (z i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (by simpa using Finset.ne_of_mem_erase hi)]
  rw [Function.update_self] at hsplit
  rw [hsplit, hsame, hbase]
  ring

/-- **Factorization of the moved partition**: the moved partition
is the clean partition times the closed-form factor
`1 + w_j (exp δ − 1)`. -/
theorem cePartition_factor (z : k → ℝ) (j : k) (δ : ℝ)
    (hW : 0 < ∑ i, Real.exp (z i)) :
    (∑ i, Real.exp (Function.update z j (z j + δ) i))
      = (∑ i, Real.exp (z i))
        * (1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1)) := by
  have hmove := cePartition_move z j δ
  have hZn : (∑ i, Real.exp (z i)) ≠ 0 := ne_of_gt hW
  have hrw2 : Real.exp (z j + δ) = Real.exp (z j) * Real.exp δ :=
    Real.exp_add _ _
  have h := hmove
  rw [hrw2] at h
  have : (∑ i, Real.exp (z i)) + Real.exp (z j) * Real.exp δ
        - Real.exp (z j)
      = (∑ i, Real.exp (z i))
        * (1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1)) := by
    field_simp
    ring
  rw [h]
  exact this

/-- **The run.py closed form** (coordinate-difference readout
credit): the CE-loss change of a single-logit move `z_j ↦ z_j + δ`
is exactly the target shift (only if `j = y`) plus
`log (1 + w_j (exp δ − 1))` — evaluated from the clean forward's
probabilities alone. Two closed-form evaluations per coordinate;
no backprop, no numerical differentiation. -/
theorem ceLogit_move_change (z : k → ℝ) (y j : k) (δ : ℝ)
    (hW : 0 < ∑ i, Real.exp (z i)) :
    ceLogit (Function.update z j (z j + δ)) y - ceLogit z y
      = -(if j = y then δ else 0)
        + Real.log (1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1)) := by
  classical
  have hty : Function.update z j (z j + δ) y
      = z y + (if j = y then δ else 0) := by
    by_cases hjy : j = y
    · subst hjy; simp
    · have hyj : y ≠ j := fun h => hjy h.symm
      rw [Function.update_of_ne hyj]
      simp [hjy]
  have hfac := cePartition_factor z j δ hW
  have hZn : (∑ i, Real.exp (z i)) ≠ 0 := ne_of_gt hW
  have hnonnegR : (0:ℝ) < 1 + Real.exp (z j) / (∑ i, Real.exp (z i))
      * (Real.exp δ - 1) := by
    have hratio : (∑ i, Real.exp (Function.update z j (z j + δ) i))
        / (∑ i, Real.exp (z i))
        = 1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1) := by
      rw [hfac]
      field_simp
    have hpos' : (0:ℝ) < ∑ i, Real.exp (Function.update z j (z j + δ) i) :=
      Finset.sum_pos' (fun i _ => Real.exp_nonneg _)
        ⟨j, Finset.mem_univ j, Real.exp_pos _⟩
    rw [← hratio]
    exact div_pos hpos' hW
  have hstep : Real.log ((∑ i, Real.exp (z i))
        * (1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1)))
      = Real.log (∑ i, Real.exp (z i))
        + Real.log (1 + Real.exp (z j) / (∑ i, Real.exp (z i))
          * (Real.exp δ - 1)) :=
    Real.log_mul hZn (ne_of_gt hnonnegR)
  unfold ceLogit
  rw [hty, hfac, hstep]
  ring

/-- **Readout-probe linearity** (run.py: "the head is linear in
the stream, so a probe's logits are the clean logits plus a
precomputed direction"): a linear head at the probed stream
`x + σ • d` equals `h x + σ • (h d)` — each probe costs ONE head
evaluation with a precomputed direction. -/
theorem head_probe_linear {X : Type*} [AddCommGroup X] [Module ℝ X]
    (h : X →ₗ[ℝ] X) (x d : X) (σ : ℝ) :
    h (x + σ • d) = h x + σ • (h d) := by
  rw [map_add, map_smul]


/-! ### Hadamard-probe inversion (run.py: forward differences along
all rows of a sign matrix give each coordinate's credit in full) -/

/-- **Hadamard-probe inversion**: with row-orthogonal probes
(`H * Hᵀ = c • 1`, `c ≠ 0`), full-batch sign-probe measurements
`g r = ⟨H r, Δ⟩` (one forward evaluation per row) recover the
coordinate-credit vector `Δ` EXACTLY: `Δ = c⁻¹ • (Hᵀ *ᵥ g)`.

The run.py economy: k forward evaluations (k Hadamard rows) give
ALL k coordinates of the credit — versus 2k finite-difference
evaluations coordinate by coordinate — and the recovery is an
identity, not an estimator. -/
theorem hadamard_probe_inversion {m : Type*} [Fintype m]
    [DecidableEq m] (H : Matrix m m ℝ) (Δ g : m → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hmul : H * Hᵀ = c • 1)
    (hg : ∀ r, g r = ∑ k, H r k * Δ k) :
    Δ = (c⁻¹) • (Hᵀ *ᵥ g) := by
  classical
  have hHB : H * ((c⁻¹ : ℝ) • Hᵀ) = 1 := by
    rw [Matrix.mul_smul, hmul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hdet : H.det ≠ 0 := by
    intro h0
    have h2 : (H * ((c⁻¹:ℝ) • Hᵀ)).det = 1 := by rw [hHB]; simp
    rw [Matrix.det_mul, h0, zero_mul] at h2
    norm_num at h2
  have hUd : IsUnit H.det := IsUnit.mk0 H.det hdet
  have hU : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hUd
  have hBinv : (c⁻¹ : ℝ) • Hᵀ = H⁻¹ := by
    rw [← Matrix.mul_one H⁻¹, ← hHB, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul H hUd, Matrix.one_mul]
  have hTH : Hᵀ * H = c • 1 := by
    have h2 : ((c⁻¹ : ℝ) • Hᵀ) * H = 1 := by
      rw [hBinv, Matrix.nonsing_inv_mul H hUd]
    rw [Matrix.smul_mul] at h2
    have h3 := congrArg (fun X : Matrix m m ℝ => c • X) h2
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at h3
    exact h3
  have hgv : g = H *ᵥ Δ := funext fun r => hg r
  have key : Hᵀ *ᵥ g = c • Δ := by
    rw [hgv, Matrix.mulVec_mulVec, hTH, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [key, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Hagi.Pretraining

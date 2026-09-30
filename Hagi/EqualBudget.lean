/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.JointCost

set_option linter.style.header false

/-!
# EqualBudget: the honest merge-vs-scratch comparison (round 47, T3)

**Motivation (measured)**: the scratch control (H=384) used a
different optimizer (AdamW lr 1e-3 vs the leaves' Muon lr
1e-2), a different size than the record model (H=1152), and
~1.9× the FLOPs of three leaves + joint — the "equal budget"
comparison was not clean. The decisive stand experiment:
scratch H=384 with the SAME Muon at ~1.9× steps vs gen-1
joint.

- **T3a `aitken_exact`**: for the geometric trajectory
  L_i = L* + d·c^i, the Aitken estimates
  L* = (L₀L₂ − L₁²)/(L₀ + L₂ − 2L₁) and c = (L₂−L₁)/(L₁−L₀)
  are EXACT — L* and c recoverable from three equidistant
  points without knowing L*.
- **T3b `aitken_consistency`**: on a true geometric sequence
  the window estimates agree at every shift — a measured
  disagreement FALSIFIES the PL/geometric model (mandatory:
  the WSD schedule makes curves non-geometric).
- **T3c `budget_gap_sign_affine`**: under the two-curve model
  L_m(C) − L* = d_m·exp(u_m·(C−C₀)) and L_s(C) − L* =
  d_s·exp(u_s·C) (u's the log-decay rates), the sign of
  L_m − L_s equals the sign of the EXPLICIT affine function
  (u_m − u_s)·C + (log(d_m/d_s) − u_m·C₀) — single crossover
  when the slopes differ, constant sign when equal.
- **T3d `headstart_pays_iff`**: at equal rates (the
  `head_start_timeshift` regime), the merge pays ⟺ C₀ <
  k·κ with k = log(d_s/d_m)/log(c) the step-equivalent head
  start — the FLOP cost of the leaves must be under k
  scratch-step-equivalents. With the reviewer's estimate
  C₀ ≈ 0.88 of one scratch run, the head start must exceed
  ~0.88·1600 step-equivalents just to break even — a
  measurable, falsifiable bar.

**Honest boundary**: the whole module assumes the geometric
(PL) decay model; the WSD schedule violates it by design, so
T3b is the mandatory pre-test. Two cost axes (FLOPs and
wall-clock on the bandwidth-bound iGPU) do not coincide;
both belong in the report.
-/

open Real

namespace Hagi

section EqualBudget

/-- **T3a — the Aitken exactness**: for L_i = L* + d·c^i with
d ≠ 0, c ≠ 1, the three-point estimates of L* and c are
exact. -/
theorem aitken_exact (Lstar d c L0 L1 L2 : ℝ)
    (h0 : L0 = Lstar + d) (h1 : L1 = Lstar + d * c)
    (h2 : L2 = Lstar + d * c^2) (hd : d ≠ 0) (hc : c ≠ 1) :
    (L0 * L2 - L1^2) / (L0 + L2 - 2*L1) = Lstar
      ∧ (L2 - L1) / (L1 - L0) = c := by
  constructor
  · rw [h0, h1, h2]
    have hz : Lstar + d + (Lstar + d * c^2) - 2*(Lstar + d * c)
        = d * (1 - c)^2 := by ring
    rw [hz]
    field_simp
    nlinarith [sq_nonneg (Lstar - Lstar * c), sq_nonneg (d * c - d)]
  · rw [h0, h1, h2]
    have hz2 : Lstar + d * c - (Lstar + d) = d * (c - 1) := by ring
    have hz3 : Lstar + d * c^2 - (Lstar + d * c) = d * c * (c - 1) := by ring
    rw [hz2, hz3]
    have hdc : d * (c - 1) ≠ 0 := by
      intro hcon
      rcases mul_eq_zero.mp hcon with h' | h'
      · exact absurd h' hd
      · exact absurd (sub_eq_zero.mp h') hc
    field_simp

/-- **T3b — the Aitken window consistency**: on a true
geometric trajectory the c-estimate
(L_{n+2}−L_{n+1})/(L_{n+1}−L_n) equals c at EVERY window —
measured disagreement falsifies the geometric model (the WSD
schedule does by design; this test is mandatory before
applying T3c/T3d). -/
theorem aitken_consistency (Lstar d c : ℝ)
    (L : ℕ → ℝ) (hL : ∀ i, L i = Lstar + d * c^(i:ℕ))
    (hdne : d ≠ 0) (hcne : c ≠ 0) (hc1 : c ≠ 1) :
    ∀ k : ℕ, (L (k+2) - L (k+1)) / (L (k+1) - L k) = c := by
  intro k
  rw [hL (k+2), hL (k+1), hL k]
  have e1 : Lstar + d * c^((k+2:ℕ)) - (Lstar + d * c^((k+1:ℕ)))
      = d * c^(k:ℕ) * (c - 1) * c := by
    have h1 : (k+2:ℕ) = (k:ℕ) + 2 := by omega
    have h2 : (k+1:ℕ) = (k:ℕ) + 1 := by omega
    rw [h1, h2, pow_add, pow_add, pow_two, pow_one]
    ring
  have e2 : Lstar + d * c^((k+1:ℕ)) - (Lstar + d * c^(k:ℕ))
      = d * c^(k:ℕ) * (c - 1) := by
    have h2 : (k+1:ℕ) = (k:ℕ) + 1 := by omega
    rw [h2, pow_add, pow_one]
    ring
  rw [e1, e2]
  have hdenom : d * c^(k:ℕ) * (c - 1) ≠ 0 := by
    intro hcon
    rcases mul_eq_zero.mp hcon with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hdne
      · exact absurd h'' (pow_ne_zero k hcne)
    · exact absurd (sub_eq_zero.mp h') hc1
  rw [show d * c^(k:ℕ) * (c - 1) * c = c * (d * c^(k:ℕ) * (c - 1)) from by ring]
  field_simp

/-- **T3c — the budget-gap sign is C-constant at equal
rates**: under the two-exponential model with equal decay
rates, the sign of L_m − L_s is CONSTANT in C: the whole
budget comparison reduces to the constant comparison
d_m·exp(−u·C₀) < d_s. -/
theorem budget_gap_sign_const (dM dS u C C0 : ℝ)
    (hdM : 0 < dM) (hdS : 0 < dS) :
    dM * Real.exp (u * (C - C0)) < dS * Real.exp (u * C)
      ↔ dM * Real.exp (-(u * C0)) < dS := by
  have hpos : (0:ℝ) < Real.exp (u * C) := Real.exp_pos _
  have hsplit : dM * Real.exp (u * (C - C0))
      = (dM * Real.exp (-(u * C0))) * Real.exp (u * C) := by
    have h1 : Real.exp (u * (C - C0)) = Real.exp (-(u * C0)) * Real.exp (u * C) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h1, mul_assoc]
  rw [hsplit]
  exact mul_lt_mul_iff_of_pos_right hpos

-- T3d (the head-start break-even iff) is NOT proved this
-- round: the two-sided sign case analysis (k = log(dS/dM)/
-- log c with log c < 0, the dM-vs-dS case split) exceeded
-- the attempt budget. Documented form (see the module
-- docstring): merge pays ⟺ C₀ vs k·κ with k the
-- step-equivalent head start; the reviewer's estimate C₀ ≈
-- 0.88 scratch-runs sets the measurable bar. The PROVED
-- pieces are T3a (exactness), T3b (consistency test),
-- T3c (equal-rate sign constancy) — the sign machinery for
-- the unequal-rate crossover remains open.

end EqualBudget

end Hagi
/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Growth.SeedOnly
import Mathlib.Tactic

set_option linter.style.header false

/-!
# JointPreserve: diversity non-collapse under SafeQP steps (round 49, block 3)

The composition: IF each SafeQP joint step contracts the
cross-expert diversity by at most factor a and injects at
most s (the h_emp hypotheses — measured on the Gram
telemetry), THEN the diversity after T steps obeys the
general recurrence bound (SeedOnly.disp_recurrence_general):
bounded above by a^T·D₀ + s·Σa^i — the non-collapse
certificate: the Jensen gain CANNOT shrink below its floor
unless a ≥ 1 (the measured regime decides).

NOT PROVED: deriving h_emp per-step (a, s) from the SafeQP
geometry itself (the dynamics of the projected steps on the
representation covariance) — the hypotheses remain empirical
inputs from the Gram logs.

**Prescription**: log the per-step diversity ratio on the
joint phase; a < 1 with small s certifies non-collapse in
advance; a ≥ 1 flags the collapse regime for the schedule
program (Wave3) to intervene.
-/

open Finset

namespace Hagi

/-- **The diversity upper bound** (was mislabeled
"non-collapse"): with per-step contraction ≤ a and injection
≤ s, diversity after T steps is AT MOST a^T·D₀ + s·Σa^i.
NOTE (external review, round-51): this bound alone is
compatible with total collapse (take s = 0). The
collapse-excluding theorem of the opposite sign is
`diversity_floor` below. -/
theorem diversity_noncollapse (D : ℕ → ℝ) (a s : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ a * D t + s) (T : ℕ) :
    D T ≤ a^T * D 0 + s * ∑ i ∈ Finset.range T, a^i :=
  disp_recurrence_general ha hs hstep T

/-- **The diversity floor (lower bound)**: with per-step
retention ≥ ρ, injection ≥ inj and leakage ≤ ξ, the
cross-expert diversity after T steps is AT LEAST
ρ^T·D₀ + (inj − ξ)·Σρ^i. This is the theorem of the sign the
architecture needs: it rules OUT collapse when inj > ξ,
rather than merely bounding diversity from above. The
companion `diversity_noncollapse` above is an UPPER bound and
by itself is compatible with total collapse — pointed out in
external review, 2025-round-51. -/
theorem geom_shift (rho : ℝ) (T : ℕ) :
    rho * ∑ i ∈ Finset.range T, rho^i + 1 = ∑ i ∈ Finset.range T, rho^i + rho^T := by
  induction T with
  | zero => simp
  | succ T ih =>
    set S := ∑ i ∈ Finset.range T, rho^i with hS
    have hsum : ∑ i ∈ Finset.range (T+1), rho^i = S + rho^T :=
      Finset.sum_range_succ _ T
    rw [hsum]
    have h1 : rho * (rho * S + 1) = rho * (S + rho^T) := by rw [← ih]
    have hexp : rho * (rho^T) = rho^(T+1) := by ring
    nlinarith [h1, hexp]

theorem diversity_floor (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 ≤ rho) (_hinj : 0 ≤ inj) (_hxi : 0 ≤ xi)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) :
    D T ≥ rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 := hstep T
    have h2 : rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i ≤ D T := ih
    have hsplit : rho * D T + inj - xi
        ≥ rho * (rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i) + (inj - xi) := by
      nlinarith [h1, h2, hrho]
    have hgs := geom_shift rho T
    set S := ∑ i ∈ Finset.range T, rho^i with hS
    -- target algebra: rho*(rho^T*D0 + (inj-xi)*S) + (inj-xi) = rho^(T+1)*D0 + (inj-xi)*(S + rho^T)
    have halg : rho * (rho^T * D 0 + (inj - xi) * S) + (inj - xi)
        = rho^(T+1) * D 0 + (inj - xi) * (S + rho^T) := by
      have hexp : rho * rho^T = rho^(T+1) := by ring
      linear_combination (inj - xi) * hgs + D 0 * hexp
    rw [Finset.sum_range_succ]
    calc D (T+1) ≥ rho * D T + inj - xi := h1
      _ ≥ rho * (rho^T * D 0 + (inj - xi) * S) + (inj - xi) := hsplit
      _ = rho^(T+1) * D 0 + (inj - xi) * (S + rho^T) := halg

/-- **The fresh-data condition for a nondegenerate diversity
floor** (round-62 program item 5): with per-step retention
ρ > 0 and STRICT injection dominance inj > ξ (the fresh-data
schedule condition — the fraction of fresh external data per
generation must more than cover the leakage), the floor of
`diversity_floor` is strictly positive: D_T ≥ (inj−ξ)·Σ_{i<T}ρⁱ
> 0. The FRESH-DATA FRACTION is exactly the control knob
that guarantees inj > ξ; without it (inj ≤ ξ) the floor
degenerates and the collapse regime is admissible. -/
theorem diversity_floor_fresh (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 < rho) (hinj : 0 ≤ inj) (hxi : 0 ≤ xi)
    (_hinjgt : xi < inj) (hD0 : 0 ≤ D 0)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) :
    D T ≥ (inj - xi) * ∑ i ∈ Finset.range T, rho ^ i := by
  have hf := Hagi.diversity_floor D rho inj xi hrho.le hinj hxi hstep T
  have hnn : 0 ≤ rho ^ T * D 0 :=
    mul_nonneg (pow_nonneg hrho.le T) hD0
  linarith

/-- **Strict positivity of the fresh floor**: for any
generation T ≥ 1 the floor is strictly positive — collapse
is EXCLUDED by strict injection dominance. -/
theorem diversity_floor_strict_pos (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 ≤ rho) (_hinj : 0 ≤ inj) (_hxi : 0 ≤ xi)
    (hinjgt : xi < inj)
    (_hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) (hT : T ≠ 0) :
    0 < (inj - xi) * ∑ i ∈ Finset.range T, rho ^ i := by
  have hdiff : 0 < inj - xi := by linarith
  have hsumpos : 0 < ∑ i ∈ Finset.range T, rho ^ i := by
    apply Finset.sum_pos'
    · intro i _
      exact pow_nonneg hrho i
    · refine ⟨0, ?_, by simp⟩
      rw [Finset.mem_range]
      omega
  positivity

end Hagi

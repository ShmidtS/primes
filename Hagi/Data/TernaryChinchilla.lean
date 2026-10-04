/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.Muon
set_option linter.style.header false

/-!
# R149: ternary Chinchilla - capacity-scaled scaling law

Phase C (R141 of the plan, external gap no. 2).
Sources: Chinchilla law L = E + A/N^alpha + B/D^beta;
2609.36437 (bit-sensitivity split: weights tolerate fewer
bits, activations need 12-14 bits - the b-member is
separate), 2607.14630 (1.125 bits/weight binarization),
2610.00983 (10^4x reconstruction-loss spread).

Model: the parameter member of the loss is scaled by the
per-weight information capacity b: A/(b*N)^alpha.

Theorems:

* `capacity_member_mono` - for a FIXED parameter count the
capacity member strictly decreases as b grows.
* `ternary_beats_binary` - instantiated: ternary capacity
b = log2(3) beats binary b = 1 in the parameter term.

Honest boundary: the FULL compute-optimal shift (the N*/D*
rebalance at a fixed budget) requires joint first-order
conditions with the empirical constants A, B, alpha, beta
(h_emp data, out of Lean scope); here the exact statement
is the capacity-member comparison.
-/

namespace Hagi

/-- The capacity-scaled parameter member of the Chinchilla
law: A / (b * N)^alpha. -/
noncomputable def capMember (A b N alpha : ℝ) : ℝ :=
  A / (b * N)^alpha

/-- Monotonicity in the capacity: for a fixed parameter
count the parameter member strictly decreases as the
per-weight capacity b grows. -/
theorem capacity_member_mono (A N alpha b1 b2 : ℝ)
    (hA : 0 < A) (hN : 0 < N) (halpha : 0 < alpha)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (h12 : b1 < b2) :
    capMember A b2 N alpha < capMember A b1 N alpha := by
  unfold capMember
  have hkey : (b1 * N)^alpha < (b2 * N)^alpha :=
    Real.rpow_lt_rpow (by positivity)
      (mul_lt_mul_of_pos_right h12 hN) halpha
  have hpow1 : 0 < (b1 * N)^alpha := by positivity
  have hpow2 : 0 < (b2 * N)^alpha := by positivity
  rw [div_lt_div_iff₀ hpow2 hpow1]
  exact mul_lt_mul_of_pos_left hkey hA

/-- Instantiated: ternary capacity b = log2(3) beats
binary b = 1 in the parameter term. -/
theorem ternary_beats_binary (A N alpha : ℝ)
    (hA : 0 < A) (hN : 0 < N) (halpha : 0 < alpha) :
    capMember A (Real.log 3 / Real.log 2) N alpha
      < capMember A 1 N alpha := by
  apply capacity_member_mono A N alpha _ _
    hA hN halpha (by norm_num) (by positivity)
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [one_lt_div h2]
  exact Real.log_lt_log (by norm_num : (0:ℝ) < 2)
    (by norm_num)

end Hagi

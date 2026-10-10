/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.MergePrice

/-!
# PolicyCompatibility — the MOPD amendment to the merge gate

Empirical source (flagged, not proved): MOPD (multi-teacher
on-policy distillation). When a much stronger teacher with a
large policy-distribution gap was attached, the initial KL was
~5x larger, policy-gradient variants degraded, and top-k
variants diverged. Integration value is not capability alone:

  capability gain × compatibility

must be positive. A strong-but-far expert can be WORSE than no
integration.

This module adds the compatibility clause to the HAGI merge
gate WITHOUT touching `merge_gate_certified` (the certified
price/gap gate stands; this is the second, orthogonal gate):

* `integration_net_gain` — the signed integration value:
  twoGap minus price;
* `MOPDApproved` — the two-clause gate: positive net gain
  AND policy divergence under the cap;
* `integration_rejects_far_teacher` — the NEGATIVE result:
  divergence above the cap keeps the gate closed however
  large the raw capability gap is — the formal core of the
  MOPD amendment;
* `mopd_kl_scaling_warning` — the conditional instability
  propagation: under the (flagged) empirical scaling law,
  a λ-fold divergence growth forces the tolerance budget
  down by the same factor.
-/

namespace Hagi.Ensemble

/-- The signed integration value: ensemble gap minus total
price (the quantity the certified gate compares to zero). -/
noncomputable def integration_net_gain (twoGap : ℝ)
    (price : ℝ) : ℝ := twoGap - price

/-- **The two-clause MOPD gate**: integrate iff the net gain
is positive AND the policy divergence is within the
compatibility cap. The clauses are independent: raw capability
does not substitute for compatibility. -/
def MOPDApproved (twoGap price Dpolicy Dmax : ℝ) : Prop :=
  0 < integration_net_gain twoGap price ∧ Dpolicy ≤ Dmax

theorem integration_net_gain_pos {twoGap price Dpolicy Dmax : ℝ}
    (h : MOPDApproved twoGap price Dpolicy Dmax) :
    0 < integration_net_gain twoGap price := h.1

/-- **The negative result (the MOPD amendment)**: divergence
above the compatibility cap keeps the gate closed for ANY
capability level — there is no twoGap large enough to buy
compatibility. -/
theorem integration_rejects_far_teacher {twoGap price Dpolicy Dmax : ℝ}
    (hfar : Dmax < Dpolicy) :
    ¬ MOPDApproved twoGap price Dpolicy Dmax :=
  fun h => absurd h.2 (not_le.2 hfar)

/-- **Conditional instability scaling (flagged empirical
premise)**: if the policy divergence scales as λ times the
baseline (the MOPD far-teacher regime, measured λ ≈ 5), then
any tolerance ε on the KL trajectory forces the divergence
budget down by the same factor λ: the far teacher must be
integrated λ times more gently, or not at all. -/
theorem mopd_kl_scaling_warning {Dbase Dpolicy : ℝ}
    (h_emp_scaling : Dpolicy = 5 * Dbase)
    (_hbase : 0 < Dbase)
    {ε : ℝ} (heps : 0 < ε)
    (hsafe : Dpolicy * ε ≤ 1) :
    Dbase ≤ 1 / ε / 5 := by
  have h1 : 5 * Dbase * ε ≤ 1 := by
    rw [← h_emp_scaling]; exact hsafe
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 5)]
  rw [le_div_iff₀ heps]
  linarith

end Hagi.Ensemble

namespace Hagi
export Hagi.Ensemble (integration_net_gain MOPDApproved integration_net_gain_pos integration_rejects_far_teacher mopd_kl_scaling_warning)
end Hagi

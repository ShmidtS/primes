/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGI

/-!
# MasterHAGICoupled — closing the three structural gaps of the
capstone flagged by the external audit (R246)

The external static audit of the whole `Hagi` tree found the
capstone contract honest but weaker than it reads in three
specific places. This module adds the strengthened forms;
each fix is a REAL hypothesis added, so the old theorems
remain valid — these are the versions a runtime certificate
should target:

1. **State-capability coupling** (audit §22): in
`CertifiedHAGIInvariant` the capability channel `cap t` is a
free sequence — the growth claim `cap 0 (1+α)^T ≤ cap T`
says nothing about the STATES. `CoupledHAGIInvariant` adds
`cap t = (S t).toGrowthState.capability`: the exponential
bound is now a bound on the actual state trajectory.

2. **Nonnegative ledger** (audit §23): `spend t ≥ 0` and
per-stage risks ≥ 0 are now hypotheses — without them
`budget T = budget 0 − ∑ spend` permits a budget that
GROWS, and the risk account is not a physical ledger.
`budget_no_growth`: under nonneg spends the budget is
nonincreasing.

3. **Vector generalization floor** (audit §24): a scalar
`Qfloor ≤ Qgen` can hide a catastrophic collapse of one
probe behind growth of others. `qvec_floor` keeps EVERY
component above its floor; `qvec_floor_implies_scalar`:
the vector floor implies any nonneg-weighted scalar floor —
the scalar version is derived, not primary.
-/

open scoped BigOperators

namespace Hagi.Master

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The capability channel read off the states. -/
def capChannel (S : ℕ → GrowthState X) (t : ℕ) : ℝ :=
  (S t).capability

/-- **The coupled capstone contract**: the audit-§22 fix —
capability channel IS the state trajectory's capability,
spends and risks are a physical (nonnegative) ledger, and
the generalization floor is componentwise. -/
structure CoupledHAGIInvariant (T : ℕ)
    (S : ℕ → GrowthState X)
    (risk spend : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ)
    (alpha : ℝ) where
  /-- The capability channel is the STATE's capability
  (audit §22 coupling). -/
  cap_is_state : ∀ t ≤ T, (S t).capability = capChannel S t
  /-- Safety telescoped, as before. -/
  risk_bound : (S T).protectedRisk - (S 0).protectedRisk
    ≤ ∑ t ∈ Finset.range T, risk t
  /-- Physical ledger: spends are nonnegative (audit §23). -/
  spend_nonneg : ∀ t ∈ Finset.range T, 0 ≤ spend t
  risk_nonneg : ∀ t ∈ Finset.range T, 0 ≤ risk t
  /-- Budget account with a physical direction. -/
  budget_account : (S T).budget = (S 0).budget
    - ∑ t ∈ Finset.range T, spend t ∧ 0 ≤ (S T).budget
  /-- Growth on the STATE trajectory (not a free channel). -/
  capability_growth :
    (S 0).capability * (1 + alpha) ^ T ≤ (S T).capability
  /-- Componentwise generalization floor (audit §24). -/
  qvec_floor : ∀ i, qfloor i ≤ qvec T i

/-- **Budget never grows under a physical ledger** (audit
§23 consequence): with nonnegative spends, the terminal
budget is at most the initial one. -/
theorem budget_no_growth (T : ℕ) (S : ℕ → GrowthState X)
    (spend : ℕ → ℝ)
    (hacc : (S T).budget = (S 0).budget
      - ∑ t ∈ Finset.range T, spend t)
    (hsp : ∀ t ∈ Finset.range T, 0 ≤ spend t) :
    (S T).budget ≤ (S 0).budget := by
  have hsum : 0 ≤ ∑ t ∈ Finset.range T, spend t :=
    Finset.sum_nonneg hsp
  rw [hacc]
  linarith

/-- **The vector floor implies any nonnegative-weighted
scalar floor** (audit §24: scalar is derived, vector is
primary): if every probe component stays above its floor
then every convex (nonneg weights) scalar aggregate stays
above the aggregated floor. -/
theorem qvec_floor_implies_scalar (T : ℕ)
    (qvec : ℕ → Fin 5 → ℝ) (qfloor : Fin 5 → ℝ)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hvec : ∀ i, qfloor i ≤ qvec T i) :
    ∑ i, w i * qfloor i ≤ ∑ i, w i * qvec T i := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hvec i) (hw i)

/-- **No single-component rescue**: if component j sits
BELOW its floor by δ yet the scalar floor still holds, the
other components must overcompensate by at least w j · δ —
the exact mechanism by which a scalar Qgen hides a
component collapse (audit §24), now quantified. -/
theorem scalar_hides_deficit (T : ℕ)
    (qvec : ℕ → Fin 5 → ℝ) (qfloor : Fin 5 → ℝ)
    (w : Fin 5 → ℝ) (j : Fin 5) (delta : ℝ)
    (hbelow : qvec T j + delta = qfloor j)
    (hscalar : ∑ i, w i * qfloor i ≤ ∑ i, w i * qvec T i) :
    w j * delta ≤ ∑ i ∈ Finset.univ.erase j,
      w i * (qvec T i - qfloor i) := by
  have hsplit := Finset.sum_erase_add (Finset.univ)
    (fun i => w i * qvec T i) (Finset.mem_univ j)
  have hsplitF := Finset.sum_erase_add (Finset.univ)
    (fun i => w i * qfloor i) (Finset.mem_univ j)
  have hsplitD : ∑ i ∈ Finset.univ.erase j,
      w i * (qvec T i - qfloor i)
      = (∑ i ∈ Finset.univ.erase j, w i * qvec T i)
        - ∑ i ∈ Finset.univ.erase j, w i * qfloor i := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext i
    ring
  rw [← hsplit, ← hsplitF, ← hbelow] at hscalar
  have hdiff : ∑ i ∈ Finset.univ.erase j, w i * qvec T i
      - ∑ i ∈ Finset.univ.erase j, w i * qfloor i
      = ∑ i ∈ Finset.univ.erase j, w i * (qvec T i - qfloor i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [← hdiff]
  linarith [hscalar]


end Hagi.Master

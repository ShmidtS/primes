/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

set_option linter.style.header false

/-!
# R263 (audit §7.1): the h_emp_merge bridge from the Core layer

The audit's central gap: no `h_emp_*` premise of the capstone
was ever derived from the Core-layer mathematics. This module
derives the MERGE stage law for the two-expert concat model:

For two children `z₁, z₂` (a token `t`), the Core ensemble
theorem (`ensemble_ce_le_mean`, Jensen for `lse`) gives

  CE(t, mid) ≤ (CE(t, z₁) + CE(t, z₂)) / 2,

where `mid = (z₁+z₂)/2` is the flat-concat merged model. We
define the measured Jensen gap

  `jensenGap z₁ z₂ := (lse z₁ + lse z₂)/2 − lse mid`

(the normalizer-level disagreement the children average away)
and prove the bridge as an EQUALITY:

  `merge_energy_bridge`: CE(t, mid) = mean CE − jensenGap,
  `jensenGap_nonneg`:     0 ≤ jensenGap.

Instantiating the stage ledger fields
`growEnergy := mean CE`, `mergeEnergy := CE(t, mid)`,
`gap := jensenGap z₁ z₂` therefore satisfies h_emp_merge
exactly (`h_emp_merge_of_bridge`), with `gap` independently
grounded in the Core `lse` theory — the first nonvacuous
`h_emp_*` instantiation beyond the ternary distortion witness
(`Unified.Nonvacuity`).
-/

open Real Finset Hagi

namespace Hagi.MergeBridge

variable {k : Type} [Fintype k] [Nonempty k]

/-- The measured Jensen gap of a two-child merge: the
normalizer-level disagreement `lse-mean − lse-mid` the flat
concat averages away (Core `lse` theory). -/
noncomputable def jensenGap (z₁ z₂ : k → ℝ) : ℝ :=
  (Hagi.lse z₁ + Hagi.lse z₂) / 2 - Hagi.lse ((z₁ + z₂) / 2)

/-- The gap is nonnegative — Jensen for `lse` (Core). -/
theorem jensenGap_nonneg (z₁ z₂ : k → ℝ) : 0 ≤ jensenGap z₁ z₂ := by
  have h := Hagi.lse_midpoint_le z₁ z₂
  unfold jensenGap
  linarith

/-- **The merge-energy bridge**: for every token `t`, the merged
model's cross-entropy is EXACTLY the children's mean minus the
Jensen gap. Both the stage law `mergeEnergy ≤ growEnergy − gap`
(read: an equality here) and the sign `gap ≥ 0` follow. -/
theorem merge_energy_bridge (t : k) (z₁ z₂ : k → ℝ) :
    Hagi.ceOneHot t ((z₁ + z₂) / 2)
      = (Hagi.ceOneHot t z₁ + Hagi.ceOneHot t z₂) / 2 - jensenGap z₁ z₂ := by
  have hmid : ((z₁ + z₂) / 2) t = (z₁ t + z₂ t) / 2 := by simp
  unfold Hagi.ceOneHot jensenGap
  rw [hmid]
  field_simp
  ring

/-- **h_emp_merge instantiated by the Core ensemble theory**:
with the stage ledger fields read off the two-expert concat
model (`growEnergy` = the children's mean CE, `mergeEnergy` =
the merged model's CE, `gap` = the measured Jensen gap), the
capstone's merge premise holds — derived, not assumed. -/
theorem h_emp_merge_of_bridge (t : k) (z₁ z₂ : k → ℝ) :
    Hagi.ceOneHot t ((z₁ + z₂) / 2)
      ≤ (Hagi.ceOneHot t z₁ + Hagi.ceOneHot t z₂) / 2
        - jensenGap z₁ z₂
      ∧ 0 ≤ jensenGap z₁ z₂ :=
  ⟨le_of_eq (merge_energy_bridge t z₁ z₂), jensenGap_nonneg z₁ z₂⟩

end Hagi.MergeBridge

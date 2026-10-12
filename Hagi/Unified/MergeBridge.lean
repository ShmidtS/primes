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

namespace Hagi.Unified

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

/-!
## Strict positivity witness (R356)

The Jensen gap is not just nonnegative — it is STRICTLY
positive for real disagreements. Concrete two-logit witness:
children `z₁ = (0, 0)` and `z₂ = (a, −a)` (a ≠ 0) have

  jensenGap = ½·log(cosh a) − log(cosh (a/2)) > 0,

because `cosh²(a/2) = (1 + cosh a)/2 < cosh a` for `a ≠ 0`
(half-angle identity + `1 < cosh a`). This kills the
"gap = 0 idle witness" degeneracy: merging two genuinely
disagreeing experts STRICTLY beats their mean.
-/

/-- Half-angle identity via `cosh(2x) = 2cosh²x − 1`. -/
private theorem cosh_half_sq (x : ℝ) :
    Real.cosh x ^ 2 = (Real.cosh (2 * x) + 1) / 2 := by
  have h1 := Real.cosh_two_mul x
  have h2 := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-- The strict Jensen-gap witness: for the two-logit family
`z₁ = (0,0)`, `z₂ = (a,−a)` with `a ≠ 0`, the merge gap is
strictly positive — merging two genuinely disagreeing
experts STRICTLY beats their mean. -/
theorem jensenGap_pos_witness (a : ℝ) (ha : a ≠ 0) :
    0 < jensenGap
      (fun _ : Fin 2 => (0:ℝ))
      (fun i : Fin 2 => if i = 0 then a else -a) := by
  set z1 : Fin 2 → ℝ := fun _ => 0 with hz1
  set z2 : Fin 2 → ℝ := fun i => if i = 0 then a else -a with hz2
  have hz20 : z2 0 = a := by norm_num [hz2]
  have hz21 : z2 1 = -a := by norm_num [hz2]
  have hea : Real.exp a + Real.exp (-a) = 2 * Real.cosh a := by
    simp only [Real.cosh_eq]
    ring
  have heh : Real.exp (a / 2) + Real.exp (-(a / 2))
      = 2 * Real.cosh (a / 2) := by
    simp only [Real.cosh_eq]
    ring
  have hse1 : ∑ v : Fin 2, Real.exp (z1 v) = 2 := by
    simp only [Fin.sum_univ_two, hz1]
    norm_num
  have hse2 : ∑ v : Fin 2, Real.exp (z2 v) = 2 * Real.cosh a := by
    rw [Fin.sum_univ_two]
    simp only [hz20, hz21]
    exact hea
  have hsem : ∑ v : Fin 2, Real.exp (((z1 + z2) / 2) v)
      = 2 * Real.cosh (a / 2) := by
    rw [Fin.sum_univ_two]
    have e0 : ((z1 + z2) / 2 : Fin 2 → ℝ) 0 = a / 2 := by
      simp [Pi.add_apply, Pi.div_apply, hz1, hz20]
    have e1 : ((z1 + z2) / 2 : Fin 2 → ℝ) 1 = -(a / 2) := by
      simp [Pi.add_apply, Pi.div_apply, hz1, hz21]
      ring
    simp only [e0, e1]
    exact heh
  have hl1 : Hagi.lse z1 = Real.log 2 := by
    simp only [Hagi.lse, hse1]
  have hl2 : Hagi.lse z2 = Real.log (2 * Real.cosh a) := by
    simp only [Hagi.lse, hse2]
  have hlm : Hagi.lse ((z1 + z2) / 2)
      = Real.log (2 * Real.cosh (a / 2)) := by
    simp only [Hagi.lse, hsem]
  have hnc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  have hnc2 : Real.cosh (a / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (a / 2))
  have hl2a : Real.log (2 * Real.cosh a)
      = Real.log 2 + Real.log (Real.cosh a) :=
    Real.log_mul two_ne_zero hnc
  have hlma : Real.log (2 * Real.cosh (a / 2))
      = Real.log 2 + Real.log (Real.cosh (a / 2)) :=
    Real.log_mul two_ne_zero hnc2
  have hc1 : 1 < Real.cosh a := (Real.one_lt_cosh (x := a)).mpr ha
  have hsq : Real.cosh (a / 2) ^ 2 = (Real.cosh a + 1) / 2 := by
    have h := cosh_half_sq (a / 2)
    rw [show 2 * (a / 2) = a from by ring] at h
    exact h
  have hlt : Real.cosh (a / 2) ^ 2 < Real.cosh a := by
    rw [hsq]
    linarith
  have hloglt : Real.log (Real.cosh (a / 2) ^ 2)
      < Real.log (Real.cosh a) :=
    Real.log_lt_log (by positivity) hlt
  have hlogpow : Real.log (Real.cosh (a / 2) ^ 2)
      = 2 * Real.log (Real.cosh (a / 2)) := by
    rw [Real.log_pow]
    norm_num
  rw [hlogpow] at hloglt
  unfold jensenGap
  rw [hl1, hl2, hlm, hl2a, hlma]
  linarith

end Hagi.Unified

namespace Hagi
export Hagi.Unified (jensenGap_pos_witness)
end Hagi

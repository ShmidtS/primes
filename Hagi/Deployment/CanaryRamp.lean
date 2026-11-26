/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Architecture.CascadeLeak
import Hagi.Cert.StepGen

/-!
# Canary-weight ramp certificate

The canary-acceptance contract: the route weight `w` is made
continuous and rolled out canary-style from 0 to 1 while the
e-process watches for harm — the leak is LINEAR in `w`
(`cascade_leak_router_linear`), so the per-step exposure is
`wₜ · L_stack · ‖ΔR‖ · ‖projR U *ᵥ x‖` (the form
`cascade_leak_bound_op` with `L_stack = cascadeGain S`).

Pieces:

* `CanaryRamp` — a GENERIC ramp policy premise: any nondecreasing
  weight sequence in `[0, 1]` (`mono`, `nonneg`, `le_one` fields).
* `linearRamp` — the standard ramp `wₜ = t / T`, with
  `linearRamp_canary` certifying it against the generic premise.
* `canaryStepLeak` — the constant form `w * L * dR * px`:
  linear in `w` by construction, matching
  `cascade_leak_router_linear` (exact linearity) and
  `cascade_leak_bound_op` (the bound).
* `canary_step_leak_bound` — the per-step leak bound: the cascade
  output perturbation at weight `w` is at most
  `canaryStepLeak (cascadeGain S) ‖ΔR‖ ‖projR U *ᵥ x‖ w`.
* `canary_ramp_harm_bound` — the cumulative harm exposure of the
  ramp: `∑ leak(w j) = (∑ w j) · L · dR · px`.
* `canary_ramp_linear_sum` + `canary_linear_ramp_harm` — for the
  standard linear ramp `wₜ = t / T` over `t ∈ [0, T]` the exposure is
  exactly `((T+1)/2) · L · dR · px` — finite and controlled.
* `canary_step_certified` — the ramp step AS a
  `Hagi.Cert.CertStepGen` (the kernel, `rd_step_certified`
  pattern): the leak rides the RISK channel with a FREE remainder.
* `canaryVilleMonitorHold` — the monitor contract (PREMISE-form):
  whenever the e-process crosses the Ville threshold the ramp step
  is a certified HOLD. Cites `gate_anytime_valid` (the Ville
  time-uniform gate) and `stitching_eprocess_anytime` (the
  stitched master e-process) — cited, not imported (Unified layer 6
  sits above Deployment 5).
* `canary_ramp_completion_bound` — an all-progress ramp with
  per-step risk spend `leak(w j)` keeps the total exposure inside
  the initial risk level (the telescope law `risk_telescope_gen`,
  windowed to a finite ramp).
* `canary_ramp_acceptance` — the canary contract: either some step
  crossed the Ville threshold (the ramp halts at a certified hold)
  or the full ramp completes with total harm `∑ leak(w j) ≤
  M.risk (t 0)`.
* `canary_ramp_anchor_3step` — numeric anchor: the 3-step ramp
  `w = 0, 1/2, 1` at `L = dR = px = 1` has total exposure `3/2`,
  exactly the `(T+1)/2` law at `T = 2`.

Honest scope: the e-process FIRING logic is premise-form (the /
 Ville statements are cited; no probability is imported), and the
ramp policy SHAPE is a premise — any nondecreasing `[0, 1]` sequence
works, the theorems are generic in the ramp.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Deployment

open Finset
open scoped Matrix Matrix.Norms.Operator

/-! ## The ramp policy (generic premise) -/

/-- A canary ramp policy: a weight sequence that is nondecreasing
(`mono`), starts inside `[0, 1]` from below (`nonneg`) and never
exceeds full rollout (`le_one`). The theorem layer is GENERIC in this
premise — the standard instance is `linearRamp`
(`linearRamp_canary`). -/
structure CanaryRamp where
  /-- The rollout weights, one per ramp step. -/
  w : ℕ → ℝ
  mono : ∀ j, w j ≤ w (j + 1)
  nonneg : ∀ j, 0 ≤ w j
  le_one : ∀ j, w j ≤ 1

/-- The standard linear ramp `wₜ = t / T` over `t ∈ [0, T]`. -/
noncomputable def linearRamp (T j : ℕ) : ℝ := (j : ℝ) / T

/-- Cast-sum identity for the linear ramp: `∑_{j<T+1} (j:ℝ) =
(T+1)·T/2` (by induction; `Finset.sum_range_id` is ℕ-only in this
Mathlib revision). -/
theorem canary_sum_cast_range (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), (j : ℝ) = (T + 1) * T / 2 := by
  induction T with
  | zero => norm_num
  | succ T ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The linear ramp is nondecreasing. -/
theorem linearRamp_mono (T : ℕ) (hT : 0 < T) (j : ℕ) :
    linearRamp T j ≤ linearRamp T (j + 1) := by
  have h : ((j : ℝ) + 1) / (T : ℝ) = (j : ℝ) / (T : ℝ) + ((1 : ℝ) / (T : ℝ)) := by
    ring
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  unfold linearRamp
  rw [Nat.cast_add_one, h]
  exact le_add_of_nonneg_right (by positivity)

/-- The linear ramp stays in `[0, 1]` on the ramp window `j ≤ T`. -/
theorem linearRamp_bounded (T : ℕ) (hT : 0 < T) (j : ℕ) :
    0 ≤ linearRamp T j ∧ (j ≤ T → linearRamp T j ≤ 1) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  constructor
  · unfold linearRamp
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hTpos)
  · intro hj
    unfold linearRamp
    have hcast : ((j : ℕ) : ℝ) ≤ ((T : ℕ) : ℝ) := by exact_mod_cast hj
    exact (div_le_one hTpos).mpr hcast

/-- The standard linear ramp satisfies the generic ramp premise on
the window `j ≤ T` (the carrier weight is the `[0,1]`-clamp of
`linearRamp T j`, which coincides with it on the window). -/
theorem linearRamp_canary (T : ℕ) (hT : 0 < T) :
    ∃ r : CanaryRamp, ∀ j ≤ T, r.w j = linearRamp T j := by
  refine ⟨{ w := fun j => min (linearRamp T j) 1
            mono := fun j => min_le_min (linearRamp_mono T hT j) (le_refl 1)
            nonneg := fun j => le_min ((linearRamp_bounded T hT j).1) zero_le_one
            le_one := fun _ => min_le_right _ _ },
    fun j hj => ?_⟩
  exact min_eq_left ((linearRamp_bounded T hT j).2 hj)

/-! ## The per-step leak (constant form) -/

/-- The leak constant form: the canary step's harm exposure is
`w · L_stack · ‖ΔR‖ · ‖projR U *ᵥ x‖` — LINEAR in the weight `w`,
matching `cascade_leak_router_linear` (exact linearity of the leak
in the router weight). -/
def canaryStepLeak (L dR px w : ℝ) : ℝ := w * L * dR * px

/-- The per-step leak bound: at a nonnegative weight `w` the cascade
output perturbation of the adapter step is at most
`canaryStepLeak (cascadeGain S) ‖ΔR‖ ‖projR U *ᵥ x‖ w`
`cascade_leak_bound_op` instantiated at `|w| = w`. -/
theorem canary_step_leak_bound {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (w : ℝ) (hw : 0 ≤ w) (ΔR : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ‖Hagi.Core.propagate S (x + w • (ΔR *ᵥ (Hagi.Architecture.projR U *ᵥ x)))
        - Hagi.Core.propagate S x‖
      ≤ canaryStepLeak (Hagi.Core.cascadeGain S) ‖ΔR‖
          ‖Hagi.Architecture.projR U *ᵥ x‖ w := by
  have h := Hagi.Architecture.cascade_leak_bound_op U S w ΔR x
  rwa [abs_of_nonneg hw] at h

/-! ## The cumulative harm bound -/

/-- The cumulative harm exposure of the ramp: the sum of per-step
leaks factors as the weight sum times the constant triple —
`∑ w j · L · dR · px = (∑ w j) · L · dR · px`. -/
theorem canary_ramp_harm_bound (T : ℕ) (r : CanaryRamp) (L dR px : ℝ) :
    ∑ j ∈ Finset.range T, canaryStepLeak L dR px (r.w j)
      = (∑ j ∈ Finset.range T, r.w j) * L * dR * px := by
  calc ∑ j ∈ Finset.range T, canaryStepLeak L dR px (r.w j)
      = ∑ j ∈ Finset.range T, (r.w j * (L * dR * px)) := by
        simp only [canaryStepLeak, mul_assoc]
    _ = (∑ j ∈ Finset.range T, r.w j) * (L * dR * px) :=
        (Finset.sum_mul _ _ _).symm
    _ = (∑ j ∈ Finset.range T, r.w j) * L * dR * px := by ring

/-- The linear ramp's weight sum: over the window `t ∈ [0, T]` the
standard ramp sums to exactly `(T + 1) / 2`. -/
theorem canary_ramp_linear_sum (T : ℕ) (hT : 0 < T) :
    ∑ j ∈ Finset.range (T + 1), linearRamp T j = (T + 1) / 2 := by
  have h1 : ∀ j : ℕ, (j : ℝ) / (T : ℝ) = (j : ℝ) * (1 / (T : ℝ)) := by
    intro j; field_simp
  have h2 : ∑ j ∈ Finset.range (T + 1), (j : ℝ) * (1 / (T : ℝ))
      = (∑ j ∈ Finset.range (T + 1), (j : ℝ)) * (1 / (T : ℝ)) :=
    (Finset.sum_mul _ _ _).symm
  unfold linearRamp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), h2, canary_sum_cast_range]
  field_simp

/-- The total exposure bound of the whole standard linear ramp:
`∑_{t≤T} leak(wₜ) = ((T+1)/2) · L · dR · px` — finite and controlled
(half the window length times the constant triple). -/
theorem canary_linear_ramp_harm (T : ℕ) (hT : 0 < T) (L dR px : ℝ) :
    ∑ j ∈ Finset.range (T + 1), canaryStepLeak L dR px (linearRamp T j)
      = ((T + 1) / 2) * L * dR * px := by
  obtain ⟨r, hrw⟩ := linearRamp_canary T hT
  have hjT : ∀ j ∈ Finset.range (T + 1), j ≤ T := by
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  have he : ∑ j ∈ Finset.range (T + 1), canaryStepLeak L dR px (r.w j)
      = ∑ j ∈ Finset.range (T + 1), canaryStepLeak L dR px (linearRamp T j) :=
    Finset.sum_congr rfl (fun j hj => by rw [hrw j (hjT j hj)])
  have hw : ∑ j ∈ Finset.range (T + 1), r.w j
      = ∑ j ∈ Finset.range (T + 1), linearRamp T j :=
    Finset.sum_congr rfl (fun j hj => by rw [hrw j (hjT j hj)])
  rw [← he, canary_ramp_harm_bound (T + 1) r L dR px, hw,
    canary_ramp_linear_sum T hT]

/-! ## The certified transition packaging (kernel) -/

/-- **The ramp step IS a certified transition**: the canary step at
weight `w` packaged as a `Hagi.Cert.CertStepGen` (
`rd_step_certified` pattern): the leak `canaryStepLeak L dR px w`
rides the RISK channel (the harm budget) with a FREE remainder (the
 no-zero-pinning lesson), the false-commit delta channel and the
budget/descent/floors laws are premises — the certificate is about
the ACCOUNTING, not about an executed rollout. -/
noncomputable def canary_step_certified {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (L dR px w : ℝ) (s s' : S)
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (budgetSpend : ℝ)
    (hbud : M.budget s' = M.budget s - budgetSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = canaryStepLeak L dR px w + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl deltaLevel s s' where
  drop := drop
  drop_pos := hdrop
  descent := hdesc
  budgetSpend := budgetSpend
  budget_next := hbud
  budget_nonneg := hbudnn
  riskSpend := canaryStepLeak L dR px w
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := delta
  delta_next := hdelta
  delta_nonneg := hdeltaNN
  floorsKept := hfloors

/-- The risk-channel spend of the certified ramp step is
leak form at the step's weight. -/
theorem canary_step_certified_riskSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (L dR px w : ℝ) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (budgetSpend : ℝ)
    (hbud : M.budget s' = M.budget s - budgetSpend)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = canaryStepLeak L dR px w + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (canary_step_certified M obl deltaLevel L dR px w s s'
      drop hdrop hdesc budgetSpend hbud hbudnn riskRem hrisk hrisk' hrem
      delta hdelta hdeltaNN hfloors).riskSpend
      = canaryStepLeak L dR px w := rfl

/-! ## The monitor contract and the acceptance theorem -/

/-- The Ville monitor contract (PREMISE-form): the e-process
`eProc : ℕ → ℝ` with threshold `thresh` guards the ramp trajectory
`t`; whenever the process CROSSES the threshold at step `j`, that
step is a certified HOLD (`TransitionStep.hold`). Cited backing (NOT
imported — Unified layer 6 sits above Deployment 5)
`gate_anytime_valid` (the Ville time-uniform gate)
`stitching_eprocess_anytime` (the stitched master e-process). -/
def canaryVilleMonitorHold {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (t : ℕ → S)
    (eProc : ℕ → ℝ) (thresh : ℝ)
    (steps : ∀ j, Hagi.Cert.TransitionStep M obl (t j) (t (j + 1))) : Prop :=
  ∀ j, thresh ≤ eProc j →
    ∃ h : Hagi.Cert.HoldStep M obl (t j) (t (j + 1)),
      steps j = Hagi.Cert.TransitionStep.hold h

/-- The all-progress completion bound: a ramp whose steps `j < T` are
certified transitions spending exactly the leak at their weights
keeps the TOTAL harm exposure inside the initial risk level — the
 telescope law (`risk_telescope_gen`), windowed to the ramp
length (the kernel law is ℕ-indexed over all steps; the windowed
form carries the same induction, restated here for a finite ramp). -/
theorem canary_ramp_completion_bound {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (T : ℕ) (t : ℕ → S) (r : CanaryRamp) (L dR px : ℝ)
    (h0 : 0 ≤ M.risk (t 0))
    (steps : ∀ j, j < T →
      Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hspend : ∀ j (hj : j < T),
      (steps j hj).riskSpend = canaryStepLeak L dR px (r.w j)) :
    ∑ j ∈ Finset.range T, canaryStepLeak L dR px (r.w j) ≤ M.risk (t 0) := by
  have key : ∀ m : ℕ, m ≤ T →
      ∑ j ∈ Finset.range m, canaryStepLeak L dR px (r.w j)
        ≤ M.risk (t 0) - M.risk (t m) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hmT : m < T := Nat.lt_of_succ_le hm
      have hm' : m ≤ T := Nat.le_of_lt hmT
      have e1 := (steps m hmT).risk_split
      have e2 := (steps m hmT).risk_next
      have hsp := hspend m hmT
      have htail := ih hm'
      have hrnn : 0 ≤ M.risk (t (m + 1)) := by
        rw [e2]; exact (steps m hmT).risk_nonneg
      rw [Finset.sum_range_succ, ← hsp]
      linarith
  have hrnn : 0 ≤ M.risk (t T) := by
    match T with
    | 0 => exact h0
    | m + 1 =>
      have e2 := (steps m (Nat.lt_succ_self m)).risk_next
      rw [e2]
      exact (steps m (Nat.lt_succ_self m)).risk_nonneg
  have hkey := key T (le_refl T)
  linarith

/-- **The canary acceptance contract**: under the Ville monitor
contract (`mon`) with a witness supply that every ALARM-FREE step is
certified progress spending exactly its leak, the ramp EITHER
halts — some step `j < T` crossed the Ville threshold, and by `mon`
that step is a certified hold — OR completes with the total harm
exposure `∑ leak(w j)` inside the initial risk level. Classical
case split on a crossing inside the window; the progress branch is
the windowed telescope (`canary_ramp_completion_bound`). -/
theorem canary_ramp_acceptance {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (T : ℕ) (t : ℕ → S) (r : CanaryRamp) (L dR px : ℝ)
    (eProc : ℕ → ℝ) (thresh : ℝ)
    (steps : ∀ j, Hagi.Cert.TransitionStep M obl (t j) (t (j + 1)))
    (hmon : canaryVilleMonitorHold M obl t eProc thresh steps)
    (h0 : 0 ≤ M.risk (t 0))
    (hprog : ∀ j, j < T → ¬ (thresh ≤ eProc j) →
      ∃ c : Hagi.Cert.CertStep M obl (t j) (t (j + 1)),
        steps j = Hagi.Cert.TransitionStep.progress c
          ∧ c.riskSpend = canaryStepLeak L dR px (r.w j)) :
    (∃ j ∈ Finset.range T, thresh ≤ eProc j ∧
      ∃ h : Hagi.Cert.HoldStep M obl (t j) (t (j + 1)),
        steps j = Hagi.Cert.TransitionStep.hold h) ∨
    (∑ j ∈ Finset.range T, canaryStepLeak L dR px (r.w j) ≤ M.risk (t 0)) := by
  by_cases hcross : ∃ j ∈ Finset.range T, thresh ≤ eProc j
  · obtain ⟨j, hjmem, hjc⟩ := hcross
    exact Or.inl ⟨j, hjmem, hjc, hmon j hjc⟩
  · right
    -- the embedding `certStep_to_gen` has no delta channel, so the
    -- acceptance trajectory runs at the zero delta level
    have noalarm : ∀ j (hj : j < T), ¬ (thresh ≤ eProc j) := by
      intro j hj hcontr
      exact absurd ⟨j, Finset.mem_range.mpr hj, hcontr⟩ hcross
    refine canary_ramp_completion_bound M obl (fun _ => 0) T t r L dR px h0
      (fun j hj =>
        Hagi.Cert.certStep_to_gen M obl
          (Classical.choose (hprog j hj (noalarm j hj)))) ?_
    intro j hj
    exact (Classical.choose_spec (hprog j hj (noalarm j hj))).2

/-! ## Numeric anchor (3-step ramp) -/

/-- The 3-step numeric anchor: at `T = 2` the standard ramp
`w = 0, 1/2, 1` with unit leak constants `L = dR = px = 1` has total
exposure `0 + 1/2 + 1 = 3/2` — exactly the `(T+1)/2` law of
`canary_ramp_linear_sum` at `T = 2`. -/
theorem canary_ramp_anchor_3step :
    ∑ j ∈ Finset.range 3, canaryStepLeak 1 1 1 (linearRamp 2 j) = 3 / 2 := by
  have h := canary_linear_ramp_harm 2 (by norm_num : 0 < 2) 1 1 1
  norm_num at h
  exact h

end Hagi.Deployment

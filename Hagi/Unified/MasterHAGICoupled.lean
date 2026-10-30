/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGI
import Hagi.Unified.Assumptions
import Hagi.Model.StageSemantics
import Hagi.Model.CertifiedTransition

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

namespace Hagi.Unified

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


/-- **`CoupledHAGIInvariant` is inhabited** (R337, audit v3
Phase 6): the idle state trajectory (all fields zero, budget
1) with zero risk/spend ledgers, zero qvec floor and `alpha =
0` satisfies every conjunct at any horizon `T`. -/
theorem coupledHAGI_nonvacuous {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (x0 : X) (T : ℕ) :
    CoupledHAGIInvariant T
      (fun _ => Hagi.Unified.idleGrowth x0 0)
      (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) 0 where
  cap_is_state := by
    intro t _
    rfl
  risk_bound := by
    simp [Hagi.Unified.idleGrowth]
  spend_nonneg := fun _ _ => le_refl 0
  risk_nonneg := fun _ _ => le_refl 0
  budget_account := by
    constructor <;> simp [Hagi.Unified.idleGrowth]
  capability_growth := by
    simp [Hagi.Unified.idleGrowth]
  qvec_floor := fun _ => le_refl 0

/-- The growing-state trajectory for the non-idle witness:
capability `c₀(1+α)^t` (real compound growth, α > 0), budget
`B − t·s` with a strictly positive per-step spend `s`, risk
pinned at zero. -/
noncomputable def coupledGrowthTraj {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x0 : X) (alpha c0 s B : ℝ) : ℕ → GrowthState X :=
  fun t =>
    { Hagi.Unified.idleGrowth x0 0 with
      capability := c0 * (1 + alpha) ^ t
      budget := B - t * s }

/-- **The coupled capstone is inhabited NON-IDLE** (R358):
with `α > 0`, `c₀ > 0`, spend `s > 0` and budget
`B = T·s + 1` (enough for T steps), the growing trajectory
satisfies every conjunct of `CoupledHAGIInvariant` —
compound capability growth `(1+α)^T`, strictly positive
spends, a budget that genuinely decreases but stays
nonnegative at the horizon. -/
theorem coupledHAGI_nonvacuous_strict {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x0 : X) (T : ℕ) (alpha c0 s : ℝ)
    (halpha : 0 < alpha) (hc0 : 0 < c0) (hs : 0 < s) :
    CoupledHAGIInvariant T
      (coupledGrowthTraj x0 alpha c0 s (T * s + 1))
      (fun _ => 0) (fun _ => s) (fun _ _ => 0) (fun _ => 0)
      alpha where
  cap_is_state := by
    intro t _
    rfl
  risk_bound := by
    simp [coupledGrowthTraj, Hagi.Unified.idleGrowth]
  spend_nonneg := fun _ _ => hs.le
  risk_nonneg := fun _ _ => le_refl 0
  budget_account := by
    constructor
    · simp [coupledGrowthTraj, Hagi.Unified.idleGrowth]
    · simp only [coupledGrowthTraj]
      have : (T:ℝ) * s < T * s + 1 := by nlinarith
      have hcast : ((T:ℝ)) = ((T:ℝ)) := rfl
      show (0:ℝ) ≤ (T * s + 1) - ((T:ℕ):ℝ) * s
      push_cast
      linarith
  capability_growth := by
    simp only [coupledGrowthTraj]
    rw [pow_zero, mul_one]
  qvec_floor := fun _ => le_refl 0

/-- АУДИТ v4 §3.2: СВЯЗАННЫЙ инвариант — CoupledHAGIInvariant
ПЛЮС требование, что состояния получены реальными
advance-переходами (закрытие разрыва «условия могут
выполняться у произвольной последовательности состояний»). -/
structure LinkedHAGIInvariant (T : ℕ)
    (S : ℕ → GrowthState X)
    (u : ℕ → Hagi.Model.StageInput X)
    (risk spend : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ)
    (alpha : ℝ) extends CoupledHAGIInvariant T S risk spend qvec qfloor alpha where
  /-- Каждое состояние получено исполнением перехода. -/
  linked : ∀ t < T, S (t + 1) = Hagi.Model.advance (S t) (u t)

/-- Связанный инвариант влечёт несвязанный (мост). -/
theorem LinkedHAGIInvariant_to_coupled {T : ℕ}
    {S : ℕ → GrowthState X} {u : ℕ → Hagi.Model.StageInput X}
    {risk spend : ℕ → ℝ} {qvec : ℕ → Fin 5 → ℝ}
    {qfloor : Fin 5 → ℝ} {alpha : ℝ}
    (h : LinkedHAGIInvariant T S u risk spend qvec qfloor alpha) :
    CoupledHAGIInvariant T S risk spend qvec qfloor alpha :=
  h.toCoupledHAGIInvariant

/-- CAPSTONE-МОСТ: семейство CertifiedTransition (зависимые
сертификаты exec-переходов) ПОРОЖДАЕТ LinkedHAGIInvariant —
телескопы бюджета/риска/роста становятся полями связанного
инварианта; несвязанные последовательности исключены. -/
theorem certified_family_linked {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → GrowthState X) (u : ℕ → Hagi.Model.StageInput X)
    (T : ℕ) (alpha : ℝ) (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ)
    (hc : ∀ t < T, Hagi.Model.CertifiedTransition (S t) (S (t + 1))
      (u t) ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk))
    (hrisk_nonneg : ∀ t ∈ Finset.range T, 0 ≤ (u t).eff.growRisk
      + (u t).eff.mergeRisk + (u t).eff.jointRisk
      + (u t).eff.compressRisk)
    (hspend_nonneg : ∀ t ∈ Finset.range T, 0 ≤ (u t).eff.growCost
      + (u t).eff.mergeCost + (u t).eff.jointCost
      + (u t).eff.compressCost)
    (hbudget : 0 ≤ (S T).budget)
    (hgrowth : (S 0).capability * (1 + alpha) ^ T
      ≤ (S 0).capability + ∑ t ∈ Finset.range T, (u t).eff.growGain)
    (hqvec : ∀ i, qfloor i ≤ qvec T i) :
    LinkedHAGIInvariant T S u
      (fun t => (u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk)
      (fun t => (u t).eff.growCost + (u t).eff.mergeCost
        + (u t).eff.jointCost + (u t).eff.compressCost)
      qvec qfloor alpha where
  toCoupledHAGIInvariant :=
    { cap_is_state := fun t _ => rfl
      risk_bound := by
        have h := Hagi.Model.certified_trajectory_risk S u T hc
        rw [h]
        linarith
      spend_nonneg := hspend_nonneg
      risk_nonneg := hrisk_nonneg
      budget_account := by
        refine ⟨?_, hbudget⟩
        exact Hagi.Model.certified_trajectory_budget S u T hc
      capability_growth := by
        have h := Hagi.Model.certified_trajectory_capability S u T hc
        rw [h]
        exact hgrowth
      qvec_floor := hqvec }
  linked := fun t _ => (hc t (by omega)).exec

/-- АУДИТ v11 §3.2: УСИЛЕННЫЙ связанный инвариант — Linked
PLUS per-step PROGRESS-сертификаты (0 < verify-снижение на
КАЖДОМ переходе) и перенос их в финальный результат:
кумулятивное сертифицированное снижение не меньше суммы
шаговых decrease (энергетический телескоп ПО ИЗМЕРЕННЫМ
progress-полям). Закрывает разрыв «progress-поле
CertifiedTransition не потребляется итоговым инвариантом». -/
structure LinkedHAGIInvariantProgress (T : ℕ)
    (S : ℕ → GrowthState X)
    (u : ℕ → Hagi.Model.StageInput X)
    (risk spend : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ)
    (alpha : ℝ)
    extends LinkedHAGIInvariant T S u risk spend qvec qfloor alpha where
  /-- На каждом переходе — строго положительное снижение. -/
  progress_pos : ∀ t < T,
    0 < (Hagi.System.verify (S (t + 1))).decrease
  /-- Кумулятивное снижение (энергетический перенос
  progress-полей в финальный сертификат). -/
  cumulative_progress :
    ∑ t ∈ Finset.range T, (Hagi.System.verify (S (t + 1))).decrease
      ≤ (S 0).energy - (S T).energy

/-- Мост-усиление: certified-семейство ПОРОЖДАЕТ усиленный
инвариант — progress-поля потребляются явно. -/
theorem certified_family_linked_progress {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → GrowthState X) (u : ℕ → Hagi.Model.StageInput X)
    (T : ℕ) (alpha : ℝ) (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ)
    (hc : ∀ t < T, Hagi.Model.CertifiedTransition (S t) (S (t + 1))
      (u t) ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk))
    (hrisk_nonneg : ∀ t ∈ Finset.range T, 0 ≤ (u t).eff.growRisk
      + (u t).eff.mergeRisk + (u t).eff.jointRisk
      + (u t).eff.compressRisk)
    (hspend_nonneg : ∀ t ∈ Finset.range T, 0 ≤ (u t).eff.growCost
      + (u t).eff.mergeCost + (u t).eff.jointCost
      + (u t).eff.compressCost)
    (hbudget : 0 ≤ (S T).budget)
    (hgrowth : (S 0).capability * (1 + alpha) ^ T
      ≤ (S 0).capability + ∑ t ∈ Finset.range T, (u t).eff.growGain)
    (hqvec : ∀ i, qfloor i ≤ qvec T i)
    (hetelescope : ∑ t ∈ Finset.range T,
        (Hagi.System.verify (S (t + 1))).decrease
      ≤ (S 0).energy - (S T).energy) :
    LinkedHAGIInvariantProgress T S u
      (fun t => (u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk)
      (fun t => (u t).eff.growCost + (u t).eff.mergeCost
        + (u t).eff.jointCost + (u t).eff.compressCost)
      qvec qfloor alpha where
  toLinkedHAGIInvariant :=
    certified_family_linked S u T alpha qvec qfloor hc
      hrisk_nonneg hspend_nonneg hbudget hgrowth hqvec
  progress_pos := fun t ht => (hc t ht).progress
  cumulative_progress := hetelescope

end Hagi.Unified


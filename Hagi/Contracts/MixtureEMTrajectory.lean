/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.ChangingEMTrajectory

/-! # Retained categorical mixtures with changing-family EM

Construct a mixture of two categorical prior/channel models on one fixed latent
carrier and an arbitrary observation type. Positive old evidence and a strict
interior weight give positive evidence and posterior support inclusion. Zero
weight preserves the complete old model, including fallback rows. A finite
interior grid and a validity-carrying state replay exactly into the retained
changing-family EM trajectory, yielding nonincreasing aggregate observation NLL.

The labels are not latent dimensions or computation counts. No selected-model
convergence, latent-cardinality growth, parameter optimum, per-unit improvement,
physical resource bound or efficient optimizer is asserted.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open Hagi.Probability.FiniteMultiEM
open Hagi.Contracts.ChangingEMTrajectory
open scoped BigOperators ENNReal

namespace Hagi.Contracts.MixtureEMTrajectory

-- BEGIN C151 ISOLATED CORE

private noncomputable def mixturePriorMass {X : Type} (ε : NNReal)
    (p r : PMF X) (x : X) : ENNReal :=
  ((1 - ε : NNReal) : ENNReal) * p x + (ε : ENNReal) * r x

private noncomputable def mixtureJointMass {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) (y : Y) : ENNReal :=
  ((1 - ε : NNReal) : ENNReal) * p x * K x y + (ε : ENNReal) * r x * L x y

private theorem mixturePriorMass_sum {X : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p r : PMF X) :
    ∑ x, mixturePriorMass ε p r x = 1 := by
  have hp : ∑ x, p x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe p
  have hr : ∑ x, r x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe r
  simp only [mixturePriorMass, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hr,
    mul_one]
  exact_mod_cast tsub_add_cancel_of_le hε

private theorem mixturePriorMass_ne_top {X : Type} (ε : NNReal)
    (p r : PMF X) (x : X) : mixturePriorMass ε p r x ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (p.apply_ne_top x)
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (r.apply_ne_top x)

private theorem mixtureJointMass_hasSum {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) :
    HasSum (mixtureJointMass ε p r K L x) (mixturePriorMass ε p r x) := by
  have hsum : (∑' y, mixtureJointMass ε p r K L x y) = mixturePriorMass ε p r x := by
    simp only [mixtureJointMass, mixturePriorMass]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      PMF.tsum_coe, PMF.tsum_coe, mul_one, mul_one]
  exact hsum ▸ ENNReal.summable.hasSum

private noncomputable def mixtureChannel {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) : PMF Y :=
  dite (mixturePriorMass ε p r x = 0) (fun _ => K x) (fun hx =>
    ⟨fun y => mixtureJointMass ε p r K L x y / mixturePriorMass ε p r x, by
      have hsum : (∑' y, mixtureJointMass ε p r K L x y /
          mixturePriorMass ε p r x) = 1 := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, (mixtureJointMass_hasSum ε p r K L x).tsum_eq,
          ← div_eq_mul_inv, ENNReal.div_self hx (mixturePriorMass_ne_top ε p r x)]
      exact hsum ▸ ENNReal.summable.hasSum⟩)

private theorem mixtureChannel_of_zero {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X)
    (hx : mixturePriorMass ε p r x = 0) : mixtureChannel ε p r K L x = K x := by
  classical
  simp [mixtureChannel, hx]

private theorem mixtureChannel_apply_of_nonzero {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X)
    (hx : mixturePriorMass ε p r x ≠ 0) (obs : Y) :
    mixtureChannel ε p r K L x obs =
      mixtureJointMass ε p r K L x obs / mixturePriorMass ε p r x := by
  classical
  simp [mixtureChannel, hx]
  rfl

/-- Normalized same-carrier interpolation, with the original channel as the
kernel-only zero-prior fallback. No observation finiteness is required. -/
noncomputable def mixtureModel {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y) (r : PMF X) (L : X → PMF Y) :
    PMF X × (X → PMF Y) :=
  (PMF.ofFintype (mixturePriorMass ε p r) (mixturePriorMass_sum ε hε p r),
    mixtureChannel ε p r K L)

private theorem mixtureModel_mul_channel {X Y : Type} [Fintype X]
    (ε : NNReal) (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (x : X) (obs : Y) :
    (mixtureModel ε hε p K r L).1 x * (mixtureModel ε hε p K r L).2 x obs =
      mixtureJointMass ε p r K L x obs := by
  classical
  change mixturePriorMass ε p r x * mixtureChannel ε p r K L x obs = _
  by_cases hx : mixturePriorMass ε p r x = 0
  · rw [mixtureChannel_of_zero ε p r K L x hx, hx, zero_mul]
    have hzero := hx
    rw [mixturePriorMass] at hzero
    have hold := (add_eq_zero.mp hzero).1
    have haux := (add_eq_zero.mp hzero).2
    have hfirst : ((1 - ε : NNReal) : ENNReal) * p x * K x obs = 0 := by
      rw [hold, zero_mul]
    have hsecond : (ε : ENNReal) * r x * L x obs = 0 := by
      rw [haux, zero_mul]
    rw [mixtureJointMass, hfirst, hsecond, add_zero]
  · rw [mixtureChannel_apply_of_nonzero ε p r K L x hx]
    exact ENNReal.mul_div_cancel hx (mixturePriorMass_ne_top ε p r x)

/-- Observation evidence is exactly the affine interpolation of the two old
observation evidences. -/
theorem mixtureModel_evidence {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y) :
    observationEvidence (mixtureModel ε hε p K r L).1
        (mixtureModel ε hε p K r L).2 obs =
      ((1 - ε : NNReal) : ENNReal) * observationEvidence p K obs +
        (ε : ENNReal) * observationEvidence r L obs := by
  rw [observationEvidence_eq_sum, observationEvidence_eq_sum,
    observationEvidence_eq_sum]
  calc
    _ = ∑ x, (((1 - ε : NNReal) : ENNReal) * (p x * K x obs) +
        (ε : ENNReal) * (r x * L x obs)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [mixtureModel_mul_channel]
      simp only [mixtureJointMass, mul_assoc]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Retained positive evidence remains positive at every strict interior
weight, even when the auxiliary observation evidence vanishes. -/
theorem mixtureModel_evidence_pos {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε < 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y)
    (hold : 0 < observationEvidence p K obs) :
    0 < observationEvidence (mixtureModel ε hε.le p K r L).1
      (mixtureModel ε hε.le p K r L).2 obs := by
  rw [mixtureModel_evidence]
  have hc : 0 < (((1 - ε : NNReal) : ENNReal)) := by
    exact_mod_cast (tsub_pos_of_lt hε)
  exact add_pos_of_pos_of_nonneg (ENNReal.mul_pos hc.ne' hold.ne') zero_le

/-- Every actual old-posterior support point is retained in the normalized
mixture posterior under strict retained mass. -/
theorem mixtureModel_posterior_support {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε < 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y)
    (hold : 0 < observationEvidence p K obs) :
    (posterior p K obs hold).support ⊆
      (posterior (mixtureModel ε hε.le p K r L).1
        (mixtureModel ε hε.le p K r L).2 obs
        (mixtureModel_evidence_pos ε hε p K r L obs hold)).support := by
  intro x hx
  rw [PMF.mem_support_iff, posterior_apply] at hx ⊢
  rw [mixtureModel_mul_channel]
  have hnum : p x * K x obs ≠ 0 := by
    intro hz
    exact hx (by rw [hz, ENNReal.zero_div])
  have hp : p x ≠ 0 := fun hp => hnum (by simp [hp])
  have hK : K x obs ≠ 0 := fun hK => hnum (by simp [hK])
  have hc : 0 < (((1 - ε : NNReal) : ENNReal)) := by
    exact_mod_cast (tsub_pos_of_lt hε)
  have hfirst : 0 < ((1 - ε : NNReal) : ENNReal) * p x * K x obs :=
    ENNReal.mul_pos (ENNReal.mul_pos hc.ne' hp).ne' hK
  have hjoint : mixtureJointMass ε p r K L x obs ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hfirst zero_le)
  exact (ENNReal.div_pos hjoint
    (((mixtureModel ε hε.le p K r L).1.bind
      (mixtureModel ε hε.le p K r L).2).apply_ne_top obs)).ne'

/-- Zero mixture weight preserves the entire prior/channel pair, including
old-prior-zero and unobserved channel rows. -/
theorem mixtureModel_zero {X Y : Type} [Fintype X]
    (p : PMF X) (K : X → PMF Y) (r : PMF X) (L : X → PMF Y) :
    mixtureModel 0 (by simp) p K r L = (p, K) := by
  apply Prod.ext
  · apply PMF.ext
    intro x
    simp [mixtureModel, mixturePriorMass]
  · funext x
    change mixtureChannel 0 p r K L x = K x
    by_cases hD : mixturePriorMass 0 p r x = 0
    · exact mixtureChannel_of_zero 0 p r K L x hD
    · apply PMF.ext
      intro obs
      rw [mixtureChannel_apply_of_nonzero 0 p r K L x hD]
      have hp : p x ≠ 0 := by
        intro hp
        apply hD
        simp [mixturePriorMass, hp]
      change (((1 - 0 : NNReal) : ENNReal) * p x * K x obs +
          (0 : ENNReal) * r x * L x obs) / mixturePriorMass 0 p r x = K x obs
      simpa [mixturePriorMass, mul_comm] using
        (ENNReal.mul_div_cancel_right (a := K x obs) (b := p x) hp (p.apply_ne_top x))

/-- The finite retained-family weight: baseline zero and generic strict
interior points, with no `some` label at `n = 0`. -/
noncomputable def mixtureGridWeight {n : ℕ} : Option (Fin n) → NNReal
  | none => 0
  | some k => ((k.1 + 1 : ℕ) : NNReal) / ((n + 2 : ℕ) : NNReal)

theorem mixtureGridWeight_le_one {n : ℕ} (a : Option (Fin n)) :
    mixtureGridWeight a ≤ 1 := by
  cases a with
  | none => simp [mixtureGridWeight]
  | some k =>
      simp only [mixtureGridWeight]
      apply (div_le_one (by positivity)).2
      norm_cast
      omega

theorem mixtureGridWeight_lt_one {n : ℕ} (a : Option (Fin n)) :
    mixtureGridWeight a < 1 := by
  cases a with
  | none => simp [mixtureGridWeight]
  | some k =>
      simp only [mixtureGridWeight]
      apply (div_lt_one (by positivity)).2
      norm_cast
      have hk := k.isLt
      omega

theorem mixtureGridWeight_some_pos {n : ℕ} (k : Fin n) :
    0 < mixtureGridWeight (some k) := by
  simp only [mixtureGridWeight]
  positivity

theorem mixtureGrid_card (n : ℕ) : Fintype.card (Option (Fin n)) = n + 1 := by
  simp

private structure MixtureState {n : ℕ} {I X Y : Type} [Fintype X]
    (y : I → Y) where
  label : Option (Fin n)
  model : I → PMF X × (X → PMF Y)
  positive : ∀ i, 0 < observationEvidence (model i).1 (model i).2 (y i)

private noncomputable def mixtureFamily {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (m : I → PMF X × (X → PMF Y))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    Option (Fin n) → I → PMF X × (X → PMF Y) := fun a i =>
  mixtureModel (mixtureGridWeight a) (mixtureGridWeight_le_one a)
    (m i).1 (m i).2 (aux a i).1 (aux a i).2

private theorem mixtureFamily_positive {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (m : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (m i).1 (m i).2 (y i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) (a : Option (Fin n))
    (i : I) :
    0 < observationEvidence (mixtureFamily m aux a i).1
      (mixtureFamily m aux a i).2 (y i) := by
  exact mixtureModel_evidence_pos (mixtureGridWeight a)
    (mixtureGridWeight_lt_one a) (m i).1 (m i).2 (aux a i).1 (aux a i).2
    (y i) (hold i)

private theorem mixtureFamily_support {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (m : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (m i).1 (m i).2 (y i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) (a : Option (Fin n))
    (i : I) :
    (posterior (m i).1 (m i).2 (y i) (hold i)).support ⊆
      (posterior (mixtureFamily m aux a i).1 (mixtureFamily m aux a i).2 (y i)
        (mixtureFamily_positive y m hold aux a i)).support := by
  exact mixtureModel_posterior_support (mixtureGridWeight a)
    (mixtureGridWeight_lt_one a) (m i).1 (m i).2 (aux a i).1 (aux a i).2
    (y i) (hold i)

private noncomputable def mixtureStateStep {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (s : MixtureState (n := n) (X := X) y)
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) : MixtureState (n := n) (X := X) y :=
  let q : I → PMF X := fun i => posterior (s.model i).1 (s.model i).2 (y i) (s.positive i)
  let F := mixtureFamily s.model aux
  let hE : ∀ a i, 0 < observationEvidence (F a i).1 (F a i).2 (y i) :=
    mixtureFamily_positive y s.model s.positive aux
  let hS : ∀ a i, (q i).support ⊆
      (posterior (F a i).1 (F a i).2 (y i) (hE a i)).support :=
    mixtureFamily_support y s.model s.positive aux
  let a := batchMStep q y F
  { label := a
    model := F a
    positive := (batchMStep_spec q y F hE hS).1.1 }

private noncomputable def mixtureState {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ℕ → MixtureState (n := n) (X := X) y
  | 0 => ⟨none, initial, initialPositive⟩
  | t + 1 => mixtureStateStep y (mixtureState y initial initialPositive seed t) (seed t)

/-- The actual model carried by the dependent positive-evidence state. -/
noncomputable def mixtureTrajectoryModel {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    I → PMF X × (X → PMF Y) :=
  (mixtureState y initial initialPositive seed t).model

/-- Bank zero is the unchanged initial model; bank `t+1` is constructed from
the actual current state model and seed `t`. -/
noncomputable def mixtureTrajectoryBank {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)
  | 0 => fun _ => initial
  | t + 1 => mixtureFamily (mixtureTrajectoryModel y initial initialPositive seed t) (seed t)

/-- Positive observation evidence of the actual dependent-state model. -/
theorem mixtureTrajectory_evidence {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y))
    (t : ℕ) (i : I) :
    0 < observationEvidence (mixtureTrajectoryModel y initial initialPositive seed t i).1
      (mixtureTrajectoryModel y initial initialPositive seed t i).2 (y i) := by
  exact (mixtureState y initial initialPositive seed t).positive i

private theorem mixtureTrajectoryBank_evidence {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ∀ t a i, 0 < observationEvidence
      (mixtureTrajectoryBank y initial initialPositive seed t a i).1
      (mixtureTrajectoryBank y initial initialPositive seed t a i).2 (y i) := by
  intro t
  cases t with
  | zero => exact fun _ i => initialPositive i
  | succ t =>
      exact mixtureFamily_positive y (mixtureTrajectoryModel y initial initialPositive seed t)
        (mixtureTrajectory_evidence y initial initialPositive seed t) (seed t)

/-- Pointwise successor equation for the actual trajectory bank. -/
theorem mixtureTrajectoryBank_succ {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y))
    (t : ℕ) (a : Option (Fin n)) (i : I) :
    mixtureTrajectoryBank y initial initialPositive seed (t + 1) a i =
      mixtureModel (mixtureGridWeight a) (mixtureGridWeight_le_one a)
        (mixtureTrajectoryModel y initial initialPositive seed t i).1
        (mixtureTrajectoryModel y initial initialPositive seed t i).2
        (seed t a i).1 (seed t a i).2 := by
  rfl

private noncomputable def mixtureCanonicalPath {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) : ℕ → Option (Fin n) :=
  changingEMPath y (mixtureTrajectoryBank y initial initialPositive seed)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed) none

private theorem mixtureTrajectory_replay {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    (mixtureCanonicalPath y initial initialPositive seed t,
      mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t)) =
      ((mixtureState y initial initialPositive seed t).label,
        (mixtureState y initial initialPositive seed t).model) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      let s := mixtureState y initial initialPositive seed t
      let F := mixtureFamily s.model (seed t)
      let q : I → PMF X := fun i => posterior (s.model i).1 (s.model i).2 (y i) (s.positive i)
      have hmodel : mixtureTrajectoryBank y initial initialPositive seed t
          (mixtureCanonicalPath y initial initialPositive seed t) = s.model := congrArg Prod.snd ih
      let qB : I → PMF X := fun i => posterior
          (mixtureTrajectoryBank y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i).1
          (mixtureTrajectoryBank y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i).2 (y i)
          (mixtureTrajectoryBank_evidence y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i)
      have hq : qB = q := by
        dsimp only [qB]
        funext i
        exact posterior_congr_of_model_eq _ _ _ _ _ (congrFun hmodel i)
      change (batchMStep qB y F, F (batchMStep qB y F)) =
        (batchMStep q y F, F (batchMStep q y F))
      rw [hq]

/-- The model selected by the canonical changing-bank path is exactly the
model carried by the dependent state, at the same time index. -/
theorem mixtureTrajectory_selected_model {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) =
      mixtureTrajectoryModel y initial initialPositive seed t := by
  exact congrArg Prod.snd (mixtureTrajectory_replay y initial initialPositive seed t)

private theorem mixtureTrajectory_keep {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    mixtureTrajectoryBank y initial initialPositive seed (t + 1) none =
      mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) := by
  calc
    _ = mixtureTrajectoryModel y initial initialPositive seed t := by
      funext i
      exact mixtureModel_zero _ _ _ _
    _ = _ := (mixtureTrajectory_selected_model y initial initialPositive seed t).symm

private theorem mixtureTrajectory_close {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ)
    (d : Option (Fin n)) (i : I) :
    (posterior
      (mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i).1
      (mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i).2 (y i)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i)).support ⊆
    (posterior (mixtureTrajectoryBank y initial initialPositive seed (t + 1) d i).1
      (mixtureTrajectoryBank y initial initialPositive seed (t + 1) d i).2 (y i)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed (t + 1) d i)).support := by
  let s := mixtureState y initial initialPositive seed t
  have hmodel : mixtureTrajectoryBank y initial initialPositive seed t
      (mixtureCanonicalPath y initial initialPositive seed t) = s.model :=
    mixtureTrajectory_selected_model y initial initialPositive seed t
  have hp := posterior_congr_of_model_eq _ _ (y i)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed t
      (mixtureCanonicalPath y initial initialPositive seed t) i) (s.positive i)
    (congrFun hmodel i)
  rw [hp]
  exact mixtureFamily_support y s.model s.positive (seed t) d i

/-- Genuine C150 integration: retained whole models and posterior support
closure make the actual canonical path NLL antitone. -/
theorem mixtureTrajectory_nll_antitone {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    Antitone (changingEMPathNLL y (mixtureTrajectoryBank y initial initialPositive seed)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed) none) := by
  exact changingEMPath_nll_antitone y (mixtureTrajectoryBank y initial initialPositive seed)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed) none (fun _ => none)
    (mixtureTrajectory_keep y initial initialPositive seed)
    (mixtureTrajectory_close y initial initialPositive seed)

end Hagi.Contracts.MixtureEMTrajectory

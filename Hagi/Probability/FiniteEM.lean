/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteLogScore

/-!
Finite fixed-observation variational expectation-maximization.

The expected complete cross-entropy minus entropy decomposes into
negative log observation evidence and KL divergence to the finite
posterior. With the exact old posterior and explicit support transport,
an improving M-step also nondecreases actual observation evidence.
The finite selector minimizes only expected complete cross-entropy
within the supplied candidate family.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open scoped BigOperators ENNReal

namespace Hagi.Probability.FiniteEM

noncomputable def jointMass {X Y : Type} (p₀ : PMF X) (K : X → PMF Y) (y : Y) (x : X) : ℝ :=
  (p₀ x * K x y).toReal

private theorem observationEvidence_toReal {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) :
    (observationEvidence p₀ K y).toReal = ∑ x, jointMass p₀ K y x := by
  rw [observationEvidence_eq_sum, ENNReal.toReal_sum]
  · rfl
  · intro x _
    exact ENNReal.mul_ne_top (p₀.apply_ne_top x) ((K x).apply_ne_top y)

private theorem observationEvidence_toReal_pos {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) :
    0 < (observationEvidence p₀ K y).toReal :=
  ENNReal.toReal_pos (ne_of_gt hobs) ((p₀.bind K).apply_ne_top y)

private theorem fromPMF_pos_of_mem_support {X : Type} (p : PMF X) (x : X)
    (hx : x ∈ p.support) : 0 < fromPMF p x :=
  ENNReal.toReal_pos ((p.mem_support_iff x).mp hx) (p.apply_ne_top x)

private theorem fromPMF_pos_of_pos {X : Type} (p : PMF X) (x : X)
    (hx : 0 < fromPMF p x) : x ∈ p.support :=
  (p.apply_pos_iff x).mp (ENNReal.toReal_pos_iff.mp hx).1

private theorem fromPMF_pos_map {X : Type} (p q : PMF X)
    (hpq : p.support ⊆ q.support) :
    ∀ x, 0 < fromPMF p x → 0 < fromPMF q x := by
  intro x hx
  exact fromPMF_pos_of_mem_support q x (hpq (fromPMF_pos_of_pos p x hx))

private theorem posterior_toReal_apply {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (x : X) :
    fromPMF (posterior p₀ K y hobs) x =
      jointMass p₀ K y x / (observationEvidence p₀ K y).toReal := by
  simp only [fromPMF, posterior_apply, jointMass, ENNReal.toReal_div]

private theorem jointMass_eq_evidence_mul_posterior {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (x : X) :
    jointMass p₀ K y x = (observationEvidence p₀ K y).toReal *
      fromPMF (posterior p₀ K y hobs) x := by
  rw [posterior_toReal_apply]
  field_simp [ne_of_gt (observationEvidence_toReal_pos p₀ K y hobs)]

private theorem ceDef_jointMass_eq {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (q : PMF X)
    (hpq : q.support ⊆ (posterior p₀ K y hobs).support) :
    ceDef (fromPMF q) (jointMass p₀ K y) - entDef (fromPMF q) =
      -Real.log (observationEvidence p₀ K y).toReal +
        (ceDef (fromPMF q) (fromPMF (posterior p₀ K y hobs)) -
          entDef (fromPMF q)) := by
  let _ : Nonempty X := observationEvidence_pos_nonempty p₀ K y hobs
  have hz : 0 < (observationEvidence p₀ K y).toReal :=
    observationEvidence_toReal_pos p₀ K y hobs
  have hcell : ∀ x, fromPMF q x * Real.log (jointMass p₀ K y x) =
      fromPMF q x * (Real.log (observationEvidence p₀ K y).toReal +
        Real.log (fromPMF (posterior p₀ K y hobs) x)) := by
    intro x
    by_cases hx : fromPMF q x = 0
    · simp only [hx, zero_mul]
    · have hxpos : 0 < fromPMF q x :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx)
      have hrpos : 0 < fromPMF (posterior p₀ K y hobs) x :=
        fromPMF_pos_map q (posterior p₀ K y hobs) hpq x hxpos
      rw [jointMass_eq_evidence_mul_posterior p₀ K y hobs,
        Real.log_mul (ne_of_gt hz) (ne_of_gt hrpos)]
  unfold ceDef entDef
  have hsum : (∑ x, fromPMF q x * Real.log (jointMass p₀ K y x)) =
      Real.log (observationEvidence p₀ K y).toReal +
        ∑ x, fromPMF q x * Real.log (fromPMF (posterior p₀ K y hobs) x) := by
    calc
      _ = ∑ x, fromPMF q x * (Real.log (observationEvidence p₀ K y).toReal +
          Real.log (fromPMF (posterior p₀ K y hobs) x)) :=
        Finset.sum_congr rfl (fun x _ => hcell x)
      _ = _ := by
        simp_rw [mul_add]
        have hnorm : (∑ i, fromPMF q i) = 1 := fromPMF_sum q
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hnorm]
        ring
  rw [hsum]
  ring

/-- Support inclusion gives nonnegative real KL divergence between finite PMFs. -/
theorem fromPMF_kl_nonneg {X : Type} [Fintype X]
    (p q : PMF X) (hpq : p.support ⊆ q.support) :
    0 ≤ klDef (fromPMF p) (fromPMF q) := by
  obtain ⟨x, hx⟩ := p.support_nonempty
  let _ : Nonempty X := ⟨x⟩
  exact klDef_nonneg_of_support (fromPMF p) (fromPMF q)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fromPMF_sum p) (fromPMF_sum q) (fromPMF_pos_map p q hpq)

private theorem fromPMF_kl_eq_zero_iff {X : Type} [Fintype X]
    (p q : PMF X) (hpq : p.support ⊆ q.support) :
    klDef (fromPMF p) (fromPMF q) = 0 ↔ q = p := by
  obtain ⟨x, hx⟩ := p.support_nonempty
  let _ : Nonempty X := ⟨x⟩
  have hzero := klDef_eq_zero_iff_of_support (fromPMF p) (fromPMF q)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fromPMF_sum p) (fromPMF_sum q) (fromPMF_pos_map p q hpq)
  constructor
  · intro h
    have hvec := hzero.mp h
    apply PMF.ext
    intro y
    exact (ENNReal.toReal_eq_toReal_iff'
      (q.apply_ne_top y) (p.apply_ne_top y)).mp (congrFun hvec y)
  · intro h
    exact hzero.mpr (congrArg fromPMF h)

theorem ceDef_jointMass_sub_entDef_eq {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) (q : PMF X)
    (hobs : 0 < observationEvidence p₀ K y)
    (hpq : q.support ⊆ (posterior p₀ K y hobs).support) :
    ceDef (fromPMF q) (jointMass p₀ K y) - entDef (fromPMF q) =
      -Real.log (observationEvidence p₀ K y).toReal +
        klDef (fromPMF q) (fromPMF (posterior p₀ K y hobs)) := by
  rw [ceDef_jointMass_eq p₀ K y hobs q hpq,
    klDef_eq_ceDef_sub_of_support (fromPMF q)
      (fromPMF (posterior p₀ K y hobs)) (fun _ => ENNReal.toReal_nonneg)
      (fromPMF_pos_map q (posterior p₀ K y hobs) hpq)]
  rw [← ceDef_self (fromPMF q)]

theorem neg_log_evidence_le_ceDef_jointMass_sub_entDef {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) (q : PMF X)
    (hobs : 0 < observationEvidence p₀ K y)
    (hpq : q.support ⊆ (posterior p₀ K y hobs).support) :
    -Real.log (observationEvidence p₀ K y).toReal ≤
      ceDef (fromPMF q) (jointMass p₀ K y) - entDef (fromPMF q) := by
  rw [ceDef_jointMass_sub_entDef_eq p₀ K y q hobs hpq]
  have hkl := fromPMF_kl_nonneg q (posterior p₀ K y hobs) hpq
  linarith

theorem ceDef_posterior_jointMass_sub_entDef_eq {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) :
    ceDef (fromPMF (posterior p₀ K y hobs)) (jointMass p₀ K y) -
        entDef (fromPMF (posterior p₀ K y hobs)) =
      -Real.log (observationEvidence p₀ K y).toReal := by
  rw [ceDef_jointMass_sub_entDef_eq p₀ K y
    (posterior p₀ K y hobs) hobs Set.Subset.rfl]
  rw [(fromPMF_kl_eq_zero_iff (posterior p₀ K y hobs)
    (posterior p₀ K y hobs) Set.Subset.rfl).mpr rfl]
  ring

theorem ceDef_jointMass_sub_entDef_eq_iff {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) (q : PMF X)
    (hobs : 0 < observationEvidence p₀ K y)
    (hpq : q.support ⊆ (posterior p₀ K y hobs).support) :
    (ceDef (fromPMF q) (jointMass p₀ K y) - entDef (fromPMF q) =
        -Real.log (observationEvidence p₀ K y).toReal) ↔
      q = posterior p₀ K y hobs := by
  constructor
  · intro h
    have hid := ceDef_jointMass_sub_entDef_eq p₀ K y q hobs hpq
    have hzero : klDef (fromPMF q) (fromPMF (posterior p₀ K y hobs)) = 0 := by
      rw [hid] at h
      linarith
    exact ((fromPMF_kl_eq_zero_iff q (posterior p₀ K y hobs) hpq).mp hzero).symm
  · intro h
    subst q
    exact ceDef_posterior_jointMass_sub_entDef_eq p₀ K y hobs

theorem log_evidence_add_klDef_le_of_ceDef_jointMass_le {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K₀ : X → PMF Y) (p₁ : PMF X) (K₁ : X → PMF Y) (y : Y)
    (hobs₀ : 0 < observationEvidence p₀ K₀ y)
    (hobs₁ : 0 < observationEvidence p₁ K₁ y)
    (hq₁ : (posterior p₀ K₀ y hobs₀).support ⊆ (posterior p₁ K₁ y hobs₁).support)
    (hM : ceDef (fromPMF (posterior p₀ K₀ y hobs₀)) (jointMass p₁ K₁ y) ≤
      ceDef (fromPMF (posterior p₀ K₀ y hobs₀)) (jointMass p₀ K₀ y)) :
    Real.log (observationEvidence p₀ K₀ y).toReal +
        klDef (fromPMF (posterior p₀ K₀ y hobs₀))
          (fromPMF (posterior p₁ K₁ y hobs₁)) ≤
      Real.log (observationEvidence p₁ K₁ y).toReal := by
  have hnew := ceDef_jointMass_sub_entDef_eq p₁ K₁ y
    (posterior p₀ K₀ y hobs₀) hobs₁ hq₁
  have hold := ceDef_posterior_jointMass_sub_entDef_eq p₀ K₀ y hobs₀
  linarith

theorem observationEvidence_le_of_ceDef_jointMass_le {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K₀ : X → PMF Y) (p₁ : PMF X) (K₁ : X → PMF Y) (y : Y)
    (hobs₀ : 0 < observationEvidence p₀ K₀ y)
    (hobs₁ : 0 < observationEvidence p₁ K₁ y)
    (hq₁ : (posterior p₀ K₀ y hobs₀).support ⊆ (posterior p₁ K₁ y hobs₁).support)
    (hM : ceDef (fromPMF (posterior p₀ K₀ y hobs₀)) (jointMass p₁ K₁ y) ≤
      ceDef (fromPMF (posterior p₀ K₀ y hobs₀)) (jointMass p₀ K₀ y)) :
    observationEvidence p₀ K₀ y ≤ observationEvidence p₁ K₁ y := by
  have hlog := log_evidence_add_klDef_le_of_ceDef_jointMass_le
    p₀ K₀ p₁ K₁ y hobs₀ hobs₁ hq₁ hM
  have hkl := fromPMF_kl_nonneg (posterior p₀ K₀ y hobs₀)
    (posterior p₁ K₁ y hobs₁) hq₁
  have hz₀ := observationEvidence_toReal_pos p₀ K₀ y hobs₀
  have hz₁ := observationEvidence_toReal_pos p₁ K₁ y hobs₁
  have hreal : (observationEvidence p₀ K₀ y).toReal ≤
      (observationEvidence p₁ K₁ y).toReal := by
    apply (Real.log_le_log_iff hz₀ hz₁).mp
    linarith
  exact (ENNReal.toReal_le_toReal ((p₀.bind K₀).apply_ne_top y)
    ((p₁.bind K₁).apply_ne_top y)).mp hreal

noncomputable def mStep {A X Y : Type} [Fintype X] [Fintype A] [Nonempty A]
    (q : PMF X) (y : Y) (c : A → PMF X × (X → PMF Y)) : A := by
  classical
  exact Classical.choose (Finite.exists_min
    (fun a => ceDef (fromPMF q) (jointMass (c a).1 (c a).2 y)))

theorem mStep_spec {A X Y : Type} [Fintype X] [Fintype A] [Nonempty A]
    (q : PMF X) (y : Y) (c : A → PMF X × (X → PMF Y))
    (hE : ∀ a, 0 < observationEvidence (c a).1 (c a).2 y)
    (hS : ∀ a, q.support ⊆ (posterior (c a).1 (c a).2 y (hE a)).support) :
    ((0 < observationEvidence (c (mStep q y c)).1 (c (mStep q y c)).2 y) ∧
      q.support ⊆ (posterior (c (mStep q y c)).1 (c (mStep q y c)).2 y
        (hE (mStep q y c))).support) ∧
      ∀ a, ceDef (fromPMF q) (jointMass (c (mStep q y c)).1
        (c (mStep q y c)).2 y) ≤
        ceDef (fromPMF q) (jointMass (c a).1 (c a).2 y) := by
  refine ⟨⟨hE (mStep q y c), hS (mStep q y c)⟩, ?_⟩
  exact Classical.choose_spec (Finite.exists_min
    (fun a => ceDef (fromPMF q) (jointMass (c a).1 (c a).2 y)))

theorem current_observationEvidence_le_mStep {A X Y : Type} [Fintype X]
    [Fintype A] [Nonempty A] (q : PMF X) (y : Y)
    (c : A → PMF X × (X → PMF Y))
    (hE : ∀ a, 0 < observationEvidence (c a).1 (c a).2 y)
    (hS : ∀ a, q.support ⊆ (posterior (c a).1 (c a).2 y (hE a)).support)
    (a₀ : A) (hq : q = posterior (c a₀).1 (c a₀).2 y (hE a₀)) :
    observationEvidence (c a₀).1 (c a₀).2 y ≤
      observationEvidence (c (mStep q y c)).1 (c (mStep q y c)).2 y := by
  subst q
  have hmin := (mStep_spec (posterior (c a₀).1 (c a₀).2 y (hE a₀)) y c hE hS).2 a₀
  exact observationEvidence_le_of_ceDef_jointMass_le
    (c a₀).1 (c a₀).2 (c (mStep (posterior (c a₀).1 (c a₀).2 y (hE a₀)) y c)).1
      (c (mStep (posterior (c a₀).1 (c a₀).2 y (hE a₀)) y c)).2 y
    (hE a₀) (hE _) (hS _) hmin

end Hagi.Probability.FiniteEM

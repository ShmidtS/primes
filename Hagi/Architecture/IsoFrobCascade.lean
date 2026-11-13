/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.ErrorProp
import Hagi.Core.FrobOuter
import Hagi.Architecture.AlignedMerge

set_option linter.style.header false

/-!
# Isotropic-Frobenius cascade sensitivities (A8 F7)

Deep sequential nets violate the additive-separability premise of
RankBudget when sensitivities are taken as spectral products
`∏ ‖J_k‖`: the worst-case product over-estimates early layers
and starves later ones (A8 empirical: spectral cascade WORSE than
uniform; isotropic-Frobenius calibration `‖J_{>j}‖_F²/d · ‖h_j‖²`
fixed it, MSE 2.2e-5 vs uniform 2.5e-5 — motivation only, never a
Lean premise). The provable slice over the C250 linear-cascade
carrier (`Hagi.Core.propagateLin`):

* `isoFrobEnergy J = frobSq J / d` — the A8 per-dimension
  calibration constant.
* `columnEnergy_basis` — the math core: the total column energy
  over the standard orthonormal basis EQUALS the Frobenius energy
  (the exact algebraic surrogate of the isotropic expected gain
  `E[‖Jx‖²] = ‖J‖_F²/d`; no probability needed — the basis
  average is the isotropic average).
* `isoFrobEnergy_eq_basis_avg` — per-dimension reading.
* `isoFrobEnergy_le_opNorm_sq` — the isotropic average
  UNDER-estimates the worst-case linfty-operator gain charged by
  `cascadeGain`: `frobSq J / d ≤ ‖J‖²` (honest direction: for the
  linfty operator norm `frobSq ≥ d‖J‖²` is FALSE — the spectral
  product over-estimates, the iso-average calibrates).
* `propagateLin_frobEnergy_le` — the cascade energy bound
  `‖propagateLin S δ‖₂² ≤ (∏ frobSq J_l) ‖δ‖₂²` (per-layer
  `frobSubord`, reused, + induction).
* `cascadeFrobEnergy_eq` + `propagateLin_isoEnergy_le` — the
  iso-normalized form `≤ d^|S| · ∏(frobSq_l/d) · ‖δ‖²`.
* `isoCascadeEnergy_le_cascadeGain_sq` — the F7 comparison: the
  iso cascade energy never exceeds `cascadeGain S²`.
-/

open scoped Matrix Matrix.Norms.Operator NNReal
open Finset

namespace Hagi.Architecture

section IsoFrob

variable {d : ℕ}

/-- A8 F7 calibration constant: per-dimension Frobenius energy. -/
noncomputable def isoFrobEnergy (J : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Hagi.Core.frobSq J / d

/-- frobSq nonneg helper. -/
theorem frobSq_nonneg' (J : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ Hagi.Core.frobSq J := by
  unfold Hagi.Core.frobSq
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- THE math core: the total column energy over the standard
orthonormal basis equals the Frobenius energy — the algebraic
surrogate of the isotropic expected gain (no probability). -/
theorem columnEnergy_basis (J : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i : Fin d, ∑ j : Fin d, (J *ᵥ Pi.single i (1:ℝ)) j ^ 2
      = Hagi.Core.frobSq J := by
  unfold Hagi.Core.frobSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hcol : (J *ᵥ Pi.single i (1:ℝ)) j = J j i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
      Finset.sum_ite_eq']
  rw [hcol]

/-- Per-dimension reading: isoFrobEnergy = basis average of the
squared column gains. -/
theorem isoFrobEnergy_eq_basis_avg (J : Matrix (Fin d) (Fin d) ℝ) :
    isoFrobEnergy J
      = (∑ i : Fin d, ∑ j : Fin d, (J *ᵥ Pi.single i (1:ℝ)) j ^ 2)
          / (d : ℝ) := by
  rw [columnEnergy_basis, isoFrobEnergy]

/-- Row square sum at most the squared row ℓ1. -/
theorem row_sq_sum_le_rowL1_sq (J : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (∑ j : Fin d, (J i j) ^ 2) ≤ (∑ j : Fin d, |J i j|) ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin d))) (f := fun j => |J i j|)
    (fun j _ => abs_nonneg _)
  simpa using h

/-- Row ℓ1 ≤ the linfty operator norm (closed form
`Matrix.linfty_opNorm_def`). -/
theorem rowL1_le_opNorm (J : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    ∑ j : Fin d, |J i j| ≤ ‖J‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hcoe : ∀ x : ℝ, |x| = ((‖x‖₊ : ℝ≥0) : ℝ) := fun x => by norm_num
  have hle : (∑ j : Fin d, (‖J i j‖₊ : ℝ≥0))
      ≤ (Finset.univ : Finset (Fin d)).sup
        (fun i' => ∑ j : Fin d, (‖J i' j‖₊ : ℝ≥0)) :=
    Finset.le_sup
      (f := fun i' => ∑ j : Fin d, (‖J i' j‖₊ : ℝ≥0)) (Finset.mem_univ i)
  have hcoe' : (∑ j : Fin d, |J i j|)
      = (∑ j : Fin d, ((‖J i j‖₊ : ℝ≥0) : ℝ)) :=
    Finset.sum_congr rfl (fun j _ => hcoe _)
  calc (∑ j : Fin d, |J i j|)
      = (∑ j : Fin d, ((‖J i j‖₊ : ℝ≥0) : ℝ)) := hcoe'
    _ ≤ ((((Finset.univ : Finset (Fin d)).sup
        (fun i' => ∑ j : Fin d, (‖J i' j‖₊ : ℝ≥0))) : ℝ≥0) : ℝ) := by
          exact_mod_cast hle

/-- The isotropic-average energy UNDER-estimates the worst-case
linfty-operator gain charged by `cascadeGain`:
`frobSq J / d ≤ ‖J‖²` (true for every `d`, also `d = 0`, where
the division is zero by `div_zero`). -/
theorem isoFrobEnergy_le_opNorm_sq (J : Matrix (Fin d) (Fin d) ℝ) :
    isoFrobEnergy J ≤ ‖J‖ ^ 2 := by
  have hrow : ∀ i : Fin d, (∑ j : Fin d, (J i j) ^ 2) ≤ ‖J‖ ^ 2 := by
    intro i
    have h1 := rowL1_le_opNorm J i
    have hA : (0:ℝ) ≤ ∑ j : Fin d, |J i j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hB : (0:ℝ) ≤ ‖J‖ := norm_nonneg _
    have hL1 : (∑ j : Fin d, |J i j|) * (∑ j : Fin d, |J i j|)
        ≤ (∑ j : Fin d, |J i j|) * ‖J‖ :=
      mul_le_mul_of_nonneg_left h1 hA
    have hL2 : (∑ j : Fin d, |J i j|) * ‖J‖ ≤ ‖J‖ * ‖J‖ :=
      mul_le_mul_of_nonneg_right h1 hB
    calc (∑ j : Fin d, (J i j) ^ 2)
        ≤ (∑ j : Fin d, |J i j|) ^ 2 := row_sq_sum_le_rowL1_sq J i
      _ = (∑ j : Fin d, |J i j|) * (∑ j : Fin d, |J i j|) := by ring
      _ ≤ ‖J‖ * ‖J‖ := by nlinarith
      _ = ‖J‖ ^ 2 := by ring
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    have hz : (∑ i : Fin 0, ∑ j : Fin 0, (J i j) ^ 2) = 0 := by simp
    unfold isoFrobEnergy Hagi.Core.frobSq
    simp [hz, div_zero]
  · have hcard : (∑ i : Fin d, ‖J‖ ^ 2) = (d : ℝ) * ‖J‖ ^ 2 := by
      simp
    have hdR : ((d:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    calc isoFrobEnergy J = Hagi.Core.frobSq J / d := rfl
      _ = (∑ i : Fin d, ∑ j : Fin d, (J i j) ^ 2) / d := rfl
      _ ≤ (∑ i : Fin d, ‖J‖ ^ 2) / d :=
          div_le_div_of_nonneg_right
            (Finset.sum_le_sum (fun i _ => hrow i))
            (Nat.cast_nonneg d)
      _ = ((d:ℝ) * ‖J‖ ^ 2) / d := by rw [hcard]
      _ = ‖J‖ ^ 2 := by field_simp

end IsoFrob

section Cascade

variable {d : ℕ}

/-- The cascade Frobenius energy: product of per-layer
Frobenius energies (the worst-case ℓ2 cascade charge). -/
def cascadeFrobEnergy
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) : ℝ :=
  (S.map fun p => Hagi.Core.frobSq p.1).prod

/-- The isotropic-normalized cascade energy: product of
per-layer `isoFrobEnergy = frobSq / d` (the A8 F7 weighting). -/
noncomputable def isoCascadeEnergy
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) : ℝ :=
  (S.map fun p => isoFrobEnergy p.1).prod

theorem cascadeFrobEnergy_nonneg
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) :
    0 ≤ cascadeFrobEnergy S :=
  List.prod_nonneg (by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨q, _, rfl⟩ := hz
    exact frobSq_nonneg' q.1)

theorem isoCascadeEnergy_nonneg
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) :
    0 ≤ isoCascadeEnergy S := by
  have hpos : ∀ p ∈ S, 0 ≤ isoFrobEnergy p.1 := by
    intro p _
    unfold isoFrobEnergy
    exact div_nonneg (frobSq_nonneg' p.1) (Nat.cast_nonneg d)
  exact List.prod_nonneg (by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact hpos q hq)

theorem cascadeFrobEnergy_cons
    (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) :
    cascadeFrobEnergy (p :: S)
      = cascadeFrobEnergy S * Hagi.Core.frobSq p.1 := by
  simp only [cascadeFrobEnergy, List.map_cons, List.prod_cons]
  ring

/-- Honest cascade energy bound: the ℓ2 output energy of the
linear cascade fold is at most the product of per-layer
Frobenius energies times the entering energy (per-layer
`frobSubord` + induction; reuses `Hagi.Architecture.frobSubord`). -/
theorem propagateLin_frobEnergy_le
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (δ : Fin d → ℝ) :
    (Hagi.Core.propagateLin S δ) ⬝ᵥ (Hagi.Core.propagateLin S δ)
      ≤ cascadeFrobEnergy S * (δ ⬝ᵥ δ) := by
  induction S generalizing δ with
  | nil =>
      show (Hagi.Core.propagateLin [] δ) ⬝ᵥ (Hagi.Core.propagateLin [] δ)
        ≤ cascadeFrobEnergy [] * (δ ⬝ᵥ δ)
      simp only [Hagi.Core.propagateLin, cascadeFrobEnergy, List.map_nil,
        List.prod_nil, List.foldl_nil, one_mul]
      exact le_rfl
  | cons p S ih =>
      have hE : 0 ≤ cascadeFrobEnergy S := cascadeFrobEnergy_nonneg S
      have h1 := ih (p.1 *ᵥ δ)
      have h2 := Hagi.Architecture.frobSubord p.1 δ
      rw [cascadeFrobEnergy_cons]
      have hrw : Hagi.Core.propagateLin (p :: S) δ
          = Hagi.Core.propagateLin S (p.1 *ᵥ δ) := rfl
      rw [hrw]
      calc (Hagi.Core.propagateLin S (p.1 *ᵥ δ)) ⬝ᵥ
            (Hagi.Core.propagateLin S (p.1 *ᵥ δ))
          ≤ cascadeFrobEnergy S * ((p.1 *ᵥ δ) ⬝ᵥ (p.1 *ᵥ δ)) := h1
        _ ≤ cascadeFrobEnergy S * (Hagi.Core.frobSq p.1 * (δ ⬝ᵥ δ)) :=
            mul_le_mul_of_nonneg_left h2 hE
        _ = (cascadeFrobEnergy S * Hagi.Core.frobSq p.1) * (δ ⬝ᵥ δ) := by
            ring

/-- Identity between the two normalizations:
`cascadeFrobEnergy = d ^ length * isoCascadeEnergy` (for
`d > 0`). -/
theorem cascadeFrobEnergy_eq (hd : 0 < d)
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) :
    cascadeFrobEnergy S = (d:ℝ) ^ S.length * isoCascadeEnergy S := by
  induction S with
  | nil => simp [cascadeFrobEnergy, isoCascadeEnergy]
  | cons p S ih =>
      have hdR : ((d:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
      have h1 := cascadeFrobEnergy_cons p S
      have h2 : isoCascadeEnergy (p :: S)
          = isoFrobEnergy p.1 * isoCascadeEnergy S := by
        simp only [isoCascadeEnergy, List.map_cons, List.prod_cons]
      rw [h1, h2, ih,
        show (p :: S).length = S.length + 1 from rfl, pow_succ,
        show isoFrobEnergy p.1 = Hagi.Core.frobSq p.1 / (d:ℝ) from rfl]
      field_simp

/-- The iso-normalized cascade energy bound: output energy at most
`d ^ |S| * ∏ (frobSq_l / d) *` entering energy — the A8 F7
cascade-weighted sensitivity, proven honestly. -/
theorem propagateLin_isoEnergy_le (hd : 0 < d)
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)))
    (δ : Fin d → ℝ) :
    (Hagi.Core.propagateLin S δ) ⬝ᵥ (Hagi.Core.propagateLin S δ)
      ≤ (d:ℝ) ^ S.length * isoCascadeEnergy S * (δ ⬝ᵥ δ) := by
  rw [← cascadeFrobEnergy_eq hd S]
  exact propagateLin_frobEnergy_le S δ

/-- The F7 comparison: the isotropic cascade energy never exceeds
the squared spectral-product gain `cascadeGain S ^ 2` (each layer:
`frobSq / d ≤ ‖J‖²`, then product monotonicity). -/
theorem isoCascadeEnergy_le_cascadeGain_sq
    (S : List (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ))) :
    isoCascadeEnergy S ≤ (Hagi.Core.cascadeGain S) ^ 2 := by
  induction S with
  | nil => simp [isoCascadeEnergy, Hagi.Core.cascadeGain]
  | cons p S ih =>
      have hG : 0 ≤ Hagi.Core.cascadeGain S :=
        List.prod_nonneg (by
          intro z hz
          simp only [List.mem_map] at hz
          obtain ⟨q, _, rfl⟩ := hz
          exact norm_nonneg q.1)
      have h1 : isoFrobEnergy p.1 ≤ ‖p.1‖ ^ 2 :=
        isoFrobEnergy_le_opNorm_sq p.1
      have h2 : 0 ≤ ‖p.1‖ ^ 2 := sq_nonneg _
      have hCE : 0 ≤ isoCascadeEnergy S := isoCascadeEnergy_nonneg S
      have hg : Hagi.Core.cascadeGain (p :: S)
          = ‖p.1‖ * Hagi.Core.cascadeGain S := by
        simp only [Hagi.Core.cascadeGain, List.map_cons, List.prod_cons]
      rw [hg]
      calc isoFrobEnergy p.1 * isoCascadeEnergy S
          ≤ ‖p.1‖ ^ 2 * isoCascadeEnergy S :=
              mul_le_mul_of_nonneg_right h1 hCE
        _ ≤ ‖p.1‖ ^ 2 * (Hagi.Core.cascadeGain S) ^ 2 :=
              mul_le_mul_of_nonneg_left ih h2
        _ = (‖p.1‖ * Hagi.Core.cascadeGain S) ^ 2 := by ring

end Cascade

end Hagi.Architecture

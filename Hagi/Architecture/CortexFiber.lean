/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CortexFiber: the energy laws of the shared-cortex ⊕ expert-fiber
geometry

Model: a shared orthonormal cortex `U` (`IsOrthoCol U`, i.e.
`Uᵀ * U = 1`) and expert fiber bases `V`. Formalized:

* `orthoNorm` — an orthonormal basis is an isometry:
  `(U *ᵥ z) ⬝ᵥ (U *ᵥ z) = z ⬝ᵥ z`.
* `fiberCross` — if `Uᵀ * V = 0` then
  `(U *ᵥ z) ⬝ᵥ (V *ᵥ w) = 0`.
* `fiberPythagoras` — with orthonormal `U`, `V` and
  `Uᵀ * V = 0`, the energy decomposes without a cross term:
  `(U *ᵥ z + V *ᵥ w) ⬝ᵥ (U *ᵥ z + V *ᵥ w) = z ⬝ᵥ z + w ⬝ᵥ w`.
* `fiberParamCount` — for `r < d`, `r * d < d * d`.

That trained experts align to a common `U` is a hypothesis,
not proved here.
-/

namespace Hagi.Architecture

open Finset Matrix

/-- Orthonormal columns: Uᵀ U = I (a shared semantic cortex
basis / an aligned fiber basis). -/
def IsOrthoCol {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ) : Prop :=
  Uᵀ * U = 1


/-- The key transpose identity: the mixed product equals the
gram-form vecMul. -/
theorem mulVec_vecMul_gram {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (z : Fin c → ℝ) :
    (U *ᵥ z) ᵥ* V = z ᵥ* (Uᵀ * V) := by
  ext i
  simp only [Matrix.vecMul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- An orthonormal basis preserves energy exactly:
`(U *ᵥ z) ⬝ᵥ (U *ᵥ z) = z ⬝ᵥ z`. -/
theorem orthoNorm {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (z : Fin c → ℝ) :
    (U.mulVec z) ⬝ᵥ (U.mulVec z) = z ⬝ᵥ z := by
  have key : (U.mulVec z) ⬝ᵥ (U.mulVec z)
      = z ⬝ᵥ ((Uᵀ * U).mulVec z) := by
    rw [Matrix.dotProduct_mulVec, mulVec_vecMul_gram, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [key, hU, Matrix.one_mulVec]

/-- If `Uᵀ * V = 0`, the cross inner product vanishes:
`(U *ᵥ z) ⬝ᵥ (V *ᵥ w) = 0`. -/
theorem fiberCross {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (hUV : Uᵀ * V = 0)
    (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (U.mulVec z) ⬝ᵥ (V.mulVec w) = 0 := by
  have key : (U.mulVec z) ⬝ᵥ (V.mulVec w)
      = z ⬝ᵥ ((Uᵀ * V).mulVec w) := by
    rw [Matrix.dotProduct_mulVec, mulVec_vecMul_gram, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [key, hUV, Matrix.zero_mulVec, dotProduct_zero]

/-- With orthonormal `U`, `V` and `Uᵀ * V = 0`, the energy
decomposes without a cross term:
`(U *ᵥ z + V *ᵥ w) ⬝ᵥ (U *ᵥ z + V *ᵥ w) = z ⬝ᵥ z + w ⬝ᵥ w`. -/
theorem fiberPythagoras {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ)
    (hU : IsOrthoCol U) (hV : IsOrthoCol V) (hUV : Uᵀ * V = 0)
    (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (U.mulVec z + V.mulVec w) ⬝ᵥ (U.mulVec z + V.mulVec w)
      = z ⬝ᵥ z + w ⬝ᵥ w := by
  have h1 : (U.mulVec z + V.mulVec w) ⬝ᵥ (U.mulVec z + V.mulVec w)
      = (U.mulVec z) ⬝ᵥ (U.mulVec z)
        + 2 * ((U.mulVec z) ⬝ᵥ (V.mulVec w))
        + (V.mulVec w) ⬝ᵥ (V.mulVec w) := by
    rw [dotProduct_add, add_dotProduct, add_dotProduct]
    nlinarith [dotProduct_comm (U *ᵥ z) (V *ᵥ w)]
  rw [h1, orthoNorm U hU z, fiberCross U V hUV z w, orthoNorm V hV w]
  ring

/-- For `r < d`, a rank-`r` fiber's coordinate count is
strictly smaller than a full layer's: `r * d < d * d`. -/
theorem fiberParamCount {d r : ℕ} (hr : r < d) :
    r * d < d * d := by
  have h0 : 0 < d := lt_of_le_of_lt (Nat.zero_le r) hr
  exact Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl d) h0

/-- Невязка замороженного ствола: цель `t`, достижимое `y = U·z + V·w` с
ортонормальными `U`, `V`, `Uᵀ V = 0`; `P t = t − U·(Uᵀ t) − V·(Vᵀ t)` —
компонента цели вне `span U ⊕ span V`. Тогда
`‖t − y‖² = ‖P t‖² + ‖Uᵀ t − z‖² + ‖Vᵀ t − w‖²`: минимум по `(z, w)` равен
`‖P t‖²` — пока ствол `U` заморожен (ранний FrozenTrunk), эта компонента
недостижима при любом волокне `V` (HagiOptimalV3: заморозка ствола после
одного домена, варианты Frozen и Hybrid). -/
theorem frozen_trunk_unreachable {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (hU : IsOrthoCol U) (hV : IsOrthoCol V)
    (hUV : Uᵀ * V = 0) (t : Fin d → ℝ) (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (t - (U *ᵥ z + V *ᵥ w)) ⬝ᵥ (t - (U *ᵥ z + V *ᵥ w))
      = (t - U *ᵥ (Uᵀ *ᵥ t) - V *ᵥ (Vᵀ *ᵥ t)) ⬝ᵥ (t - U *ᵥ (Uᵀ *ᵥ t) - V *ᵥ (Vᵀ *ᵥ t))
        + (U *ᵥ (Uᵀ *ᵥ t - z) + V *ᵥ (Vᵀ *ᵥ t - w)) ⬝ᵥ (U *ᵥ (Uᵀ *ᵥ t - z) + V *ᵥ (Vᵀ *ᵥ t - w)) := by
  have dotMulVec : ∀ (A : Matrix (Fin d) (Fin c) ℝ) (x : Fin c → ℝ) (y : Fin d → ℝ),
      (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
    intro A x y
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]
    have h := Matrix.vecMul_transpose (Aᵀ) y
    simp only [Matrix.transpose_transpose] at h
    rw [h]
  have dotMulVec' : ∀ (A : Matrix (Fin d) (Fin r) ℝ) (x : Fin r → ℝ) (y : Fin d → ℝ),
      (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
    intro A x y
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]
    have h := Matrix.vecMul_transpose (Aᵀ) y
    simp only [Matrix.transpose_transpose] at h
    rw [h]
  set a := Uᵀ *ᵥ t - z with ha
  set b := Vᵀ *ᵥ t - w with hb
  set P := t - U *ᵥ (Uᵀ *ᵥ t) - V *ᵥ (Vᵀ *ᵥ t) with hP
  have hsum : t - (U *ᵥ z + V *ᵥ w) = P + (U *ᵥ a + V *ᵥ b) := by
    simp only [hP, ha, hb, Matrix.mulVec_sub]
    abel
  have hPa : (U *ᵥ a) ⬝ᵥ P = 0 := by
    have key : ∀ u : Fin c → ℝ, (U *ᵥ u) ⬝ᵥ P = 0 := by
      intro u
      rw [hP, dotProduct_sub, dotProduct_sub]
      have h1 : (U *ᵥ u) ⬝ᵥ t = u ⬝ᵥ (Uᵀ *ᵥ t) := by
        exact dotMulVec U u t
      have h2 : (U *ᵥ u) ⬝ᵥ (U *ᵥ (Uᵀ *ᵥ t)) = u ⬝ᵥ (Uᵀ *ᵥ t) := by
        rw [dotMulVec U u (U *ᵥ (Uᵀ *ᵥ t)), Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      have h3 : (U *ᵥ u) ⬝ᵥ (V *ᵥ (Vᵀ *ᵥ t)) = 0 := fiberCross U V hUV u _
      rw [h1, h2, h3]; ring
    exact key a
  have hPb : (V *ᵥ b) ⬝ᵥ P = 0 := by
    have key : ∀ u : Fin r → ℝ, (V *ᵥ u) ⬝ᵥ P = 0 := by
      intro u
      rw [hP, dotProduct_sub, dotProduct_sub]
      have h1 : (V *ᵥ u) ⬝ᵥ t = u ⬝ᵥ (Vᵀ *ᵥ t) := by
        exact dotMulVec' V u t
      have h2 : (V *ᵥ u) ⬝ᵥ (V *ᵥ (Vᵀ *ᵥ t)) = u ⬝ᵥ (Vᵀ *ᵥ t) := by
        rw [dotMulVec' V u (V *ᵥ (Vᵀ *ᵥ t)), Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
      have h3 : (V *ᵥ u) ⬝ᵥ (U *ᵥ (Uᵀ *ᵥ t)) = 0 := by
        rw [dotProduct_comm]; exact fiberCross U V hUV _ u
      rw [h1, h2, h3]; ring
    exact key b
  have hPa' : P ⬝ᵥ (U *ᵥ a) = 0 := by rw [dotProduct_comm]; exact hPa
  have hPb' : P ⬝ᵥ (V *ᵥ b) = 0 := by rw [dotProduct_comm]; exact hPb
  have hperp : (U *ᵥ a) ⬝ᵥ (V *ᵥ b) = 0 := fiberCross U V hUV a b
  have hperp' : (V *ᵥ b) ⬝ᵥ (U *ᵥ a) = 0 := by rw [dotProduct_comm]; exact hperp
  rw [hsum]
  simp only [add_dotProduct, dotProduct_add, hPa, hPb, hPa', hPb', hperp, hperp',
    add_zero, zero_add, add_zero]

end Hagi.Architecture

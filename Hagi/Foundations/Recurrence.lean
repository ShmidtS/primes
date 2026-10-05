/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.Recurrence — каноническая рекуррентная лемма

Миграция-2026-10-05 (аудит графа импортов): одна пара лемм
для линейной рекурренты x_{t+1} <= rho * x_t + c на ГОРИЗОНТЕ
t < T — вместо 8+ разрозненных копий (Audit.Foundations.
anchor_recurrence, Dynamics.Contraction, Data.DistillRecursion,
JointPreserve.diversity_floor, Growth.SeedOnly.disp_recurrence_,
Saturation.pl_gap_geometric, GainRenewal.gain_renewal_recurrence,
Energy.FreeEnergy.geometric_pool_identity — переводятся
постепенно).

Горизонт T — В САМОЙ ЛЕММЕ (посылки только при t < T):
ошибка квантификации по всем t не воспроизводится в новых
капстоунах.
-/

open Finset Real

namespace Hagi.Foundations

variable (rho c : ℝ)

/-- Телескоп-тождество геометрической суммы:
(1 - rho) * sum_{i<t} rho^i = 1 - rho^t. -/
theorem geom_telescope (T : ℕ) :
    (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i = 1 - rho ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      have hexp : (1 - rho) * (∑ i ∈ Finset.range T, rho ^ i + rho ^ T)
          = (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i
            + (1 - rho) * rho ^ T := by ring
      rw [hexp, ih, pow_succ]
      ring

/-- **Верхняя рекуррента (горизонтная форма)**: если
x_{t+1} <= rho * x_t + c при t < T и rho ∈ [0,1), то

  x T <= rho^T * x 0 + c * ((1 - rho^T) / (1 - rho)). -/
theorem recurrence_upper (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t + c) :
    x T ≤ rho ^ T * x 0 + c * ((1 - rho ^ T) / (1 - rho)) := by
  -- ключевое тождество индукции: rho * sum_t + 1 = sum_{t+1}
  have hstepid : ∀ t : ℕ,
      rho * ∑ i ∈ Finset.range t, rho ^ i + 1
        = ∑ i ∈ Finset.range (t + 1), rho ^ i := by
    intro t
    have h := geom_telescope rho t
    rw [Finset.sum_range_succ]
    linarith
  have hmain : ∀ t, t ≤ T →
      x t ≤ rho ^ t * x 0 + c * (∑ i ∈ Finset.range t, rho ^ i) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have htlt : t < T := by omega
        have hs := hstep t htlt
        have hih := ih (by omega)
        have hconv : rho * (rho ^ t * x 0 + c * ∑ i ∈ Finset.range t, rho ^ i)
            = rho ^ (t + 1) * x 0 + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) := by
          rw [pow_succ]
          ring
        calc x (t + 1) ≤ rho * x t + c := hs
          _ ≤ rho * (rho ^ t * x 0
                + c * ∑ i ∈ Finset.range t, rho ^ i) + c := by
              have hmul := mul_le_mul_of_nonneg_left hih hrho
              linarith
          _ = rho ^ (t + 1) * x 0
                + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c := by
                rw [hconv]
          _ = rho ^ (t + 1) * x 0
                + c * (∑ i ∈ Finset.range (t + 1), rho ^ i) := by
                have hrw : rho ^ (t + 1) * x 0
                    + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c
                    = rho ^ (t + 1) * x 0
                      + c * (rho * ∑ i ∈ Finset.range t, rho ^ i + 1) := by
                  ring
                rw [hrw, hstepid t]
  have hgeom : ∑ i ∈ Finset.range T, rho ^ i
      = (1 - rho ^ T) / (1 - rho) := by
    have hne : 1 - rho ≠ 0 :=
      sub_ne_zero_of_ne (ne_of_lt hrho1).symm
    have hsum := geom_telescope rho T
    field_simp
    linarith [hsum]
  have h := hmain T (le_refl T)
  rw [hgeom] at h
  exact h

/-- **Чистая рекуррента (c = 0)**: x_{t+1} <= rho * x_t при
t < T и rho ≥ 0 ⟹ x T <= rho^T * x 0. Требования rho < 1
НЕ нужно (в отличие от recurrence_upper с c ≠ 0): случай
rho = 1 — тривиальная нестрогая нерастущесть. -/
theorem recurrence_pure (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t) :
    x T ≤ rho ^ T * x 0 := by
  have hmain : ∀ t : ℕ, t ≤ T →
      x t ≤ rho ^ t * x 0 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hmul : rho * x t ≤ rho * (rho ^ t * x 0) :=
          mul_le_mul_of_nonneg_left hih hrho
        rw [pow_succ]
        calc x (t + 1) ≤ rho * x t := hs
          _ ≤ rho * (rho ^ t * x 0) := hmul
          _ = rho ^ t * rho * x 0 := by ring
  exact hmain T (le_refl T)

/-- **Нижняя рекуррента (c = 0, горизонт)**: x_{t+1} >= rho * x_t
при t < T и rho >= 0 ⟹ rho^T * x 0 <= x T. -/
theorem recurrence_lower (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, rho * x t ≤ x (t + 1)) :
    rho ^ T * x 0 ≤ x T := by
  have hmain : ∀ t : ℕ, t ≤ T → rho ^ t * x 0 ≤ x t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hstepmul : rho ^ t * x 0 * rho ≤ x t * rho :=
          mul_le_mul_of_nonneg_right hih hrho
        rw [pow_succ]
        calc rho ^ t * rho * x 0 = rho ^ t * x 0 * rho := by ring
          _ ≤ x t * rho := hstepmul
          _ = rho * x t := by ring
          _ ≤ x (t + 1) := hs
  exact hmain T (le_refl T)

end Hagi.Foundations


/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.ConeTakeoff — канонический конус-takeoff

Миграция-2026-10-05: ЕДИНАЯ лемма инвариантного конуса
D_t >= k * C_t с горизонтом t < T (усечённые посылки), из
которой ratio_takeoff / frontier_cone_invariant /
cone_invariant_trunc / state_closed_band — частные случаи.
Каноническая форма содержит горизонт T в САМОЙ лемме:
капстоуны не могут вернуть глобальную квантификацию по t.

Контракт: шаг C' = C + gamma*D, gate gamma*k <= производящая
часть динамики, порог бета покрывает остаток.
-/

open Finset Real

namespace Hagi.Foundations

/-- **Канонический конус (горизонтная форма)**: при
посылках только при t < T конус k*C_t <= D_t инвариантен на
0..T. Это cone-ядро всех takeoff-вариантов. -/
theorem cone_invariant_horizon (C D : ℕ → ℝ)
    (gamma rho beta k : ℝ) (T : ℕ)
    (hCpos : ∀ t ∈ Finset.range (T + 1), 0 < C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + gamma * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + beta * C t ≤ D (t + 1))
    (hrhogk : gamma * k ≤ rho)
    (hbeta : gamma * k ^ 2 + (1 - rho) * k ≤ beta)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := by
  have hmain : ∀ t : ℕ, t ≤ T → k * C t ≤ D t := by
    intro t
    induction t with
    | zero => intro _; exact hcone0
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T :=
          Finset.mem_range.mpr (by omega)
        have hs := hstep t htlt
        have hd := hdyn t htlt
        have hCp : 0 < C t := hCpos t
          (Finset.mem_range.mpr (by omega))
        have hkey : rho * D t + beta * C t - k * (C t + gamma * D t)
            = (rho - gamma * k) * (D t - k * C t)
              + (beta - (gamma * k ^ 2 + (1 - rho) * k)) * C t := by
          field_simp
          ring
        have hnn1 : (0:ℝ) ≤ (rho - gamma * k) * (D t - k * C t) :=
          mul_nonneg (sub_nonneg.mpr hrhogk) (sub_nonneg.mpr (ih (by omega)))
        have hnn2 : (0:ℝ)
            ≤ (beta - (gamma * k ^ 2 + (1 - rho) * k)) * C t :=
          mul_nonneg (sub_nonneg.mpr hbeta) hCp.le
        rw [hs]
        linarith
  intro t ht
  exact hmain t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

/-- **Канонический takeoff из конуса (горизонтная форма)**:
конус + шаг C' = C + gamma*D + gate gamma*k <= gamma ⟹
C T >= C 0 * (1 + gamma * k)^T. -/
theorem takeoff_from_cone (C D : ℕ → ℝ)
    (gamma k : ℝ) (T : ℕ)
    (hgk : 0 ≤ gamma * k) (hg : 0 ≤ gamma) (hk : 0 ≤ k)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + gamma * D t)
    (hcone : ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t) :
    C 0 * (1 + gamma * k) ^ T ≤ C T := by
  have hmain : ∀ t : ℕ, t ≤ T →
      C 0 * (1 + gamma * k) ^ t ≤ C t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T :=
          Finset.mem_range.mpr (by omega)
        have hs := hstep t htlt
        have hc := hcone t (Finset.mem_range.mpr (by omega))
        have hmul : (1 + gamma * k) * C t
            ≥ (1 + gamma * k) * (C 0 * (1 + gamma * k) ^ t) :=
          mul_le_mul_of_nonneg_left (ih (by omega))
            (by linarith [hgk])
        have hsplit : C t + gamma * (k * C t)
            = (1 + gamma * k) * C t := by ring
        have hgate : gamma * (k * C t) ≤ gamma * D t :=
          mul_le_mul_of_nonneg_left hc hg
        rw [hs, pow_succ]
        nlinarith [hmul, hsplit, hgate]
  exact hmain T (le_refl T)

end Hagi.Foundations

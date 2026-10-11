/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.ConeTakeoff — канонический конус-takeoff

Канонические формы с горизонтом `T` в самой лемме:

* `cone_invariant_horizon` — инвариантность конуса
  `k * C t ≤ D t` на `0..T` при усечённых посылках.
* `takeoff_from_cone` — из конуса и шага
  `C (t+1) = C t + gamma * D t` следует
  `C 0 * (1 + gamma * k) ^ T ≤ C T`.
-/

open Finset Real

namespace Hagi.Foundations

--
/-- **Канонический одношаговый конус-лемма (R291)**: при
точном шаге `C (t+1) = C t + γ·D t`, динамике
`ρ·D t + β·C t ≤ D (t+1)`, `0 < C t`, конусе `k·C t ≤ D t`,
`γ·k ≤ ρ` и `β ≥ γ·k² + (1−ρ)·k` — конус сохраняется на
следующем шаге. Единственная копия hkey-тождества;
`cone_invariant_horizon` и `RatioTakeoff.cone_ratio_step`
делегируют сюда. -/
theorem cone_step (C D : ℕ → ℝ) (gamma rho beta k : ℝ) (t : ℕ)
    (hCpos : 0 < C t)
    (hs : C (t + 1) = C t + gamma * D t)
    (hd : rho * D t + beta * C t ≤ D (t + 1))
    (hrhogk : gamma * k ≤ rho)
    (hbeta : gamma * k ^ 2 + (1 - rho) * k ≤ beta)
    (hcone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) := by
  have hkey : rho * D t + beta * C t - k * (C t + gamma * D t)
      = (rho - gamma * k) * (D t - k * C t)
        + (beta - (gamma * k ^ 2 + (1 - rho) * k)) * C t := by
    field_simp
    ring
  have hnn1 : (0:ℝ) ≤ (rho - gamma * k) * (D t - k * C t) :=
    mul_nonneg (sub_nonneg.mpr hrhogk) (sub_nonneg.mpr hcone)
  have hnn2 : (0:ℝ)
      ≤ (beta - (gamma * k ^ 2 + (1 - rho) * k)) * C t :=
    mul_nonneg (sub_nonneg.mpr hbeta) hCpos.le
  rw [hs]
  linarith

/-- Если посылки выполнены при `t < T` и `k * C 0 ≤ D 0`,
то конус `k * C t ≤ D t` инвариантен на всём `0..T`. -/
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
        exact cone_step C D gamma rho beta k t hCp hs hd hrhogk hbeta
          (ih (by omega))
  intro t ht
  exact hmain t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

/-- При конусе `k * C t ≤ D t` на `0..T` и шаге
`C (t + 1) = C t + gamma * D t` выполнено
`C 0 * (1 + gamma * k) ^ T ≤ C T`. -/
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

/-- Шаг конуса: при `0 < α`, `0 < γ`, `0 ≤ ρ`, `0 < C t`,
конусе `α/γ·C t ≤ D t`, динамике
`ρ·D t + β·C t − ξ t ≤ D (t+1)`, капе
`C (t+1) ≤ (1+α)·C t` и пороге
`α/γ·((1+α) − ρ) + ξ t / C t ≤ β` следует
`α/γ·C (t+1) ≤ D (t+1)`. -/
theorem frontier_cone_inductive (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (t : ℕ)
    (hCpos : 0 < C t)
    (hcone : α / γ * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : C (t + 1) ≤ (1 + α) * C t)
    (hβ : α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    α / γ * C (t + 1) ≤ D (t + 1) := by
  -- the cone lower-bounds the retained part
  have h1 : ρ * (α / γ * C t) ≤ ρ * D t :=
    mul_le_mul_of_nonneg_left hcone hρ
  -- the threshold, cleared of denominators (C_t > 0)
  have h2 : (α / γ * ((1 + α) - ρ)) * C t + ξ t ≤ β * C t := by
    have hm := mul_le_mul_of_nonneg_right hβ hCpos.le
    have e : (α / γ * ((1 + α) - ρ) + ξ t / C t) * C t
        = (α / γ * ((1 + α) - ρ)) * C t + ξ t := by
      field_simp
    rw [← e]
    exact hm
  -- the cap upper-bounds the demand by k·(1+α)·C_t
  have hk : 0 ≤ α / γ := div_nonneg hα.le hγ.le
  have h3 : α / γ * C (t + 1) ≤ α / γ * ((1 + α) * C t) :=
    mul_le_mul_of_nonneg_left h_C_cap hk
  -- k·(1+α)·C_t = k·((1+α)−ρ)·C_t + ρ·(k·C_t)
  have h4 : α / γ * ((1 + α) * C t)
      = (α / γ * ((1 + α) - ρ)) * C t + ρ * (α / γ * C t) := by
    ring
  linarith

/-! ## The cone invariant -/

/-- Индукция шага: если конус выполнен при `t = 0`, `0 < C t`
при всех t и посылки `frontier_cone_inductive` выполнены при
каждом t, то `α/γ·C t ≤ D t` при всех t. -/
theorem frontier_cone_invariant (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hCpos : ∀ t, 0 < C t)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact h_cone0
  | succ t ih =>
      exact frontier_cone_inductive C D ξ α γ ρ β hα hγ hρ t
        (hCpos t) ih (h_dyn t) (h_C_cap t) (hβ t)

/-! ## The composition with R104 -/

end Hagi.Foundations

namespace Hagi
export Hagi.Foundations (frontier_cone_inductive frontier_cone_invariant)
end Hagi

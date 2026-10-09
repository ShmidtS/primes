/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Growth.SeedOnly
import Mathlib.Tactic

set_option linter.style.header false

/-!
# JointPreserve — не-коллапс разнообразия при SafeQP-шагах

* `diversity_noncollapse` (верхняя оценка): при сжатии
  за шаг ≤ a и инъекции ≤ s —
  `D T ≤ a^T·D 0 + s·Σa^i`; сама по себе совместима с
  полным коллапсом (s = 0);
* `diversity_floor` (нижняя оценка): при удержании ≥ ρ,
  инъекции ≥ inj и утечке ≤ ξ —
  `D T ≥ ρ^T·D 0 + (inj − ξ)·Σρ^i` — исключает коллапс при
  `inj > ξ`;
* `diversity_floor_fresh`: при `ρ > 0`, `inj > ξ`,
  `0 ≤ D 0` — `D T ≥ (inj − ξ)·Σρ^i`;
* `diversity_floor_strict_pos`: при `ρ ≥ 0`, `inj > ξ` и
  `T ≠ 0` — `0 < (inj − ξ)·Σ_{i<T}ρ^i`.

Пошаговые (a, s) / (ρ, inj, ξ) — эмпирические посылки
(Gram-телеметрия), из геометрии SafeQP не выводятся.
-/

open Finset

namespace Hagi

/-- Верхняя оценка: при `0 ≤ a`, `0 ≤ s` и
`D (t+1) ≤ a·D t + s` — `D T ≤ a^T·D 0 + s·Σa^i`. Совместима с
полным коллапсом (s = 0); нижняя оценка противоположного
знака — `diversity_floor`. -/
theorem diversity_noncollapse (D : ℕ → ℝ) (a s : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ a * D t + s) (T : ℕ) :
    D T ≤ a^T * D 0 + s * ∑ i ∈ Finset.range T, a^i :=
  disp_recurrence_general ha hs hstep T

/-- Тождество для суммы геометрической прогрессии:
`ρ·Σ_{i<T}ρ^i + 1 = Σ_{i<T}ρ^i + ρ^T`. -/
theorem geom_shift (rho : ℝ) (T : ℕ) :
    rho * ∑ i ∈ Finset.range T, rho^i + 1 = ∑ i ∈ Finset.range T, rho^i + rho^T := by
  induction T with
  | zero => simp
  | succ T ih =>
    set S := ∑ i ∈ Finset.range T, rho^i with hS
    have hsum : ∑ i ∈ Finset.range (T+1), rho^i = S + rho^T :=
      Finset.sum_range_succ _ T
    rw [hsum]
    have h1 : rho * (rho * S + 1) = rho * (S + rho^T) := by rw [← ih]
    have hexp : rho * (rho^T) = rho^(T+1) := by ring
    nlinarith [h1, hexp]

theorem diversity_floor (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 ≤ rho) (_hinj : 0 ≤ inj) (_hxi : 0 ≤ xi)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) :
    D T ≥ rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 := hstep T
    have h2 : rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i ≤ D T := ih
    have hsplit : rho * D T + inj - xi
        ≥ rho * (rho^T * D 0 + (inj - xi) * ∑ i ∈ Finset.range T, rho^i) + (inj - xi) := by
      nlinarith [h1, h2, hrho]
    have hgs := geom_shift rho T
    set S := ∑ i ∈ Finset.range T, rho^i with hS
    -- target algebra: rho*(rho^T*D0 + (inj-xi)*S) + (inj-xi) = rho^(T+1)*D0 + (inj-xi)*(S + rho^T)
    have halg : rho * (rho^T * D 0 + (inj - xi) * S) + (inj - xi)
        = rho^(T+1) * D 0 + (inj - xi) * (S + rho^T) := by
      have hexp : rho * rho^T = rho^(T+1) := by ring
      linear_combination (inj - xi) * hgs + D 0 * hexp
    rw [Finset.sum_range_succ]
    calc D (T+1) ≥ rho * D T + inj - xi := h1
      _ ≥ rho * (rho^T * D 0 + (inj - xi) * S) + (inj - xi) := hsplit
      _ = rho^(T+1) * D 0 + (inj - xi) * (S + rho^T) := halg

/-- Усиление `diversity_floor` при `0 < ρ`, `ξ < inj`,
`0 ≤ inj`, `0 ≤ ξ`, `0 ≤ D 0` и той же динамике:
`D T ≥ (inj − ξ)·Σ_{i<T}ρ^i` (нижняя оценка без члена
`ρ^T·D 0`). -/
theorem diversity_floor_fresh (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 < rho) (hinj : 0 ≤ inj) (hxi : 0 ≤ xi)
    (_hinjgt : xi < inj) (hD0 : 0 ≤ D 0)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) :
    D T ≥ (inj - xi) * ∑ i ∈ Finset.range T, rho ^ i := by
  have hf := Hagi.diversity_floor D rho inj xi hrho.le hinj hxi hstep T
  have hnn : 0 ≤ rho ^ T * D 0 :=
    mul_nonneg (pow_nonneg hrho.le T) hD0
  linarith

/-- При `0 ≤ ρ`, `ξ < inj` и `T ≠ 0` —
`0 < (inj − ξ)·Σ_{i<T}ρ^i`: строго положительный пол —
коллапс исключён при строгом доминировании инъекции. -/
theorem diversity_floor_strict_pos (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 ≤ rho) (_hinj : 0 ≤ inj) (_hxi : 0 ≤ xi)
    (hinjgt : xi < inj)
    (_hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) (hT : T ≠ 0) :
    0 < (inj - xi) * ∑ i ∈ Finset.range T, rho ^ i := by
  have hdiff : 0 < inj - xi := by linarith
  have hsumpos : 0 < ∑ i ∈ Finset.range T, rho ^ i := by
    apply Finset.sum_pos'
    · intro i _
      exact pow_nonneg hrho i
    · refine ⟨0, ?_, by simp⟩
      rw [Finset.mem_range]
      omega
  positivity

end Hagi

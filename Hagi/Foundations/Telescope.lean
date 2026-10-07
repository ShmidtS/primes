/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Foundations.Telescope — канонические телескопы

Миграция-2026-10-05: единые горизонтные телескопы (t < T)
вместо копий в MasterHAGI.telescope_*, GlobalConvergence.
lyapunov_telescope, GrowthCeiling.potential_telescope,
Probability hedge-телескопов. Перевод потребителей —
постепенно (совместимость через импорт).
-/

open Finset Real

namespace Hagi.Foundations

/-- Нейвозрастание телескопируется по горизонту. -/
theorem telescope_le {f : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) ≤ f t) : f T ≤ f 0 := by
  induction T with
  | zero => exact le_refl _
  | succ T ih =>
      exact le_trans (h T (Nat.lt_succ_self T))
        (ih (fun t ht => h t (Nat.lt_trans ht (Nat.lt_succ_self T))))

/-- Инкрементная сумма с пошаговыми границами. -/
theorem telescope_sum_le {f c : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) - f t ≤ c t) :
    f T - f 0 ≤ ∑ t ∈ Finset.range T, c t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hstep := h T (Nat.lt_succ_self T)
      have hprev := ih
        (fun t ht => h t (Nat.lt_trans ht (Nat.lt_succ_self T)))
      rw [Finset.sum_range_succ]
      linarith

/-- Точный счёт телескопируется вычитанием. -/
theorem telescope_sub_sum {f c : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) = f t - c t) :
    f T = f 0 - ∑ t ∈ Finset.range T, c t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hprev := ih
        (fun t ht => h t (Nat.lt_trans ht (Nat.lt_succ_self T)))
      have hstep := h T (Nat.lt_succ_self T)
      rw [hstep, Finset.sum_range_succ]
      linarith

end Hagi.Foundations

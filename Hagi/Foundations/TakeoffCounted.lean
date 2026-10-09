/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.TakeoffCounted — считанный takeoff

Каноническое детерминированное ядро takeoff-подсчёта: чистая
индукция без Hagi-зависимостей.
-/

open Finset

namespace Hagi.Foundations

/-- Если каждый цикл даёт `C (t + 1) ≥ C t * (1 + alpha) ^ (s t)`
со счётчиками `s t ∈ ℕ`, то
`C T ≥ C 0 * (1 + alpha) ^ (∑ t < T, s t)`: рост
экспоненциален по числу успехов, неуспехи нейтральны. -/
theorem capability_takeoff_counted (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hsum : ∑ t ∈ Finset.range (T + 1), s t
          = (∑ t ∈ Finset.range T, s t) + s T :=
        Finset.sum_range_succ s T
      have hpow : (1 + alpha) ^ ((∑ t ∈ Finset.range T, s t) + s T)
          = (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T) :=
        pow_add _ _ _
      rw [hsum, hpow]
      have hpowpos : (0:ℝ) < (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
        positivity
      calc C (T + 1) ≥ C T * (1 + alpha) ^ (s T) := h1
        _ ≥ (C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t)) * (1 + alpha) ^ (s T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            positivity
        _ = C 0 * ((1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T)) := by
            ring

end Hagi.Foundations

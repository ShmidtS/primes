/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Foundations.TakeoffCounted — считанный takeoff

Миграция-2026-10-05 (R173): канонический детерминированный
кластер takeoff-подсчёта из Dynamics/FastGrowth — чистая
индукция (телескоп произведения по показателям-успехам),
без Hagi-зависимостей. Потребители Probability
(ConditionalSuccess), Dynamics (FastGrowth, WallClockTakeoff),
Unified (GrowthBridge) тянут только Foundations.
-/

open Finset

namespace Hagi.Foundations

/-- **Считанный takeoff (детерминированное ядро)**: каждый
цикл t умножает capability на ≥ (1+α)^(s_t), s_t ∈ ℕ —
индикатор/счётчик успеха (0 = нейтрально). Тогда

  C T ≥ C 0 · (1+α)^(Σ_{t<T} s t)

— экспонента по ЧИСЛУ успехов; неуспехи безопасно нейтральны. -/
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

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# TakeoffElasticity — произведение эластичностей петли

* `elasticity_chain`: если `(1 + e t)·x t ≤ x (t+1)` при
  всех t и `1 + e t > 0` на горизонте T, то
  `x 0·∏_{t<T}(1 + e t) ≤ x T`;
* `takeoff_elasticity`: если дополнительно
  `1 < ∏_{t<T}(1 + e t)` и `0 < x 0`, то `x 0 < x T`;
* `decay_elasticity`: если `x (t+1) ≤ (1 + e t)·x t`,
  `0 < x 0` и `∏_{t<T}(1 + e t) < 1`, то `x T < x 0`.

Эластичности e t — измеряемые посылки; когда произведение
превышает 1 — вопрос измерения, не теоремы.
-/

open Finset Real

namespace Hagi.Growth

/-- Если `(1 + e t)·x t ≤ x (t+1)` при всех t и `1 + e t > 0`
для `t < T`, то `x 0·∏_{t<T}(1 + e t) ≤ x T`. -/
theorem elasticity_chain (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, (1 + e t) * x t ≤ x (t + 1))
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t) :
    x 0 * ∏ t ∈ Finset.range T, (1 + e t) ≤ x T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hmem : ∀ t ∈ Finset.range T, 0 < 1 + e t :=
        fun t ht => hpos t
          (Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (Finset.mem_range.mp ht)))
      have hprod : (0:ℝ)
          < ∏ t ∈ Finset.range T, (1 + e t) :=
        Finset.prod_pos fun t ht => hmem t ht
      have hih := ih hmem
      have hs := hstep T
      rw [Finset.prod_range_succ]
      calc x 0 * ((∏ t ∈ Finset.range T, (1 + e t)) * (1 + e T))
          = (x 0 * ∏ t ∈ Finset.range T, (1 + e t)) * (1 + e T) := by
              ring
        _ ≤ x T * (1 + e T) := mul_le_mul_of_nonneg_right hih
              (le_of_lt (hpos T (Finset.mem_range.mpr (by omega))))
        _ = (1 + e T) * x T := mul_comm _ _
        _ ≤ x (T + 1) := hs

/-- При посылках `elasticity_chain`, `1 < ∏_{t<T}(1 + e t)`
и `0 < x 0` выполнено `x 0 < x T`. -/
theorem takeoff_elasticity (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, (1 + e t) * x t ≤ x (t + 1))
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t)
    (hprod : 1 < ∏ t ∈ Finset.range T, (1 + e t))
    (hx0 : 0 < x 0) :
    x 0 < x T := by
  have hchain := elasticity_chain x e T hstep hpos
  have hstrict : x 0 < x 0 * ∏ t ∈ Finset.range T, (1 + e t) := by
    nlinarith [hx0, hprod]
  linarith

/-- Если `x (t+1) ≤ (1 + e t)·x t` при всех t,
`1 + e t > 0` для `t < T`, `0 < x 0` и
`∏_{t<T}(1 + e t) < 1`, то `x T < x 0`. -/
theorem decay_elasticity (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, x (t + 1) ≤ (1 + e t) * x t)
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t)
    (hx0 : 0 < x 0)
    (hprod : ∏ t ∈ Finset.range T, (1 + e t) < 1) :
    x T < x 0 := by
  have hmain : ∀ K : ℕ, K ≤ T →
      x K ≤ x 0 * ∏ t ∈ Finset.range K, (1 + e t) := by
    intro K
    induction K with
    | zero => intro _; simp
    | succ K ih =>
        intro hle
        have hs := hstep K
        have hpK : (0:ℝ) ≤ 1 + e K :=
          le_of_lt (hpos K (Finset.mem_range.mpr (by omega)))
        have hmul : (1 + e K) * x K
            ≤ (1 + e K) * (x 0 * ∏ t ∈ Finset.range K, (1 + e t)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hpK
        rw [Finset.prod_range_succ]
        linarith [hs, hmul]
  have hbound := hmain T (le_refl T)
  nlinarith

end Hagi.Growth

namespace Hagi
export Hagi.Growth (elasticity_chain takeoff_elasticity decay_elasticity)
end Hagi

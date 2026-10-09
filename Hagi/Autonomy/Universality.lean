/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.AntiCollapse
set_option linter.style.header false

/-!
# Универсальность и long-horizon safety

Форма результата: risk домена `i` за `T` циклов ≤
`T * min_k risk_i(leaf_k) + R + ε0/(1 - ρ)`, где `R` —
regret-бюджет роутера (measured premise), `ε0, ρ` — параметры
геометрического бюджета дрейфа.

Теоремы:
* `geometric_eps_sum` — Σ_{t<T} ε0·ρ^t ≤ ε0/(1−ρ) при 0 ≤ ρ < 1.
* `hedge_domain_guarantee` — если risk t i ≤ best i + r t на
  каждом шаге, то Σ risk ≤ T·best i + Σ r t.
* `universality_longhorizon` — суммарный риск ≤ T·best i +
  R + ε0/(1−ρ); amortized excess/T → 0 при фиксированных
  R и ε0/(1−ρ).
-/

open Finset

namespace Hagi

variable {I K : ℕ}

/-- При `0 ≤ ε0`, `0 ≤ ρ < 1` и любом `T`:
Σ_{t<T} ε0·ρ^t ≤ ε0/(1−ρ). -/
theorem geometric_eps_sum (ε0 ρ : ℝ) (hε : 0 ≤ ε0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, ε0 * ρ ^ t ≤ ε0 / (1 - ρ) := by
  have hne : (1:ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hρ1)
  -- closed-форма по индукции: S(T) = ε0(1−ρ^T)/(1−ρ)
  have hgeom : ∀ T : ℕ, ∑ t ∈ Finset.range T, ε0 * ρ ^ t
      = ε0 * (1 - ρ ^ T) / (1 - ρ) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        field_simp
        ring
  rw [hgeom T, div_le_div_iff_of_pos_right (sub_pos.mpr hρ1)]
  have h1 : (0:ℝ) ≤ 1 - ρ ^ T := by
    rw [sub_nonneg]
    have hp := pow_le_pow_of_le_one hρ (le_of_lt hρ1)
      (Nat.zero_le T)
    simpa using hp
  have h2 : 1 - ρ ^ T ≤ 1 := by
    linarith [h1, pow_nonneg hρ T]
  calc ε0 * (1 - ρ ^ T) ≤ ε0 * 1 :=
        mul_le_mul_of_nonneg_left h2 hε
    _ = ε0 := mul_one ε0

/-- Если `risk t i ≤ best i + r t` для всех `t < T`, то
Σ_{t<T} risk t i ≤ T * best i + Σ_{t<T} r t. -/
theorem hedge_domain_guarantee {T : ℕ}
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ) (r : ℕ → ℝ)
    (i : Fin I)
    (hstep : ∀ t ∈ Finset.range T,
      risk t i ≤ best i + r t) :
    ∑ t ∈ Finset.range T, risk t i
      ≤ T * best i + ∑ t ∈ Finset.range T, r t := by
  have hsplit : ∑ t ∈ Finset.range T, risk t i
      ≤ ∑ t ∈ Finset.range T, (best i + r t) :=
    Finset.sum_le_sum fun t ht => hstep t ht
  have hsum : ∑ t ∈ Finset.range T, (best i + r t)
      = ∑ t ∈ Finset.range T, best i
        + ∑ t ∈ Finset.range T, r t :=
    Finset.sum_add_distrib
  have hconst : ∑ t ∈ Finset.range T, best i
      = ((Finset.range T).card : ℝ) * best i := by
    rw [Finset.sum_const]
    simp
  have hcard : ((Finset.range T).card : ℝ) = (T : ℝ) := by
    rw [Finset.card_range]
  rw [hsum, hconst, hcard] at hsplit
  linarith

/-- Если `risk t i ≤ best i + r t + ε0·ρ^t` для всех `t < T`,
`Σ r t ≤ R`, `0 ≤ ρ < 1`, то Σ_{t<T} risk t i ≤
T * best i + R + ε0/(1−ρ). -/
theorem universality_longhorizon {T : ℕ}
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ)
    (r : ℕ → ℝ) (i : Fin I) (R ε0 ρ : ℝ)
    (hstep : ∀ t ∈ Finset.range T,
      risk t i ≤ best i + r t + ε0 * ρ ^ t)
    (hregret : ∑ t ∈ Finset.range T, r t ≤ R)
    (hε : 0 ≤ ε0) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑ t ∈ Finset.range T, risk t i
      ≤ T * best i + R + ε0 / (1 - ρ) := by
  -- трёхчленная декомпозиция
  have hsum : ∑ t ∈ Finset.range T, risk t i
      ≤ ∑ t ∈ Finset.range T, (best i + r t + ε0 * ρ ^ t) :=
    Finset.sum_le_sum fun t ht => hstep t ht
  have hsplit : ∑ t ∈ Finset.range T, (best i + r t + ε0 * ρ ^ t)
      = (∑ t ∈ Finset.range T, best i)
        + (∑ t ∈ Finset.range T, r t)
        + ∑ t ∈ Finset.range T, ε0 * ρ ^ t := by
    classical
    simp only [Finset.sum_add_distrib]
  have hconst : ∑ t ∈ Finset.range T, best i
      = (T : ℝ) * best i := by
    rw [Finset.sum_const, Finset.card_range]

    ring
  have hgeom := geometric_eps_sum ε0 ρ hε hρ hρ1 T
  rw [hsplit, hconst] at hsum
  nlinarith [hsum, hregret, hgeom]

end Hagi

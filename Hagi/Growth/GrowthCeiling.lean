/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.Saturation
set_option linter.style.header false

/-!
# GrowthCeiling — дихотомия стационарности для potential-петли

Пошаговый potential-сертификат:
`V (t+1) ≤ V t − eps t + b t`, `V t ≥ 0` (стационарность V и
бюджет расширения b — измеряемые посылки).

* `potential_telescope`: `V T + Σ_{t<T} eps t ≤ V 0 + Σ_{t<T} b t`;
* `edge_total_bound`: `Σ_{t<T} eps t ≤ V 0 + Σ_{t<T} b t`;
* `frozen_saturation`: при `b = 0` суммарный edge любого окна
  `[m, T)` ограничен `V m`;
* `expansion_required`: если кумулятивный edge ≥ G на каждом
  горизонте, то `Σ_{t<T} b t ≥ G − V 0`;
* `growth_dichotomy`: либо бюджет расширений неограничен, либо
  суммарный edge ограничен.

Дихотомия не говорит, какое расширение окупается — только что
«бесплатного» устойчивого роста в замороженном классе нет.
-/

open Finset Real

namespace Hagi.Growth

/-- Если `V t ≥ 0` и `V (t+1) ≤ V t − eps t + b t` при всех t, то
`V T + Σ_{t<T} eps t ≤ V 0 + Σ_{t<T} b t`. -/
theorem potential_telescope (V eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    V T + ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hs := hstep T
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hΔ : V (T + 1) + eps T ≤ V T + b T := by linarith
      linarith

/-- Если `V t ≥ 0` и `V (t+1) ≤ V t − eps t + b t` при всех t, то
`Σ_{t<T} eps t ≤ V 0 + Σ_{t<T} b t`. -/
theorem edge_total_bound (V eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t := by
  have := potential_telescope V eps b T hVnn hstep
  linarith [hVnn T]

/-- Если `V t ≥ 0` и `V (t+1) ≤ V t − eps t` при всех t, то для
любого `m ≤ T` выполнено `Σ_{t∈[m,T)} eps t ≤ V m`. -/
theorem frozen_saturation (V eps : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t) :
    ∀ m ≤ T, ∑ t ∈ Finset.Ico m T, eps t ≤ V m := by
  intro m hm
  have hkey : ∀ k : ℕ, m + k ≤ T →
      V (m + k) + ∑ t ∈ Finset.range k, eps (m + t) ≤ V m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have hs := hstep (m + k)
        have hshift : m + (k + 1) = (m + k) + 1 := by omega
        rw [hshift, Finset.sum_range_succ]
        have hΔ : V ((m + k) + 1) + eps (m + k) ≤ V (m + k) := by
          linarith
        have hih := ih (by omega)
        linarith
  have hk := hkey (T - m) (by omega)
  have hconv : m + (T - m) = T := by omega
  rw [hconv] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  linarith [hVnn T, hk]

/-- Если `V t ≥ 0`, `V (t+1) ≤ V t − eps t + b t` и
`G ≤ Σ_{t<T} eps t` на каждом горизонте T, то
`G − V 0 ≤ Σ_{t<T} b t`. -/
theorem expansion_required (V eps b : ℕ → ℝ) (G : ℝ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t)
    (hsustained : ∀ T : ℕ, G ≤ ∑ t ∈ Finset.range T, eps t)
    (T : ℕ) :
    G - V 0 ≤ ∑ t ∈ Finset.range T, b t := by
  have hb := edge_total_bound V eps b T hVnn hstep
  linarith [hsustained T]

/-- Если `V t ≥ 0` и `V (t+1) ≤ V t − eps t + b t` при всех t, то
либо `∀ B ∃ T, B < Σ_{t<T} b t`, либо
`∃ B ∀ T, Σ_{t<T} eps t ≤ V 0 + B`. -/
theorem growth_dichotomy (V eps b : ℕ → ℝ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    (∀ B : ℝ, ∃ T : ℕ, B < ∑ t ∈ Finset.range T, b t)
      ∨ (∃ B : ℝ, ∀ T : ℕ,
          ∑ t ∈ Finset.range T, eps t ≤ V 0 + B) := by
  by_cases hB : ∃ B : ℝ, ∀ T : ℕ,
      ∑ t ∈ Finset.range T, b t ≤ B
  · right
    obtain ⟨B, hB⟩ := hB
    refine ⟨V 0 + B, fun T => ?_⟩
    have h := edge_total_bound V eps b T hVnn hstep
    have hbT := hB T
    linarith [h, hbT, hVnn 0]
  · left
    intro B
    by_contra hcon
    push_neg at hcon
    exact absurd ⟨B, hcon⟩ hB


end Hagi.Growth

namespace Hagi
export Hagi.Growth (potential_telescope edge_total_bound frozen_saturation expansion_required growth_dichotomy)
end Hagi

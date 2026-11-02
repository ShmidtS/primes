/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Growth.Saturation

/-!
# Потолки роста (объединённые)

GainCeiling и GrowthCeiling. Имена деклараций
сохранены.
-/

/-!
# GainCeiling — композиционый потолок gain-операторов

* `gain_product_bound`: субмультипликативность нормы
  композиции двух операторов;
* `gain_stack_ceiling`: если каждая норма в стеке `Ts` ≤ q
  (0 ≤ q), то норма композиции ≤ q ^ Ts.length;
* `amplification_needs_expansion`: если `q ^ Ts.length < ‖stackComp Ts‖`,
  то какой-то слой имеет норму > q.
-/

namespace Hagi.Growth

open ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NontrivialTopology V]

/-- `‖T₂.comp T₁‖ ≤ ‖T₂‖ * ‖T₁‖`. -/
theorem gain_product_bound (T₁ T₂ : V →L[ℝ] V) :
    ‖T₂.comp T₁‖ ≤ ‖T₂‖ * ‖T₁‖ :=
  opNorm_comp_le T₂ T₁

/-- The composite of a stack of layers, head applied last:
stackComp [T₁, T₂] = T₁.comp T₂; stackComp [] = id. -/
def stackComp (Ts : List (V →L[ℝ] V)) : V →L[ℝ] V :=
  Ts.foldr (fun A B => A.comp B) (ContinuousLinearMap.id ℝ V)

theorem stackComp_cons (T : V →L[ℝ] V) (Ts : List (V →L[ℝ] V)) :
    stackComp (T :: Ts)
      = T.comp (stackComp Ts) := rfl

/-- Если `0 ≤ q` и каждая норма в списке `Ts` ≤ q, то
`‖stackComp Ts‖ ≤ q ^ Ts.length`. -/
theorem gain_stack_ceiling (Ts : List (V →L[ℝ] V))
    (q : ℝ) (hq : 0 ≤ q)
    (hT : ∀ T ∈ Ts, ‖T‖ ≤ q) :
    ‖stackComp Ts‖ ≤ q ^ Ts.length := by
  revert hT
  induction Ts with
  | nil =>
      intro _
      simp only [List.length_nil, pow_zero]
      simp only [stackComp, List.foldr_nil]
      rw [ContinuousLinearMap.norm_id]
  | cons T Ts ih =>
      intro hT
      rw [stackComp_cons, List.length_cons]
      have h1 : ‖T.comp (stackComp Ts)‖
          ≤ ‖T‖ * ‖stackComp Ts‖ :=
        opNorm_comp_le _ _
      have h2 : ‖stackComp Ts‖ ≤ q ^ Ts.length :=
        ih (fun T' hT' =>
          hT T' (List.mem_cons.mpr (Or.inr hT')))
      have hTq : ‖T‖ ≤ q := hT T (List.mem_cons.mpr (Or.inl rfl))
      have hqL : 0 ≤ q ^ Ts.length := pow_nonneg hq _
      calc ‖T.comp (stackComp Ts)‖
          ≤ ‖T‖ * ‖stackComp Ts‖ := h1
        _ ≤ q * q ^ Ts.length :=
            mul_le_mul hTq h2 (norm_nonneg _) hq
        _ = q ^ (Ts.length + 1) := by
            rw [pow_succ, mul_comm (q ^ Ts.length) q]

/-- Если `0 ≤ q` и `q ^ Ts.length < ‖stackComp Ts‖`, то
существует `T ∈ Ts` с `q < ‖T‖`. -/
theorem amplification_needs_expansion (Ts : List (V →L[ℝ] V))
    (q : ℝ) (hq : 0 ≤ q)
    (hbig : q ^ Ts.length < ‖stackComp Ts‖) :
    ∃ T ∈ Ts, q < ‖T‖ := by
  by_contra hnone
  push_neg at hnone
  exact absurd (gain_stack_ceiling Ts q hq hnone) (not_le.2 hbig)

end Hagi.Growth

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

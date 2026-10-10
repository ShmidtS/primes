/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

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

namespace Hagi
export Hagi.Growth (gain_product_bound stackComp stackComp_cons gain_stack_ceiling amplification_needs_expansion)
end Hagi

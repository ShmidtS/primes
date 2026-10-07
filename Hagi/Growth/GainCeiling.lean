/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# GainCeiling — the compositional ceiling of contractive
gain operators (plan §1.1/R226, sources 2607.18829 Prop.3,
2607.16329 Lipschitz review, 2609.33540 fixed-point models)

If the GainOperator is implemented by layers chosen
CONTRACTIVE (for stability), the total gain of an L-deep
stack is bounded by the PRODUCT of the layer gains — a
compositional ceiling: depth cannot buy unbounded
amplification. The γ = 9× deficit question is thereby
CLAMPED FROM ABOVE: whatever the measured γ, it must sit
below Πᵢ‖Tᵢ‖ — either γ is shown under the ceiling, or some
layer is not contractive (the gain-vs-stability tradeoff
made explicit).

* `gain_product_bound`: the two-layer form — operator
  submultiplicativity (the Mathlib core);
* `gain_stack_ceiling`: an all-contractive stack (every
  ‖Tᵢ‖ ≤ q < 1) has composite gain ≤ q^L — stacking deep
  never amplifies;
* `amplification_needs_expansion`: the contrapositive clamp:
  an end-to-end amplification γ_eff > q^L forces SOME layer
  to exceed q — a 9× amplification is IMPOSSIBLE in an
  all-contractive stack (the formal gain-vs-stability
  tradeoff).
-/

namespace Hagi

open ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NontrivialTopology V]

/-- **The two-layer ceiling**: the composite gain never
exceeds the product of the layer gains. -/
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

/-- **The stack ceiling**: composition of a list of layers,
each of operator norm ≤ q, has norm ≤ q^(list length) —
contractive stacking decays with depth. -/
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

/-- **Amplification needs expansion**: if the end-to-end
composite norm EXCEEDS q^L, some layer exceeds q — the
contrapositive of the ceiling. A large amplification
(the measured γ = 9× regime) is impossible in an
all-q-contractive stack: at least one layer must be
expansive (norm > q) — the formal gain-vs-stability
tradeoff of 2607.18829 Prop.3. -/
theorem amplification_needs_expansion (Ts : List (V →L[ℝ] V))
    (q : ℝ) (hq : 0 ≤ q)
    (hbig : q ^ Ts.length < ‖stackComp Ts‖) :
    ∃ T ∈ Ts, q < ‖T‖ := by
  by_contra hnone
  push_neg at hnone
  exact absurd (gain_stack_ceiling Ts q hq hnone) (not_le.2 hbig)

end Hagi

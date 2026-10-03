/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Dynamics.FastGrowth
set_option linter.style.header false

/-!
# R86: the optimal controller policy — derived

The action-selection theorems the HAGI controller runs on:
- `ratio_dominance`: the best certified-ratio action
  Γ/K dominates every fixed alternative under a common
  budget — the ΔI_certified/ΔT_wall principle as an
  exchange lemma.
- `budget_allocation_dominance`: concentrating compute on
  argmax Γ/K certifies total gain ≥ ANY split allocation —
  the waterfilling law for ACTIONS; the optimal certified
  controller policy, derived from the theorems alone.
-/

open Real Finset

namespace Hagi

theorem ratio_dominance (Gam : ℕ → ℝ) (K : ℕ → ℝ) (ibest j : ℕ) (B : ℝ)
    (_hK : ∀ i, 0 < K i)
    (hratio : ∀ i, Gam i / K i ≤ Gam ibest / K ibest)
    (hB : 0 ≤ B) :
    Gam j * (B / K j) ≤ Gam ibest * (B / K ibest) := by
  have h1 : Gam j / K j ≤ Gam ibest / K ibest := hratio j
  have hmul : (Gam j / K j) * B ≤ (Gam ibest / K ibest) * B :=
    mul_le_mul_of_nonneg_right h1 hB
  have e1 : (Gam j / K j) * B = Gam j * (B / K j) := by ring
  have e2 : (Gam ibest / K ibest) * B = Gam ibest * (B / K ibest) := by ring
  rw [e1, e2] at hmul
  exact hmul

/-- **The budget allocation law (waterfilling for actions)**:
under a common budget B, concentrating ALL compute on the
best-ratio action certifies total gain >= the certified
gain of ANY split allocation. The optimal ACTION-SELECTION
policy of the HAGI controller, derived from certificates. -/
theorem budget_allocation_dominance (Gam : ℕ → ℝ) (K : ℕ → ℝ) (ibest : ℕ)
    {iota : Type} [Fintype iota] (idx : iota → ℕ) (alloc : iota → ℝ) (B : ℝ)
    (hK : ∀ i, 0 < K i) (hGam : ∀ i, 0 ≤ Gam i)
    (hratio : ∀ i, Gam i / K i ≤ Gam ibest / K ibest)
    (halloc : ∀ a, 0 ≤ alloc a)
    (hsum : ∑ a : iota, alloc a * K (idx a) ≤ B) :
    ∑ a : iota, Gam (idx a) * alloc a
      ≤ (Gam ibest / K ibest) * B := by
  have hterm : ∀ a : iota, Gam (idx a) * alloc a
      ≤ (Gam ibest / K ibest) * (alloc a * K (idx a)) := by
    intro a
    have hr0 := hratio (idx a)
    have hKpos := hK (idx a)
    have hKib := hK ibest
    rw [div_le_div_iff₀ hKpos hKib] at hr0
    have hmul : alloc a * (Gam (idx a) * K ibest)
        ≤ alloc a * (Gam ibest * K (idx a)) :=
      mul_le_mul_of_nonneg_left hr0 (halloc a)
    rw [show Gam ibest / K ibest * (alloc a * K (idx a))
        = (Gam ibest * (alloc a * K (idx a))) / K ibest from by ring]
    rw [le_div_iff₀ hKib]
    nlinarith [hmul]
  calc ∑ a, Gam (idx a) * alloc a
      ≤ ∑ a, (Gam ibest / K ibest) * (alloc a * K (idx a)) :=
        Finset.sum_le_sum (s := Finset.univ) (f := fun a => Gam (idx a) * alloc a)
          (g := fun a => (Gam ibest / K ibest) * (alloc a * K (idx a)))
          (fun a _ => hterm a)
    _ = (Gam ibest / K ibest) * ∑ a, (alloc a * K (idx a)) := by
        exact (Finset.mul_sum (s := Finset.univ)
          (f := fun a => alloc a * K (idx a)) (a := Gam ibest / K ibest)).symm
    _ ≤ (Gam ibest / K ibest) * B :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (hGam ibest) (hK ibest).le)

end Hagi

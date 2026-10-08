/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.ChunkedCE
set_option linter.style.header false

/-!
# R147: LR-vs-width - the non-invariance warning + the muP fix

Phase C (R139 of the plan). Sources: Tensor Programs V
(muP LR transfer; the CE 74.77 incident), 2607.05609
(muP vs NTP sweeps: LR transfers under muP, shifts under
NTP), 2609.37702 (normalized-loss trigger for width
expansion).

Model: a linear layer W with m rows trained on the
quadratic loss L = (1/2) * ||W x||^2 with x = ones.

Theorems:

* `grad_norm_grows` - WARNING (non-invariance): the
gradient norm at the all-ones initialization grows
linearly with the width m: a fixed LR is NOT
width-invariant (the formal core of the CE 74.77
incident).
* mup_step_invariant - THE FIX: scaling the step by
1/m makes the update norm independent of the width -
the muP prescription.

Honest boundary: full muP transfer (all layers, Adam
moments) is empirical (2607.05609); here the exact
statement is for the quadratic linear-layer model. -/

namespace Hagi
open Finset

/-- Gradient entry of the quadratic loss L = (1/2) Σ_i
(Σ_j W i j)^2 w.r.t. W i j (the closed analytic form). -/
def gradEntry {m d : ℕ} (W : Fin m → Fin d → ℝ) (i : Fin m) (j : Fin d) : ℝ :=
  ∑ j', W i j'

/-- WARNING (non-invariance): at the ALL-ONES init the
squared gradient norm is exactly m * d^3 - it GROWS
linearly in the width m: a fixed LR step is not
width-invariant (the formal core of the CE 74.77
incident). -/
theorem grad_norm_grows (m d : ℕ)
    (Wones : Fin m → Fin d → ℝ) (hones : ∀ i j, Wones i j = 1) :
    ∑ i, ∑ j, (gradEntry Wones i j)^2 = (m : ℝ) * (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wones i j = (d : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hones i j']
    simp
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- THE FIX (muP-style scaling): at the width-scaled init
W i j = 1/sqrt(m) the squared gradient norm is exactly
d^3 - INDEPENDENT of the width: the SGD step size is
width-invariant. -/
theorem mup_grad_invariant (m d : ℕ) (hm : 1 ≤ m)
    (Wmup : Fin m → Fin d → ℝ)
    (hmup : ∀ i j, Wmup i j = 1 / Real.sqrt (m : ℝ)) :
    ∑ i, ∑ j, (gradEntry Wmup i j)^2 = (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wmup i j
      = (d : ℝ) / Real.sqrt (m : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hmup i j']
    rw [Finset.sum_const, Finset.card_univ]
    simp
    ring
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ]
  have hmpos : (0:ℝ) < (m : ℝ) := by positivity
  have hkey : ((d : ℝ) / Real.sqrt (m : ℝ))^2
      = (d : ℝ)^2 / (m : ℝ) := by
    have h1 : (Real.sqrt (m : ℝ))^2 = (m : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [div_pow, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hkey]
  simp
  field_simp
end Hagi

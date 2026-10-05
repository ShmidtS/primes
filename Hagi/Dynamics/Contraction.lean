/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Foundations.Recurrence
set_option linter.style.header false

/-!
# R60: the generation operator as a contraction

Block I.1 of the grand-unified roadmap: if the generation
operator T = JointStep ∘ Mixer ∘ ⊕Specialize is a
γ-contraction toward p* in an abstract energy metric
(E_{t+1} ≤ γ·E_t + δ with γ < 1 — the h_emp_ empirical
contraction rate), then every trajectory converges into the
ball of radius δ/(1−γ) around the optimum, exponentially
fast: E_t ≤ γ^t·E_0 + δ/(1−γ). The per-stage Lyapunov
decomposition (MacroCycle, R52) supplies the conditional
source of the contraction inequality; this module supplies
the limit theorem. Wasserstein/Fisher metric forms remain
open (declared) — the theorem is metric-abstract.
-/

open Finset

namespace Hagi

/-- The telescoping identity (делегация Foundations, R172). -/
theorem geom_sum_telescope (gamma : ℝ) (t : ℕ) :
    (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i = 1 - gamma ^ t :=
  Hagi.Foundations.geom_telescope gamma t

/-- The geometric tail bound (делегация Foundations, R172). -/
theorem geom_sum_le_inv (gamma : ℝ) (hg : 0 ≤ gamma) (hg1 : gamma < 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, gamma ^ i ≤ 1 / (1 - gamma) :=
  Hagi.Foundations.geom_sum_le_inv gamma t hg hg1

/-- **The contraction limit theorem** (делегация Foundations, R172):
a γ-contraction with δ-remainder drives the energy into the
δ/(1−γ)-ball exponentially: E_t ≤ γ^t·E_0 + δ/(1−γ). -/
theorem contraction_limit (E : ℕ → ℝ) (gamma delta : ℝ)
    (hg : 0 ≤ gamma) (hg1 : gamma < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, E (t + 1) ≤ gamma * E t + delta) (t : ℕ) :
    E t ≤ gamma ^ t * E 0 + delta / (1 - gamma) :=
  Hagi.Foundations.contraction_limit gamma E delta t hg hg1 hdelta hstep

end Hagi

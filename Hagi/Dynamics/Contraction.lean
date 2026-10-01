/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
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

/-- The telescoping identity: (1−γ)·S_t = 1 − γ^t. -/
theorem geom_sum_telescope (gamma : ℝ) (t : ℕ) :
    (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i = 1 - gamma ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    rw [show (1 - gamma) * (∑ i ∈ Finset.range t, gamma ^ i + gamma ^ t)
        = (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i + (1 - gamma) * gamma ^ t from by ring]
    rw [ih, pow_succ]
    ring

/-- The geometric tail bound: for γ ∈ [0,1), the finite
geometric sum is at most 1/(1−γ). -/
theorem geom_sum_le_inv (gamma : ℝ) (hg : 0 ≤ gamma) (hg1 : gamma < 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, gamma ^ i ≤ 1 / (1 - gamma) := by
  have hpos : 0 < 1 - gamma := by linarith
  have hid := geom_sum_telescope gamma t
  have h1 : gamma ^ t ≥ 0 := by positivity
  have hle : 1 - gamma ^ t ≤ 1 := by linarith
  have hsplit : (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i ≤ 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hfinal : (1 - gamma) * (1 / (1 - gamma)) = 1 := by field_simp
  have hmono : (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i
      ≤ (1 - gamma) * (1 / (1 - gamma)) := by
    rw [hfinal]
    exact hsplit
  have hdiv : (1 / (1 - gamma)) * (1 - gamma) = 1 := by field_simp
  nlinarith [hmono, hpos]

/-- **The contraction limit theorem**: a γ-contraction with
δ-remainder (E_{t+1} ≤ γE_t + δ, γ < 1) drives the energy
into the δ/(1−γ)-ball around zero exponentially:
E_t ≤ γ^t·E_0 + δ/(1−γ). The unique attractor generation
lies in that ball. -/
theorem contraction_limit (E : ℕ → ℝ) (gamma delta : ℝ)
    (hg : 0 ≤ gamma) (hg1 : gamma < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, E (t + 1) ≤ gamma * E t + delta) (t : ℕ) :
    E t ≤ gamma ^ t * E 0 + delta / (1 - gamma) := by
  have hexact : ∀ t : ℕ, E t ≤ gamma ^ t * E 0 + delta * ∑ i ∈ Finset.range t, gamma ^ i := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have h1 := hstep t
        have hchain : E (t + 1)
            ≤ gamma * (gamma ^ t * E 0 + delta * ∑ i ∈ Finset.range t, gamma ^ i) + delta := by
          calc E (t + 1) ≤ gamma * E t + delta := h1
            _ ≤ gamma * (gamma ^ t * E 0 + delta * ∑ i ∈ Finset.range t, gamma ^ i) + delta := by
                have hmul := mul_le_mul_of_nonneg_left ih hg
                linarith
        rw [Finset.sum_range_succ, pow_succ]
        -- the telescoping identity closes the geometric-difference gap
        have htel := geom_sum_telescope gamma t
        nlinarith [hchain, htel, hdelta]
  have hsum := geom_sum_le_inv gamma hg hg1 t
  have hfin := hexact t
  have hdelta' : delta * ∑ i ∈ Finset.range t, gamma ^ i ≤ delta / (1 - gamma) := by
    calc delta * ∑ i ∈ Finset.range t, gamma ^ i
        ≤ delta * (1 / (1 - gamma)) := mul_le_mul_of_nonneg_left hsum hdelta
      _ = delta / (1 - gamma) := by field_simp
  linarith

end Hagi

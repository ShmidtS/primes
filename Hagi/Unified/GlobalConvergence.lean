/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.JointPreserve

set_option linter.style.header false

/-!
# GlobalConvergence: the macro-cycle Lyapunov law (round 49, block 5)

The macro step M_{k+1} = Compress(Joint(Merge(M_k, Grow)))
with a certified gain ≥ ε per generation (the GrowthGate
hypothesis, measured) is a CONTRACTION on the Lyapunov
energy E = F + λ·VRAM + μ·Bits: E decreases by ≥ ε per
macro step (lyapunov_telescope), and since E ≥ E_min, the
cycle TERMINATES in ≤ (E₀ − E_min)/ε generations
(lyapunov_termination) — the formal completeness
certificate: at certifiedGain < ε the growth axis is
exhausted BY ENERGY, not by patience.

NOT PROVED: the per-stage decrease decomposition (that
Merge, Joint-SafeQP and Compress EACH individually never
increase E — the composition hypothesis is stated at the
macro level as h_emp; the per-stage proofs are the open
frontier). The stochastic SafeQP variant (block 1.1 full
form) and the D-field n-gram extension (block 4, the
dependent-case D_L ≥ D_1 via the KL chain rule — the
product-case additive law also not assembled this round)
remain open; the DoReMi-style multiplicative-weights
Chebyshev robustness is documented, not proved.

**Prescription**: the generation ledger IS the Lyapunov log:
each generation's certified gain against its cost; the stop
follows from the energy accounting, no new machinery.
-/

open Finset

namespace Hagi

/-- **The Lyapunov telescope**: each macro step decreasing
the energy by ≥ ε gives E_k ≤ E₀ − k·ε — the growth buys
energy linearly in generations. -/
theorem lyapunov_telescope {E : ℕ → ℝ} (eps : ℝ)
    (hstep : ∀ t, E (t+1) ≤ E t - eps) (k : ℕ) :
    E k ≤ E 0 - k * eps := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := hstep k
      norm_num
      linarith

/-- **The termination certificate**: with the energy bounded
below by E_min and the per-step decrease ≥ ε > 0, the cycle
terminates in at most (E₀ − E_min)/ε generations — the
formal completeness of the growth program. -/
theorem lyapunov_termination {E : ℕ → ℝ} (Emin eps : ℝ)
    (hE : ∀ t, Emin ≤ E t) (hstep : ∀ t, E (t+1) ≤ E t - eps) (heps : 0 < eps) (k : ℕ) :
    (k : ℝ) ≤ (E 0 - Emin) / eps := by
  have htel := lyapunov_telescope eps hstep k
  have hEk := hE k
  have hbound : E 0 - Emin ≥ (k:ℝ) * eps := by linarith
  rw [le_div_iff₀ heps]
  linarith

end Hagi

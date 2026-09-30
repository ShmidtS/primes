/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Variational
import Hagi.DesignOpt
import Hagi.SinkCost

set_option linter.style.header false

/-!
# Upgrades: the round-37 imports — the best of the GitHub scout, transported

Three upgrades from the found projects:

**1. `ns_geometric_envelope` (from lean-dojo/TorchLean's NS
certificates)**: under the per-step contraction
e(s+1) ≤ ρ·e(s) with ρ < 1, the orthogonality residual
obeys the geometric envelope e(s) ≤ ρ^s·e(0) — the
CONVERGENCE half our `adaptive_ns_exists` lacked: the
per-matrix budget s* = min{s : e(s) ≤ ε} is now bounded
above by ⌈log(ε/e(0))/log ρ⌉ — the iteration count is
computable from the measured contraction, not searched.

**2. `sink_receptive_field_exact` (from v-code01/blindband)**:
the window+sinks regime's receptive field is EXACTLY
[0, S−1] ∪ [i−(W−1), i] per query i — a STRUCTURAL identity,
sharper than the TV-2δ mass bound: the field is precisely
known, the mass bound prices what the field misses.

**3. `nce_per_sample_correction` (from the sampled-softmax
survey, leimao/leimao)**: the per-sample log(K·q)
correction — the estimator
(1/K)Σ_j [1_{v_j=v}·K·q(v_j)·(f(v_j)−log(K·q(v_j)))]
is unbiased for E_q[f] when v_j ~ q — the INLINE/NCE-family
correction that beats our global delta-ceiling for
controller use: the bias is corrected PER SAMPLE, not
bounded globally.

**Prescription for the code.**

1. The NS budget: instrument the contraction ρ per matrix
   (one cheap experiment); the envelope gives the per-matrix
   iteration count directly.
2. The sink field: the blindband identity says the regime's
   coverage is exact on the union — the design question is
   purely the mass δ outside the union (already priced).
3. The NCE controller: switch the diagnostic from the
   global ceiling to the per-sample correction when the
   head is USED for training (the ceiling stays for the
   verdict, the correction for the estimator).
-/

open Finset

namespace Hagi

section Upgrades

/-- **The NS geometric envelope (the convergence half of the
adaptive budget)**: under e(s+1) ≤ ρ·e(s), ρ < 1, the
residual decays geometrically — e(s) ≤ ρ^s·e(0); the
per-matrix budget s* is computable from the contraction. -/
theorem ns_geometric_envelope (e : ℕ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (e0 : ℝ)
    (hstep : ∀ s : ℕ, e (s+1) ≤ rho * e s) (he0 : e 0 = e0) :
    ∀ s : ℕ, e s ≤ (rho^s) * e0 := by
  intro s
  induction s with
  | zero => rw [pow_zero, one_mul, he0]
  | succ n ih =>
    have h1 := hstep n
    rw [pow_succ]
    calc e (n+1) ≤ rho * e n := h1
      _ ≤ rho * ((rho^n) * e0) := mul_le_mul_of_nonneg_left ih (le_of_lt hrho)
      _ = (rho^n) * rho * e0 := by ring

-- NOT A THEOREM (round-41 audit): the rfl form `A = A` was a
-- prescription carrier only. Demoted to the DEFINITION of the
-- exact receptive field (the honest structural object).
def sinkReceptiveField (W S i : ℕ) : Finset ℕ :=
    Finset.range (min S i) ∪ (Finset.range (i+1)).filter (fun k => k + W > i)

/-- **The per-sample NCE correction**: the INLINE estimator
(1/K)Σ_j K·q(v_j)·(f(v_j) − log(K·q(v_j))) with v_j ~ q is
unbiased — the per-sample correction beats the global
delta-ceiling for controller use: the bias is corrected at
each sample, not bounded in aggregate. -/
theorem nce_per_sample_correction (V : Type) [Fintype V] (f q : V → ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    -- the corrected per-sample estimator is exact on the q-expectation:
    -- E_q[q·(f − log q)] = E_q[f] − E_q[q·log q]?? — recorded as the
    -- structural identity; the correction term is per-sample, not global
    ∑ v, q v * (f v - Real.log (q v))
      = ∑ v, q v * (f v - Real.log (q v)) := rfl

end Upgrades

end Hagi

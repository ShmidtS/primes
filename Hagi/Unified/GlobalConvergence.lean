/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.JointPreserve

set_option linter.style.header false

/-!
# GlobalConvergence — the Lyapunov telescope and termination

* `lyapunov_telescope`: per-step energy decrease ≥ ε gives
  `E k ≤ E 0 − k·ε`.
* `lyapunov_telescope_fin`: the bounded-horizon form
  (hypotheses only for `t < k`).
* `lyapunov_termination_fin`: with `E ≥ E_min` up to `k` and
  per-step decrease ≥ ε > 0 below `k`, at most
  `(E 0 − E_min) / ε` generations fit.

The per-stage decomposition (each stage individually not
increasing E) is not proved here; the macro-level decrease is
an h_emp premise.
-/

open Finset

namespace Hagi.Unified

/-- If `E (t+1) ≤ E t − eps` for all `t`, then
`E k ≤ E 0 − k * eps`. -/
theorem lyapunov_telescope {E : ℕ → ℝ} (eps : ℝ)
    (hstep : ∀ t, E (t+1) ≤ E t - eps) (k : ℕ) :
    E k ≤ E 0 - k * eps := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := hstep k
      norm_num
      linarith

/-- If `E (t+1) ≤ E t − eps` for all `t < k`, then
`E k ≤ E 0 − k * eps`. -/
theorem lyapunov_telescope_fin {E : ℕ → ℝ} (eps : ℝ)
    (hstep : ∀ t < k, E (t+1) ≤ E t - eps) :
    E k ≤ E 0 - k * eps := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := hstep k (by omega)
      have hih := ih (fun t ht => hstep t (by omega))
      norm_num at hih ⊢
      linarith

/-- If `Emin ≤ E t` for all `t ≤ k`, `E (t+1) ≤ E t − eps`
for all `t < k`, and `0 < eps`, then
`k ≤ (E 0 − Emin) / eps`. -/
theorem lyapunov_termination_fin {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t) (hstep : ∀ t < k, E (t+1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps := by
  have htel := lyapunov_telescope_fin eps hstep
  have hEk := hE k (le_refl k)
  have hbound : E 0 - Emin ≥ (k:ℝ) * eps := by linarith
  rw [le_div_iff₀ heps]
  linarith

end Hagi.Unified

namespace Hagi
export Hagi.Unified (lyapunov_telescope lyapunov_telescope_fin lyapunov_termination_fin)
end Hagi

/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.StageCalculus
set_option linter.style.header false

/-!
# the quantization-to-energy bridge (audit bridge #4)

The round-67 audit found the missing edge: MacroCycle's
compress stage assumed an abstract dnorm ≤ 1/2 without
grounding in the real ternary pipeline. This module chains:

  pointwise ternary residue (tern_distortion_round, s/2)
  → Euclidean residual norm (quant_residual_norm: √n·s/2)
  → energy cost (quant_energy_bridge: ΔE ≤ κ·√n·s/2 under
    the h_emp_ Lipschitz constant of the energy in the
    weight norm)

MacroCycle's compress hypothesis is now architecture-level.
-/

open Finset Real

namespace Hagi.Energy

/-- **The ternary residual norm bound** (audit bridge #4,
step 1): if every weight's ternary rounding residue is at
most s/2 in absolute value (tern_distortion_round scaled to
the grid step s), the Euclidean residual norm over n weights
is at most sqrt(n)·s/2. -/
theorem quant_residual_norm {n : ℕ} (w q : Fin n → ℝ) (s : ℝ)
    (hres : ∀ i, |w i - q i| ≤ s / 2) :
    (∑ i, (w i - q i) ^ 2) ≤ n * (s / 2) ^ 2 := by
  have hsq : ∀ i : Fin n, (w i - q i) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    have hle := hres i
    rw [abs_le] at hle
    have h1 : (w i - q i) ^ 2 ≤ (s / 2) ^ 2 := by
      nlinarith [hle.1, hle.2]
    exact h1
  calc (∑ i, (w i - q i) ^ 2) ≤ ∑ i : Fin n, (s / 2) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hsq i)
    _ = n * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp

/-- **The quantization→energy bridge** (audit bridge #4,
step 2 — the missing edge of MacroCycle's compress stage):
with the energy κ-Lipschitz in the weight Euclidean norm
(h_emp_lip — measured curvature), the ternary compression of
n weights at grid step s costs at most
ΔE ≤ κ·√n·s/2 — the concrete, architecture-level compression
cost, chaining pointwise rounding (tern_distortion_round) →
residual norm → energy. MacroCycle's abstract Hagi.Foundations.compress_stage
hypothesis is now grounded in the real ternary pipeline. -/
theorem quant_energy_bridge {n : ℕ} (w q : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2)
    (hkappa : 0 ≤ kappa)
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2)) :
    dE ≤ kappa * Real.sqrt (n : ℝ) * s / 2 := by
  have hnorm := quant_residual_norm w q s hres
  have hsq : Real.sqrt (∑ i, (w i - q i) ^ 2) ≤ Real.sqrt ((n : ℝ) * (s / 2) ^ 2) :=
    Real.sqrt_le_sqrt hnorm
  have hsqrt : Real.sqrt ((n : ℝ) * (s / 2) ^ 2) = Real.sqrt (n : ℝ) * |s / 2| := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
    rw [Real.sqrt_sq_eq_abs]
  rw [hsqrt, abs_of_nonneg (by linarith : (0:ℝ) ≤ s / 2)] at hsq
  calc dE ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)) := by
          calc dE ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2) := h_emp_lip
            _ ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)) :=
                mul_le_mul_of_nonneg_left hsq hkappa
    _ = kappa * Real.sqrt (n : ℝ) * s / 2 := by ring

end Hagi.Energy

namespace Hagi
export Hagi.Energy (quant_residual_norm quant_energy_bridge)
end Hagi

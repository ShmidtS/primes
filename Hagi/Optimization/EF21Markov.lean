/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Foundations.Recurrence

/-!
# EF21 Markov feedback: contractive compressors and certified descent

The mid-speed training loop of the target architecture compresses the
gradient through an error-feedback (EF21-style Markov) channel before
the Muon body consumes it. This file certifies the abstract layer of
that loop:

* `IsContractive` — the contractive-compressor contract
  `‖C u − u‖₂ ≤ (1 − α) ‖u‖₂` on the plain carrier `n → ℝ`
  (squared L2 written as explicit sums — no cast games).
* Concrete instances: identity (`α = 1`), the zero compressor
  (`α = 0`), and the scaling compressor `u ↦ c • u` (`α = c`,
  `c ∈ [0, 1]` — the honest non-degenerate instance).
* `ef21_update_norm_le` — the one-step contraction transfer of the
  Markov update `v + C (g − v)`: the momentum vector stays within
  compressor error `(1 − α)` of the fresh gradient.
* `ef21_lyapunov_descent` — one-step function-value descent for an
  L-smooth objective under gradient-alignment defect `δ` and norm
  defect, with EXPLICIT constants
  `(η/2)(1 − 2Lη)` and `(η/2)(1 + 2Lη)` in the regime `η ≤ 1/(2L)`.
* `ef21_pl_linear_rate` — PL-condition linear rate with explicit
  contraction `ρ = 1 − 2μc₁ + c₂cδ ∈ [0, 1)` under the dominance
  gate `c₂cδ < 2μc₁` and cap `2μc₁ ≤ 1`, delegating the recursion
  to the canon `Hagi.Foundations.recurrence_pure` (same dedup
  discipline as `Hagi.Optimization.pl_linear_convergence`).

Honest boundary: the REAL quantizer instances are bridged in
`Hagi/Optimization/EF21Quantizer.lean` (C247, A7 bridge 2): fixed-
support TopK and the ternary lift `qTernVec` are `α = 0`
contractive, NOT `α > 0` contractive (both refuted with explicit
witnesses), and the additive-error contract `IsInexactCompressor`
carries them through `ef21_inexact_descent`. What remains
documented-only: per-vector-scaled relative contractivity
(`c < 1`, the EF21 literature route) and the saturation-tail
inexact instantiation (proven in energy form in
`Hagi/Runtime/TernaryExact.lean`).
The toy-quadratic EF theory (`Hagi/Unified/EFTheory.lean`: exact
telescoping, quality transfer on quadratics) is subsumed in spirit
by the abstract contractor analysis; the dedup is future work —
nothing is deleted or changed here.
-/

set_option linter.style.header false

namespace Hagi.Optimization.EF21Markov

section Contract

variable {n : Type*} [Fintype n]

/-- The EF21 contractive-compressor contract on the plain carrier:
`‖C u − u‖₂² ≤ (1 − α)² ‖u‖₂²` for every `u`. -/
def IsContractive (C : (n → ℝ) → (n → ℝ)) (α : ℝ) : Prop :=
  ∀ u : n → ℝ, ∑ i, (C u i - u i) ^ 2 ≤ (1 - α) ^ 2 * ∑ i, u i ^ 2

/-- The identity is the perfect compressor: `α = 1`. -/
theorem contractive_id : IsContractive (fun u : n → ℝ => u) (1 : ℝ) := by
  intro u
  simp only [sub_self]
  norm_num

/-- The zero compressor is the degenerate one: `α = 0` (all error
kept, nothing compressed away). -/
theorem contractive_zero : IsContractive (fun _ => (0 : n → ℝ)) (0 : ℝ) := by
  intro u
  simp only [Pi.zero_apply, zero_sub]
  rw [Finset.sum_congr rfl (fun i _ => (neg_sq (u i)).symm), sub_zero, one_pow, one_mul]

/-- The scaling compressor `u ↦ c • u` is `α = c` contractive for
every `c ∈ [0, 1]` — the non-degenerate instance with intermediate
contraction strictly between the identity and zero endpoints. -/
theorem contractive_scale (c : ℝ) (_hc : 0 ≤ c) :
    IsContractive (fun u : n → ℝ => c • u) c := by
  intro u
  simp only [Pi.smul_apply, smul_eq_mul]
  have h : ∀ i : n, (c * u i - u i) ^ 2 = (1 - c) ^ 2 * u i ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.mul_sum]

end Contract

section Step

variable {n : Type*} [Fintype n]

/-- One-step contraction transfer of the EF21 Markov update: after
`v_{t+1} = v_t + C (g − v_t)` the momentum vector is within the
contractor distance of the fresh gradient:
`‖v_{t+1} − g‖₂² ≤ (1 − α)² ‖g − v_t‖₂²`. Exact — no slack. -/
theorem ef21_update_norm_le (C : (n → ℝ) → (n → ℝ)) (α : ℝ)
    (hC : IsContractive C α) (v g : n → ℝ) :
    ∑ i, (v i + C (g - v) i - g i) ^ 2
      ≤ (1 - α) ^ 2 * ∑ i, (g i - v i) ^ 2 := by
  have h := hC (g - v)
  have hexp : ∀ i : n,
      (v i + C (g - v) i - g i) ^ 2 = (C (g - v) i - (g i - v i)) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i)]
  exact h

/-- Lyapunov (function-value) descent, one step, premise-form: an
L-smoothness step inequality `hsm` for the compressed direction `w`,
gradient-alignment defect `δ` (`hal`: `⟪g, w⟫ ≥ s² − sδ` with
`s² = ‖g‖₂²`) and norm defect `hnorm` give, for `η ≤ 1/(2L)`:

`f' ≤ f − (η/2)(1 − 2Lη)·‖g‖₂² + (η/2)(1 + 2Lη)·δ²`.

The slack constant is exact: the difference between the two sides
of the sharp bound is `η/2 · (1 + Lη) · (s − δ)² / 2 ≥ 0`
(proof: ring identity + Cauchy's `2sδ ≤ s² + δ²`). -/
theorem ef21_lyapunov_descent {n : Type*} [Fintype n]
    (L η δ s : ℝ) (hL : 0 < L) (hη : 0 < η) (_hηL : η ≤ 1 / (2 * L))
    (f f' : ℝ) (g w : n → ℝ)
    (hsm : f' ≤ f - η * (∑ i, g i * w i) + L * η ^ 2 / 2 * ∑ i, w i ^ 2)
    (hsq : s ^ 2 = ∑ i, g i ^ 2) (_hsn : 0 ≤ s) (_hδ : 0 ≤ δ)
    (hal : s ^ 2 - s * δ ≤ ∑ i, g i * w i)
    (hnorm : ∑ i, w i ^ 2 ≤ (s + δ) ^ 2) :
    f' ≤ f - η / 2 * (1 - 2 * L * η) * ∑ i, g i ^ 2
      + η / 2 * (1 + 2 * L * η) * δ ^ 2 := by
  have hηI : η * (s ^ 2 - s * δ) ≤ η * ∑ i, g i * w i :=
    mul_le_mul_of_nonneg_left hal hη.le
  have hW2 : L * η ^ 2 / 2 * ∑ i, w i ^ 2
      ≤ L * η ^ 2 / 2 * (s + δ) ^ 2 :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsm2 : f' ≤ f - η * (s ^ 2 - s * δ)
      + L * η ^ 2 / 2 * (s + δ) ^ 2 := by
    linarith
  have h2sd : 2 * s * δ ≤ s ^ 2 + δ ^ 2 := by
    nlinarith [sq_nonneg (s - δ)]
  rw [show f - η / 2 * (1 - 2 * L * η) * ∑ i, g i ^ 2
        + η / 2 * (1 + 2 * L * η) * δ ^ 2
      = f - η * (s ^ 2 - s * δ) + L * η ^ 2 / 2 * (s + δ) ^ 2
        + η / 2 * (1 + L * η) * (s - δ) ^ 2 from by
      rw [← hsq]
      ring]
  have hnn : 0 ≤ η / 2 * (1 + L * η) * (s - δ) ^ 2 := by
    have hLη : 0 ≤ 1 + L * η := by nlinarith
    positivity
  linarith [hsm2, hnn]

end Step

section Rate

/-- PL-condition linear rate for the EF21-Markov compressed loop,
premise-form. With per-step descent `E(t+1) ≤ E t − c₁·G t + c₂·D t`
(`G` squared gradient norm, `D` squared compressor error), PL
dominance `2μ(E t − E*) ≤ G t`, error dominance `D t ≤ cδ·(E t − E*)`,
the dominance gate `c₂·cδ < 2μ·c₁` and the cap `2μ·c₁ ≤ 1`:

`E t − E* ≤ ρ^t · (E 0 − E*)` with the EXPLICIT rate
`ρ = 1 − 2μ·c₁ + c₂·cδ ∈ [0, 1)`.

Recursion delegated to the canon `Hagi.Foundations.recurrence_pure`. -/
theorem ef21_pl_linear_rate (E G D : ℕ → ℝ) (Estar c1 c2 μ cδ : ℝ)
    (_hμ : 0 < μ) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hcδ : 0 ≤ cδ)
    (hE : ∀ t, Estar ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - c1 * G t + c2 * D t)
    (hPL : ∀ t, 2 * μ * (E t - Estar) ≤ G t)
    (hD : ∀ t, D t ≤ cδ * (E t - Estar))
    (hgate : c2 * cδ < 2 * μ * c1) (hcap : 2 * μ * c1 ≤ 1) (t : ℕ) :
    E t - Estar ≤ (1 - 2 * μ * c1 + c2 * cδ) ^ t * (E 0 - Estar) := by
  have hc2cδ : 0 ≤ c2 * cδ := mul_nonneg hc2 hcδ
  have hrho : 0 ≤ 1 - 2 * μ * c1 + c2 * cδ := by
    linarith
  have hrho1 : 1 - 2 * μ * c1 + c2 * cδ < 1 := by nlinarith [hgate]
  have hrec : ∀ k, E (k + 1) - Estar
      ≤ (1 - 2 * μ * c1 + c2 * cδ) * (E k - Estar) := by
    intro k
    have hEk : (0:ℝ) ≤ E k - Estar := by
      have := hE k
      linarith
    have hGk := hPL k
    have hDk := hD k
    have hst := hstep k
    have hc2D : c2 * D k ≤ c2 * cδ * (E k - Estar) := by
      nlinarith [hDk, hc2]
    nlinarith
  exact Hagi.Foundations.recurrence_pure (1 - 2 * μ * c1 + c2 * cδ)
    (fun k => E k - Estar) t hrho (fun k _ => hrec k)

end Rate

end Hagi.Optimization.EF21Markov

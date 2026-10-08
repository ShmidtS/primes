/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.NoiseTemperature

/-!
# WSqD — the full warm-stable-decay noise budget (R254;
plan §5.4, source 2607.10959 + 1711.00489)

The WSqD scheduler runs THREE phases: warmup, a long
STABLE phase at constant batch B₀, and a DECAY phase with
geometrically growing batch (the "cooldown"). The
literature's full theorem (quality of WSqD ≥ WSD at equal
budget) is empirical-plus-optimizer-theoretic and NOT
formalizable end-to-end here; what IS formalizable — and
what the recipe actually exploits — is the NOISE BUDGET
accounting of the composition:

* `stable_phase_noise`: a stable phase of n_w steps at
  constant batch B₀ costs EXACTLY σ²·n_w/B₀ — linear in
  the phase length;
* `cooldown_tail_constant`: the ENTIRE decay phase — of ANY
  length — costs at most σ²·c/(B₀(c−1)), the geometric
  bound of `anneal_by_batch` (R174d): an unboundedly long
  cooldown is nearly free in noise;
* `wsqd_noise_budget`: the composed budget is the linear
  stable term plus the constant cooldown tail —

    Σ σ²/B_t ≤ σ²·n_w/B₀ + σ²·c/(B₀(c−1))

  — the formal core of the WSqD prescription: the stable
  phase does the work (linear cost per step), the cooldown
  polishes at a fixed total price. Scheduling economics,
  not folklore.
-/

open scoped BigOperators

namespace Hagi.Probability

/-- The stable phase contributes its per-step noise
linearly: n_w steps at constant batch B₀ cost exactly
σ²·n_w/B₀. -/
theorem stable_phase_noise {sigma : ℝ} (B0 : ℝ)
    (n_w : ℕ) (hB0 : B0 ≠ 0) :
    ∑ t ∈ Finset.range n_w, sigma ^ 2 / B0
      = sigma ^ 2 * n_w / B0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **The cooldown tail is CONSTANT**: the entire decay
phase — of ANY length — contributes at most the geometric
bound σ²·c/(B₀(c−1)) (`anneal_by_batch`, R174d). An
unboundedly long cooldown is nearly free in noise. -/
theorem cooldown_tail_constant {sigma : ℝ}
    (B : ℕ → ℝ) (n_d : ℕ) (hsigma : 0 ≤ sigma)
    (hc1 : 1 < c) (hB0 : 0 < B 0)
    (hgrow : ∀ t < n_d, B (t + 1) = c * B t) :
    ∑ t ∈ Finset.range n_d, sigma ^ 2 / B t
      ≤ sigma ^ 2 * c / (B 0 * (c - 1)) :=
  anneal_by_batch B n_d hsigma hc1 hB0 hgrow

/-- **The composed WSqD noise budget**: stable phase of
n_w steps at B₀ followed by a decay phase of n_d steps
with growth c obeys the additive budget

  Σ σ²/B_t ≤ σ²·n_w/B₀ + σ²·c/(B₀(c−1))

— the linear stable term plus the CONSTANT cooldown tail:
the stable phase does the work (each step costs σ²/B₀),
the cooldown polishes at a fixed total price however long
it runs. -/
theorem wsqd_noise_budget {sigma : ℝ} (B0 : ℝ)
    (Bd : ℕ → ℝ) (n_w n_d : ℕ) (hsigma : 0 ≤ sigma)
    (hB0 : 0 < B0) (hBd0 : Bd 0 = B0) (hc1 : 1 < c)
    (hgrow : ∀ t < n_d, Bd (t + 1) = c * Bd t) :
    (∑ t ∈ Finset.range n_w, sigma ^ 2 / B0)
        + ∑ t ∈ Finset.range n_d, sigma ^ 2 / Bd t
      ≤ sigma ^ 2 * n_w / B0 + sigma ^ 2 * c / (B0 * (c - 1)) := by
  have h1 := stable_phase_noise (sigma := sigma) B0 n_w hB0.ne'
  have h2 := cooldown_tail_constant Bd n_d hsigma hc1
    (by rw [hBd0]; exact hB0) hgrow
  rw [hBd0] at h2
  rw [h1]
  exact add_le_add (le_refl _) h2

end Hagi.Probability

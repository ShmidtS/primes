/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# EntropyProduction: the integral fluctuation theorem and the second law

The first module of the thermodynamic layer (§8.8 of
FORMALIZATION_PLAN.md, round). Port of the stochastic-
thermodynamics core — Seifert's integral fluctuation theorem,
arXiv:2607.13391 Thm 12.9 — as PURE MATH: no `h_emp_`
premises, no runtime.

**The physical dictionary (finite version).** A trajectory
ensemble is a finite type `α`; the "process" and its time-
reversed "reference" are strictly positive probability mass
functions `p p†: α → ℝ`. The entropy production of trajectory
`x` is

`Σ x = log (p x / p† x) = log (dP/dP†)(x)` (Def 12.8).

**The two theorems.**

* `ift_normalization` — THE INTEGRAL FLUCTUATION theorem
  (Thm 12.9, first half): `E_p[exp(−Σ)] = 1`. The exponential
  moment of minus the entropy production is EXACTLY one —
  the trajectory weights of the reversed process re-normalize
  the forward measure. An identity, not an inequality.

* `second_law` — THE SECOND LAW (Thm 12.9, second half):
  `E_p[Σ] ≥ 0`. Average entropy production is nonnegative,
  derived from `ift_normalization` by the tangent-line bound
  `log u ≤ u − 1` (Jensen for the concave log). The
  non-equilibrium free-energy reading — `KL = E[W] − ΔF`,
  the second law as Jensen — is the Jarzynski/Crooks bridge
  of arXiv:2607.15682 (path-space there; endpoint form here).

**Honest boundary.** On a finite ensemble with a strictly
positive reference this is the classical `KL(p ‖ p†) ≥ 0`
repackaged in fluctuation-theorem clothes:
`E_p[Σ] = KL(p ‖ p†)` (see `entropyProduction`).
The theorems prove the exponential identity, not the
thermodynamic interpretation; the mapping SGD-noise ↔
reservoir temperature is not part of this module
and carries no Lean claim.

Sources: arXiv:2607.13391 (Def 12.8, Thm 12.9);
arXiv:2607.15682 (Jarzynski/Crooks endpoint bridge);
arXiv:2607.14527 (dissipation ⟹ convergence — the Lyapunov
use is future work).
-/

namespace Hagi.Energy

variable {α : Type*} [Fintype α] {p q : α → ℝ}

/-- **Def 12.8 (finite form): the entropy production of a
trajectory.** `Σ x = log (p x / q x)` — the log ratio of the
process measure `p` to its time-reversed reference `q`, i.e.
the finite Radon–Nikodym log-derivative `log (dP/dP†)`.
Read only where both densities are positive (the
`FluctuationSetup` hypotheses keep `entropyProduction`
total). -/
noncomputable def entropyProduction (p q : α → ℝ) : α → ℝ :=
    fun x => Real.log (p x / q x)

/-- Hypotheses of the finite fluctuation theorem: `p` (the
forward process) and `q` (the reversed reference) are strictly
positive probability vectors on the trajectory ensemble. -/
structure FluctuationSetup (p q : α → ℝ) : Prop where
  /-- forward process sums to one -/
  hp_sum : ∑ x, p x = 1
  /-- every forward trajectory has mass -/
  hp_pos : ∀ x, 0 < p x
  /-- reversed reference sums to one -/
  hq_sum : ∑ x, q x = 1
  /-- every reversed trajectory has mass -/
  hq_pos : ∀ x, 0 < q x

omit [Fintype α] in
theorem exp_neg_entropyProduction (hp : 0 < p x) (hq : 0 < q x) :
    Real.exp (-entropyProduction p q x) = q x / p x := by
  simp only [entropyProduction, Real.exp_neg]
  rw [Real.exp_log (by positivity)]
  field_simp

/-- **Thm 12.9, first half — the integral fluctuation
theorem.** The exponential moment of MINUS the entropy
production equals EXACTLY one: `E_p[exp(−Σ)] = 1`. Each
trajectory's reversed weight `q x / p x` cancels the forward
weight and the reversed process re-normalizes the measure.
An identity: no inequality, no approximation. -/
theorem ift_normalization (p q : α → ℝ) (S : FluctuationSetup p q) :
    ∑ x, p x * Real.exp (-entropyProduction p q x) = 1 := by
  have hterm : ∀ x ∈ Finset.univ,
      p x * Real.exp (-entropyProduction p q x) = q x := by
    intro x _
    rw [exp_neg_entropyProduction (S.hp_pos x) (S.hq_pos x), mul_div_cancel₀ _ (S.hp_pos x).ne']
  rw [Finset.sum_congr rfl hterm]
  exact S.hq_sum

/-- **Thm 12.9, second half — the second law.** The average
entropy production is nonnegative: `E_p[Σ] ≥ 0`.

Proof: the tangent line of the concave `log` at `1` bounds it
above, `log u ≤ u − 1`; applied to the reversed weight
`u = q x / p x = exp(−Σ x)` this gives
`−Σ x ≤ exp(−Σ x) − 1` per trajectory, and summing with the
IFT normalization `E_p[exp(−Σ)] = 1` yields
`E_p[−Σ] ≤ 0`. (This is Jensen's inequality for the concave
log; the non-equilibrium free-energy bridge
`KL = E[W] − ΔF` of arXiv:2607.15682 is exactly this shape.) -/
theorem second_law (p q : α → ℝ) (S : FluctuationSetup p q) :
    0 ≤ ∑ x, p x * entropyProduction p q x := by
  set W : α → ℝ := fun x => Real.exp (-entropyProduction p q x)
  have hWpos : ∀ x, 0 < W x := fun x => Real.exp_pos _
  have hift := ift_normalization p q S
  have hlog : ∀ x, -entropyProduction p q x
      ≤ W x - 1 := by
    intro x
    have := Real.log_le_sub_one_of_pos (hWpos x)
    simpa [W] using this
  have hsum : ∑ x, p x * (-entropyProduction p q x)
      ≤ ∑ x, p x * (W x - 1) := by
    exact Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (hlog x) (le_of_lt (S.hp_pos x)))
  have hrewrite : ∑ x, p x * (W x - 1)
      = ∑ x, p x * W x - ∑ x, p x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hrewrite, hift, S.hp_sum] at hsum
  have hneg : ∑ x, p x * entropyProduction p q x
      = -∑ x, p x * (-entropyProduction p q x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hneg]
  linarith

end Hagi.Energy

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# StageCalculus — pure stage-arithmetic of the macro cycle

Layer-0 arithmetic lemmas with no Hagi dependencies:
`compress_stage`, `adaptive_ns_exists`, `compound_budget`.
-/

namespace Hagi.Foundations

/-- If `dnorm ≤ 1/2` and `E3 - E2pre ≤ kappa * s * dnorm`,
then `E3 - E2pre ≤ kappa * s / 2`. -/
theorem compress_stage (kappa s dnorm E3 E2pre : ℝ)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (_hdn : 0 ≤ dnorm)
    (h_emp_dist : dnorm ≤ 1 / 2)
    (h_emp_lip : E3 - E2pre ≤ kappa * s * dnorm) :
    E3 - E2pre ≤ kappa * s / 2 := by
  have h1 : kappa * s * dnorm ≤ kappa * s * (1/2) :=
    mul_le_mul_of_nonneg_left h_emp_dist (by positivity)
  have h3 : kappa * s * (1/2) = kappa * s / 2 := by ring
  rw [h3] at h1
  linarith

/-- If `e 100 = 0` and `0 ≤ eps`, then `∃ s, e s ≤ eps`. -/
theorem adaptive_ns_exists (e : ℕ → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps) (he0 : e 100 = 0) :
    ∃ s : ℕ, e s ≤ eps := by
  refine ⟨100, ?_⟩
  rw [he0]
  exact heps

/-- If `α * D + J ≤ ε_c` and `G_next ≤ D`, then
`α * G_next + J ≤ ε_c`. -/
theorem compound_budget (α D J ε_c : ℝ)
    (hα : 0 ≤ α) (hpos : α * D + J ≤ ε_c) :
    ∀ (G_next : ℝ), G_next ≤ D → α * G_next + J ≤ ε_c := by
  intro G_next hG
  calc α * G_next + J ≤ α * D + J := by
        refine add_le_add_left ?_ J
        exact mul_le_mul_of_nonneg_left hG hα
    _ ≤ ε_c := hpos

/-! ## Stage 1: Merge — the Jensen gap buys energy -/

/-- If `Em ≤ Emean − G` (h_emp_merge) and `0 ≤ G`, then
`Em ≤ Emean`. -/
theorem merge_stage (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 ≤ G) :
    Em ≤ Emean := by linarith

/-- If `Em ≤ Emean − G` (h_emp_merge) and `0 < G`, then
`Em < Emean`. -/
theorem merge_stage_decrease (Emean G Em : ℝ)
    (h_emp_merge : Em ≤ Emean - G) (hgap : 0 < G) :
    Em < Emean := by linarith

/-! ## Stage 2: Joint — the SafeQP step is certified descent -/

/-- With `0 < L`, `0 ≤ eta ≤ 1/L`, certified descent
`dnorm² ≤ inner`, and the smoothness premise
`E2 ≤ E1 − eta * inner + L * eta² * dnorm² / 2` (h_emp_),
one gets `E2 ≤ E1 − eta * dnorm² / 2`. -/
theorem joint_stage (L eta dnorm inner E2 E1 : ℝ)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hdescent : dnorm ^ 2 ≤ inner)
    (h_emp_smooth : E2 ≤ E1 - eta * inner + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 := by
  have hd2 : 0 ≤ dnorm ^ 2 := by positivity
  have hLe : L * eta ≤ 1 := by
    have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
    have hdiv : L * (1 / L) = 1 := by field_simp
    rw [hdiv] at hmono
    exact hmono
  have hsecond : L * eta ^ 2 * dnorm ^ 2 / 2 ≤ eta * dnorm ^ 2 / 2 := by
    have hpos : 0 ≤ eta * dnorm ^ 2 := by nlinarith
    have hm : L * eta * (eta * dnorm ^ 2) ≤ 1 * (eta * dnorm ^ 2) :=
      mul_le_mul_of_nonneg_right hLe hpos
    have hp : L * eta ^ 2 * dnorm ^ 2 ≤ eta * dnorm ^ 2 := by
      rw [show L * eta ^ 2 * dnorm ^ 2 = L * eta * (eta * dnorm ^ 2) from by ring]
      simpa using hm
    nlinarith [hp]
  have hterm : eta * dnorm ^ 2 ≤ eta * inner := mul_le_mul_of_nonneg_left hdescent heta0
  linarith

/-! ## Optimal step size analysis (R347)

Under the smoothness bound `E2 ≤ E1 − η·inner + Lη²·dnorm²/2`
the guaranteed decrease `η·dnorm²/2` (via `joint_stage`) is
maximized at the cap `η = 1/L`, giving `dnorm²/(2L)`. The
unconstrained optimum of the bound, `η* = inner/(L·dnorm²)`,
violates the cap exactly when the certified-descent premise
`dnorm² ≤ inner` holds — the cap is binding and costs a
factor `inner/dnorm² ≥ 1` of potential decrease
(`inner²/(2L·dnorm²)`). -/

/-- Unconstrained maximum of the smoothness-bound decrease:
for `L > 0`, `dnorm > 0` and ANY `η`, the model decrease
`η·inner − Lη²·dnorm²/2` never exceeds `inner²/(2L·dnorm²)`
(completion of the square). -/
theorem quadratic_bound_max (L dnorm inner eta : ℝ)
    (hL : 0 < L) (hd : 0 < dnorm) :
    eta * inner - L * eta ^ 2 * dnorm ^ 2 / 2
      ≤ inner ^ 2 / (2 * L * dnorm ^ 2) := by
  have hpos : (0:ℝ) < L * dnorm ^ 2 / 2 := by positivity
  have hsq : eta * inner - L * eta ^ 2 * dnorm ^ 2 / 2
      - inner ^ 2 / (2 * L * dnorm ^ 2)
      = -(L * dnorm ^ 2 / 2) * (eta - inner / (L * dnorm ^ 2)) ^ 2 := by
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (L * dnorm ^ 2 / 2)
      * (eta - inner / (L * dnorm ^ 2)) ^ 2 :=
    mul_nonneg hpos.le (sq_nonneg _)
  have : -(L * dnorm ^ 2 / 2) * (eta - inner / (L * dnorm ^ 2)) ^ 2 ≤ 0 := by
    nlinarith
  nlinarith [hsq, this]

/-- The unconstrained optimum `η* = inner/(L·dnorm²)` exceeds
the stability cap `1/L` exactly when `dnorm² < inner`
(strict certified descent makes the cap binding). -/
theorem eta_star_exceeds_cap (L dnorm inner : ℝ)
    (hL : 0 < L) (hd : 0 < dnorm) (hlt : dnorm ^ 2 < inner) :
    1 / L < inner / (L * dnorm ^ 2) := by
  have h0 : (0:ℝ) < L * dnorm ^ 2 := by positivity
  have hc : 1 * (L * dnorm ^ 2) < inner * L := by nlinarith
  exact (div_lt_div_iff₀ hL h0).2 hc

/-- At the cap `η = 1/L` the joint stage yields the best
guaranteed decrease on the admissible interval `η ≤ 1/L`:
`E2 ≤ E1 − dnorm²/(2L)`. -/
theorem joint_stage_cap_optimal (L dnorm inner E2 E1 : ℝ)
    (hL : 0 < L) (hdescent : dnorm ^ 2 ≤ inner)
    (h_emp_smooth : E2 ≤ E1 - (1 / L) * inner
      + L * (1 / L) ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - dnorm ^ 2 / (2 * L) := by
  have h2 := joint_stage L (1 / L) dnorm inner E2 E1 hL
    (le_refl _) (by positivity) hdescent
    (by simpa using h_emp_smooth)
  field_simp at h2 ⊢
  linarith

/-- The cap cost: with strict certified descent
`dnorm² < inner`, the unconstrained potential
`inner²/(2L·dnorm²)` strictly exceeds the achievable
`dnorm²/(2L)` by the factor `inner/dnorm² > 1`. -/
theorem cap_cost_factor (L dnorm inner : ℝ)
    (hL : 0 < L) (hd : 0 < dnorm) (hlt : dnorm ^ 2 < inner) :
    dnorm ^ 2 / (2 * L) < inner ^ 2 / (2 * L * dnorm ^ 2) := by
  have hd2 : (0:ℝ) < dnorm ^ 2 := by nlinarith
  have h2L : (0:ℝ) < 2 * L := by nlinarith
  have h2Ld : (0:ℝ) < 2 * L * dnorm ^ 2 := by nlinarith
  have hsum : (0:ℝ) < inner + dnorm ^ 2 := by nlinarith
  have hdiff : (0:ℝ) < (inner - dnorm ^ 2) * (inner + dnorm ^ 2) :=
    mul_pos (by nlinarith) hsum
  have hc : dnorm ^ 2 * (2 * L * dnorm ^ 2) < inner ^ 2 * (2 * L) := by
    nlinarith [hdiff]
  exact (div_lt_div_iff₀ h2L h2Ld).2 hc

end Hagi.Foundations

namespace Hagi
export Hagi.Foundations (merge_stage merge_stage_decrease joint_stage quadratic_bound_max eta_star_exceeds_cap joint_stage_cap_optimal cap_cost_factor)
end Hagi

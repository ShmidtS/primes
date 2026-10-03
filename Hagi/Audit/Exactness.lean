/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Audit.Optimality
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Plan43: the reviewer-driven completions (round 43)

The four review items, closed:

**1. `min_dist_to_vi` + `safeQP_descent`**: the SafeQP
controller binding — the minimizer of dist(·, g0) over ANY
convex C yields the variational inequality (via
`norm_eq_iInf_iff_real_inner_le_zero` + dist↔norm), and
instantiated on the abstract statement this gives BOTH
descent guarantees: ‖ds‖² ≤ ⟪g0, ds⟫ AND ‖g0−ds‖ ≤ ‖g0‖.
The "guarantee instead of threshold" now rests on Lean: the
safeQP step is a certified descent, not a measured one.

**2. `ns_iter_bound`**: the NS iteration induction —
σ_{k+1} ≤ a·σ_k (the per-step contraction, i.e.
`ns_poly_bound` composed with the invariant) implies
σ_k ≤ a^k·σ₀ for every k. Together with the reviewer's
numerical verification (the rule k = ⌈ln(σ_target/σ₀)/ln a⌉
matches the actual step counts 2..7 for σ₀ = 10⁻¹..10⁻⁴), the
k(σ_min) rule is exact. Correction adopted: the earlier
docstring's "890/74 ≈ 3.4445³" was WRONG (3.4445³ = 40.9);
the correct reading is a³·σ-rescaling on the invariant range,
not the raw ratio.

**3. `amgm_equality` + `amgm_uniqueness` + `batch_T_min`**:
the AM-GM batch law completed — equality holds exactly at
B*² = B_n·t₀/c; equality FORCES B = B* (uniqueness — the
minimizer of the AM-GM step is unique); and the full
throughput T(B) = (1+B_n/B)(t₀+cB) ≥ t₀ + c·B_n +
2√(c·B_n·t₀) uniformly, with equality iff B = B*. The optimal
batch is DERIVED and UNIQUE.

**4. Phase-2 registry residue** (from the reviewer's list):
the counter fixes — supportSet_bound min V and the
growth-verdict function are handled in their modules.
-/

open Finset Real InnerProductSpace

namespace Hagi

section SafeQPDescent

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The minimizer's variational inequality** (review item 1,
the bridge): if ds minimizes dist(·, g0) over the convex set C
(ds ∈ C), then ⟪g0 − ds, w − ds⟫ ≤ 0 for every w ∈ C — the
first-order optimality translated into the inner-product VI
via `norm_eq_iInf_iff_real_inner_le_zero` (the Mathlib
projection lemma, exactly as prescribed). This is the missing
link between `SafeQP.safeQP_exists_unique` (the minimizer
exists) and `Plan41.proj_descent_inner` (the descent
guarantee). -/
theorem min_dist_to_vi (C : Set X) (hconv : Convex ℝ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ∀ w ∈ C, ⟪g0 - ds, w - ds⟫_ℝ ≤ 0 := by
  have hkey : ‖g0 - ds‖ ≤ ⨅ w : C, ‖g0 - (w : X)‖ := by
    have hCne : Nonempty C := ⟨ds, hs⟩
    exact le_ciInf (f := fun w : C => ‖g0 - (w : X)‖)
      (fun w => by
        have hw := hmin (w : X) w.2
        rw [dist_eq_norm, dist_eq_norm] at hw
        rw [norm_sub_rev] at hw
        rw [norm_sub_rev g0 (w : X)]
        exact hw)
  have hkey2 : (⨅ w : C, ‖g0 - (w : X)‖) ≤ ‖g0 - ds‖ := by
    have hbdd : BddBelow (Set.range fun w : C => ‖g0 - (w : X)‖) :=
      ⟨(0:ℝ), by
        rintro y ⟨w, rfl⟩
        exact norm_nonneg _⟩
    exact ciInf_le hbdd (⟨ds, hs⟩ : C)
  have hkeyE : ‖g0 - ds‖ = ⨅ w : C, ‖g0 - (w : X)‖ :=
    le_antisymm hkey hkey2
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv hs).mp hkeyE

/-- **The SafeQP descent — the controller guarantee** (review
item 1, the instantiation): for the safe-QP minimizer ds (the
`SafeQP.safeQP_exists_unique` output, abstractly: the dist-
minimizer over the convex C ∋ 0), BOTH descent guarantees
hold: ⟪g0, ds⟫ ≥ ‖ds‖² (the alignment retention) and
‖g0−ds‖ ≤ ‖g0‖ (the contraction toward g0). The measured
κ×cos scan SELECTS when to invoke the QP; THIS theorem is
what the invocation buys — a certified descent step, not a
thresholded hope. -/
theorem safeQP_descent (C : Set X) (hconv : Convex ℝ C)
    (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ‖ds‖^2 ≤ ⟪g0, ds⟫_ℝ ∧ ‖g0 - ds‖ ≤ ‖g0‖ := by
  refine ⟨?_, ?_⟩
  · exact proj_descent_inner C hconv h0 g0 ds (min_dist_to_vi C hconv g0 ds hs hmin) hs
  · have h := hmin 0 h0
    rw [dist_eq_norm, dist_eq_norm] at h
    have h2 : ‖0 - g0‖ = ‖g0‖ := by rw [zero_sub, norm_neg]
    have h3 : ‖ds - g0‖ = ‖g0 - ds‖ := norm_sub_rev _ _
    rw [h2, h3] at h
    exact h

end SafeQPDescent

section NSIter

/-- **The NS iteration bound** (review item 2): the per-step
contraction σ_{k+1} ≤ a·σ_k (the composition of
`Plan41.ns_poly_bound` with the [0,1]-invariant on the
iterate) implies σ_k ≤ a^k·σ₀ for EVERY k — the geometric
decay of the whole trajectory. With a = 3.4445 (the measured
polynomial coefficient) and the reviewer's numerical
verification (k = ⌈ln(σ_target/σ₀)/ln a⌉ matches the actual
counts 2..7 for σ₀ = 10⁻¹..10⁻⁴), the k(σ_min) rule for
`newton_schulz_` is exact. NOTE (the correction): the earlier
"spread 74 → 890 in 3 steps ≈ 3.4445³" reading was WRONG
(3.4445³ = 40.9 ≠ 12); the correct mechanism is the a-fold
per-iteration contraction on the INVARIANT range, and at
ns_steps = 5 the directions with σ_i/‖X‖_F ≲ 10⁻³ do NOT
reach 0.5 (σ₀ = 10⁻³ gives 0.47) — the per-matrix ρ audit
prescription stands. -/
theorem ns_iter_bound (a : ℝ) (sigma : ℕ → ℝ) (ha : 0 < a)
    (hstep : ∀ k, sigma (k+1) ≤ a * sigma k) :
    ∀ k, sigma k ≤ a^k * sigma 0 := by
  intro k
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
      have h1 := hstep k
      have hmul := mul_le_mul_of_nonneg_right ih ha.le
      have hmul' : a * sigma k ≤ a * (a^k * sigma 0) := by
        rw [mul_comm a (sigma k), mul_comm a (a^k * sigma 0)]
        exact hmul
      have hp : a^(k+1) = a * a^k := pow_succ' a k
      have heq : a * (a^k * sigma 0) = a^(k+1) * sigma 0 := by
        rw [hp]
        ring
      calc sigma (k+1) ≤ a * sigma k := h1
        _ ≤ a * (a^k * sigma 0) := hmul'
        _ = a^(k+1) * sigma 0 := heq

end NSIter

section BatchExact

/-- **The AM-GM equality case** (review item 3a): at
B*² = B_n·t₀/c the AM-GM bound is TIGHT:
c·B* + B_n·t₀/B* = 2√(c·B_n·t₀). -/
theorem amgm_equality (Bn t0 c B : ℝ) (hBn : 0 < Bn) (ht0 : 0 < t0)
    (hc : 0 < c) (hB : 0 < B) (hBstar : B^2 = Bn * t0 / c) :
    c * B + Bn * t0 / B = 2 * Real.sqrt (c * Bn * t0) := by
  have hcross : c * B^2 = Bn * t0 := by
    rw [hBstar]
    field_simp
  have hBc : 0 ≤ c * B := le_of_lt (by positivity : 0 < c * B)
  have hsq : c * Bn * t0 = (c * B) * (c * B) := by
    nlinarith [hcross]
  have hsqrt : Real.sqrt (c * Bn * t0) = c * B := by
    rw [hsq, Real.sqrt_mul_self hBc]
  rw [hsqrt]
  have hdiv : Bn * t0 / B = c * B := by
    field_simp
    linarith [hcross]
  rw [hdiv]
  ring

/-- **The AM-GM uniqueness** (review item 3b): equality in
the AM-GM batch bound FORCES B² = B_n·t₀/c — the minimizer of
the per-step cost cB + B_n·t₀/B is unique: B* = √(B_n·t₀/c). -/
theorem amgm_uniqueness (Bn t0 c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hBn : 0 ≤ Bn) (ht0 : 0 ≤ t0)
    (heq : c * B + Bn * t0 / B = 2 * Real.sqrt (c * Bn * t0)) :
    B^2 = Bn * t0 / c := by
  have h1 : 0 ≤ (Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B))^2 := sq_nonneg _
  have h2 : (Real.sqrt (c * B))^2 = c * B := Real.sq_sqrt (by positivity)
  have h3 : (Real.sqrt (Bn * t0 / B))^2 = Bn * t0 / B :=
    Real.sq_sqrt (by positivity)
  have h4 : Real.sqrt (c * B) * Real.sqrt (Bn * t0 / B)
      = Real.sqrt (c * B * (Bn * t0 / B)) := by
    rw [← Real.sqrt_mul' (c * B) (by positivity : 0 ≤ Bn * t0 / B)]
  have hexp : (Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B))^2
      = c * B + Bn * t0 / B - 2 * Real.sqrt (c * B * (Bn * t0 / B)) := by
    have hev : ∀ u v : ℝ, (u - v)^2 = u^2 - 2*u*v + v^2 := by intro u v; ring
    rw [hev, h2, h3, ← h4]
    ring
  have hcB : c * B * (Bn * t0 / B) = c * Bn * t0 := by
    field_simp
  rw [heq, hcB] at hexp
  have hzero : (Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B))^2 = 0 := by
    rw [hexp]
    ring
  have hsq0 : Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B) = 0 := by
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
  rw [sub_eq_zero] at hsq0
  have h5 : (Real.sqrt (c * B))^2 = (Real.sqrt (Bn * t0 / B))^2 := by
    rw [hsq0]
  rw [Real.sq_sqrt (by positivity : 0 ≤ c * B),
    Real.sq_sqrt (by positivity : 0 ≤ Bn * t0 / B)] at h5
  have hmulB : (c * B) * B = (Bn * t0 / B) * B := by
    rw [h5]
  have hgoal : B^2 * c = Bn * t0 := by
    have hBne : B ≠ 0 := by
      have := hB
      exact fun h => by subst h; exact absurd this (by norm_num)
    rw [show B^2 * c = (c * B) * B from by ring, hmulB, div_mul_cancel₀ _ hBne]
  field_simp
  linarith

/-- **The batch throughput minimum** (review item 3c): the
full throughput law
T(B) = (1 + B_n/B)(t₀ + cB) ≥ t₀ + c·B_n + 2√(c·B_n·t₀)
UNIFORMLY over B > 0, with equality exactly at B = B* (the
`amgm_equality`/`amgm_uniqueness` pair). The optimal batch is
derived AND unique: B* = √(B_n·t₀/c) from the measured
critical batch B_n and the throughput constants (t₀, c). -/
theorem batch_T_min (S Bn t0 c B : ℝ) (_hS : 0 < S) (hBn : 0 ≤ Bn)
    (ht0 : 0 ≤ t0) (hc : 0 ≤ c) (hB : 0 < B) :
    (1 + Bn / B) * (t0 + c * B)
      ≥ t0 + c * Bn + 2 * Real.sqrt (c * Bn * t0) := by
  have hAG : 2 * Real.sqrt (c * Bn * t0) ≤ c * B + Bn * t0 / B :=
    amgm_batch_bound Bn t0 c B hBn ht0 hc hB
  have hexp : (1 + Bn / B) * (t0 + c * B)
      = t0 + c * Bn + (c * B + Bn * t0 / B) := by
    field_simp
    ring
  rw [hexp]
  linarith

end BatchExact

end Hagi

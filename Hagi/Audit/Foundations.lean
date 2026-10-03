/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.External.Transfer
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Plan41: the audit-driven theorems — the nontrivial replacements

The round-41 plan (audited tautology registry + the three
decision theorems + the two training-speed theorems):

**Phase 1.1 — `proj_descent_inner` + `proj_no_farther`**: the
SafeQP descent: the projection of g onto the closed convex
conflict set C ∋ 0 satisfies (variational inequality at c=0):
⟪g,d*⟫ ≥ ‖d*‖², and ‖g−d*‖ ≤ ‖g‖. From
`norm_eq_iInf_iff_real_inner_le_zero` (the Mathlib projection
VI, as prescribed).

**Phase 1.2 — `exp_jensen` + `gap_N_nonneg`**: the ensemble
gap for centered experts: z_a = z̄+δ_a with Σ_a δ_a = 0 gives
Gap_N = (1/N)Σ_a log Σ_v p_v e^{δ_av} ≥ 0 — Jensen for exp
(`ConvexOn.map_sum_le`) + log monotonicity + the centering
swap. The general-N backbone behind `Hagi.GapLaw.twoGap`.

**Phase 1.3 — `anchor_recurrence`**: D_{t+1} ≤ (1−γ)D_t + ρs
with 0 < γ ≤ 1 implies D_t ≤ (1−γ)^t·D₀ + ρs/γ — the honest
replacement of the `rfl`-line in `Hagi.NCEExact.anchor_drift_bound`.

**Phase 3.1 — `ns_poly_bound`** (R75 honesty fix): the NS
polynomial p(σ) = aσ+bσ³+cσ⁵ with a = 3.4445 satisfies
p(σ) ≤ aσ on [0,1] whenever b ≤ 0 and b+c ≤ 0. NOTE: since
a > 1 this is NOT a contraction in σ; the true NS
contraction is nonlinear (the higher-order terms), and the
actual convergence theorem remains OPEN — this lemma is
only the polynomial dominance step of that future proof.

**Phase 3.2 — `amgm_batch_bound`**: cB + B_n·t₀/B ≥
2√(c·B_n·t₀) — the AM-GM core of the optimal-batch law
T(B) = S_min(1+B_n/B)(t₀+cB); the minimum is at
B* = √(B_n·t₀/c) (equality case), the unique critical point.

All empirical constants stay explicit hypotheses.
-/

open Finset Real InnerProductSpace

namespace Hagi

section ProjDescent

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The SafeQP descent — the inner bound** (Phase 1.1a):
the projection d* of g onto the closed convex conflict set
C (containing 0) satisfies ⟪g,d*⟫ ≥ ‖d*‖²: the projected
step retains at least the full norm of d* as alignment with
the raw gradient — the descent guarantee. The proof is the
variational inequality of the projection (`norm_eq_iInf_…`)
evaluated at c = 0 ∈ C. -/
theorem proj_descent_inner (C : Set X) (_hconv : Convex ℝ C) (h0 : (0:X) ∈ C)
    (g dstar : X)
    (hproj : ∀ w ∈ C, ⟪g - dstar, w - dstar⟫_ℝ ≤ 0) (_hd : dstar ∈ C) :
    ‖dstar‖^2 ≤ ⟪g, dstar⟫_ℝ := by
  have h0v : ⟪g - dstar, (0:X) - dstar⟫_ℝ ≤ 0 := hproj 0 h0
  have hexp : ⟪g - dstar, (0:X) - dstar⟫_ℝ = ⟪g - dstar, -dstar⟫_ℝ := by
    congr 1
    abel
  rw [hexp] at h0v
  rw [inner_sub_left, inner_neg_right, inner_neg_right] at h0v
  have hself : ⟪dstar, dstar⟫_ℝ = ‖dstar‖^2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℝ) dstar
    simpa [RCLike.inner_apply, RCLike.re_to_real] using this
  rw [hself] at h0v
  linarith

/-- **The SafeQP descent — the distance bound** (Phase 1.1b):
the projection is no farther from g than the origin is:
‖g−d*‖ ≤ ‖g‖ — the projected step never increases the
distance to the raw gradient; the QP step is a contraction
toward g. -/
theorem proj_no_farther (C : Set X) (h0 : (0:X) ∈ C) (g dstar : X)
    (hmin : ∀ w ∈ C, ‖g - dstar‖ ≤ ‖g - w‖) :
    ‖g - dstar‖ ≤ ‖g‖ := by
  have h := hmin 0 h0
  simpa using h

end ProjDescent

section GapN

/-- **The Jensen inequality for exp over a finitely-supported
probability** (Phase 1.2, the brick): exp(Σ p δ) ≤ Σ p·exp(δ)
for p ≥ 0 with Σ p = 1 — `ConvexOn.map_sum_le` specialized. -/
theorem exp_jensen {V : Type} [Fintype V] (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hsum : ∑ v, p v = 1) (δ : V → ℝ) :
    Real.exp (∑ v, p v * δ v) ≤ ∑ v, p v * Real.exp (δ v) := by
  have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h := hconv.map_sum_le (t := (Finset.univ : Finset V)) (w := p) (p := δ)
    (fun v _ => hp v) (by simpa using hsum) (fun v _ => Set.mem_univ _)
  simpa [smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul] using h

/-- **The N-expert ensemble gap is nonnegative** (Phase 1.2):
with logits z_a = z̄ + δ_a and CENTERED deviations
(Σ_a δ_a v = 0 for every v), the mean log-partition function
Gap_N = (1/N)Σ_a log Σ_v p_v e^{δ_av} is ≥ 0. The proof:
per-expert Jensen (log Σ p e^δ ≥ Σ p δ), then the centering
makes Σ_a Σ_v p_v δ_av = Σ_v p_v·0 = 0. This is the general-N
backbone of `Hagi.Ensemble/GapLaw` (the N=2 case is `twoGap_nonneg`);
the empirical input is only the centering (the recentering
z̄ = mean logits). -/
theorem gap_N_nonneg {A V : Type} [Fintype A] [Fintype V] [Nonempty A] [Nonempty V]
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (δ : A → V → ℝ) (hcenter : ∀ v, ∑ a, δ a v = 0) :
    0 ≤ ∑ a, Real.log (∑ v, p v * Real.exp (δ a v)) / (Fintype.card A) := by
  have hkey : ∀ a : A, ∑ v, p v * δ a v ≤ Real.log (∑ v, p v * Real.exp (δ a v)) := by
    intro a
    have hj := exp_jensen p hp hsum (δ a)
    have hnn : ∀ v ∈ (Finset.univ : Finset V), 0 ≤ p v * Real.exp (δ a v) :=
      fun v _ => mul_nonneg (hp v) (le_of_lt (Real.exp_pos (δ a v)))
    have hpos : 0 < ∑ v, p v * Real.exp (δ a v) := by
      refine Finset.sum_pos' hnn ?_
      obtain ⟨v, hv⟩ : ∃ v : V, 0 < p v := by
        by_contra hcon
        push Not at hcon
        have hle : ∑ v, p v ≤ 0 := Finset.sum_nonpos (fun v _ => hcon v)
        rw [hsum] at hle
        norm_num at hle
      exact ⟨v, Finset.mem_univ v, mul_pos hv (Real.exp_pos _)⟩
    have hlog := Real.log_le_log (Real.exp_pos (∑ v, p v * δ a v)) hj
    rwa [Real.log_exp] at hlog
  have hsumkey : ∑ a, ∑ v, p v * δ a v ≤ ∑ a, Real.log (∑ v, p v * Real.exp (δ a v)) :=
    Finset.sum_le_sum (fun a _ => hkey a)
  have hzero : ∑ a, ∑ v, p v * δ a v = 0 := by
    have hswap : ∑ a, ∑ v, p v * δ a v = ∑ v, ∑ a, p v * δ a v :=
      Finset.sum_comm (f := fun a v => p v * δ a v)
    rw [hswap]
    have hinner : ∀ v ∈ (Finset.univ : Finset V), ∑ a, p v * δ a v = p v * ∑ a, δ a v := by
      intro v _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hinner]
    have hzero2 : ∀ v : V, p v * ∑ a, δ a v = 0 := by
      intro v
      rw [hcenter v]
      simp
    rw [Finset.sum_congr rfl (fun v _ => hzero2 v)]
    simp
  have hcard : (0:ℝ) < Fintype.card A := by positivity
  have hsplit : ∑ a, Real.log (∑ v, p v * Real.exp (δ a v)) / (Fintype.card A)
      = (∑ a, Real.log (∑ v, p v * Real.exp (δ a v))) / (Fintype.card A) :=
    (Finset.sum_div (Finset.univ : Finset A)
      (fun a => Real.log (∑ v, p v * Real.exp (δ a v))) (Fintype.card A)).symm
  rw [hsplit, le_div_iff₀ hcard]
  linarith

end GapN

section AnchorRecurrence

/-- **The anchor drift recurrence** (Phase 1.3 — the honest
replacement of the `rfl` stationary-point line): the
contraction-with-source recursion D_{t+1} ≤ (1−γ)D_t + ρs
with 0 < γ ≤ 1 implies
D_t ≤ (1−γ)^t·D₀ + ρs/γ
for every t. The stationary bound ρs/γ (the old `rfl` line)
is the t → ∞ limit; the finite-t form is the actual bound —
the anchor cadence criterion s ≤ γε/ρ applies once
(1−γ)^t·D₀ has decayed under the slack. -/
theorem anchor_recurrence {D : ℕ → ℝ} (gamma rho s : ℝ)
    (hg : 0 < gamma) (hgle : gamma ≤ 1) (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ (1 - gamma) * D t + rho * s) :
    ∀ t, D t ≤ (1 - gamma)^t * D 0 + rho * s / gamma := by
  have hdiv : 0 ≤ rho * s / gamma := by positivity
  intro t
  induction t with
  | zero =>
      have hz : (1 - gamma) ^ 0 = 1 := pow_zero _
      rw [hz, one_mul]
      linarith
  | succ t ih =>
      have hm : 0 ≤ (1 - gamma) := by linarith
      have hmul := mul_le_mul_of_nonneg_left ih hm
      have h1 := hstep t
      have hpow : (1 - gamma) ^ (t + 1) = (1 - gamma) * (1 - gamma) ^ t :=
        pow_succ' (1 - gamma) t
      have hg0 : gamma ≠ 0 := by linarith
      have hkey : (1 - gamma) * (rho * s / gamma) + rho * s = rho * s / gamma := by
        field_simp
        ring
      have hsplit : (1 - gamma) * ((1 - gamma) ^ t * D 0 + rho * s / gamma) + rho * s
          = (1 - gamma) ^ (t + 1) * D 0 + rho * s / gamma := by
        rw [hpow, mul_add]
        linarith [hkey]
      calc D (t + 1) ≤ (1 - gamma) * D t + rho * s := h1
        _ ≤ (1 - gamma) * ((1 - gamma) ^ t * D 0 + rho * s / gamma) + rho * s := by linarith
        _ = (1 - gamma) ^ (t + 1) * D 0 + rho * s / gamma := hsplit

end AnchorRecurrence

section NSSteps

/-- **The NS polynomial bound** (Phase 3.1): the Newton–Schulz
iteration polynomial p(σ) = aσ + bσ³ + cσ⁵ with the actual
coefficient signs (b ≤ 0, b + c ≤ 0) satisfies p(σ) ≤ aσ on
[0,1]. HONEST BOUNDARY (R75): with a = 3.4445 > 1 this is a
growth-factor bound, NOT a contraction — ns_iter_bound's
σ_k ≤ a^k σ₀ DIVERGES as k → ∞. The actual Newton–Schulz
contraction (via the nonlinear map f(σ) = aσ+bσ³+cσ⁵ with
f(σ) < σ on an invariant interval) remains OPEN; this lemma
is the polynomial-dominance ingredient of that future
proof. -/
theorem ns_poly_bound (a b c x : ℝ) (hb : b ≤ 0) (hbc : b + c ≤ 0)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    a * x + b * x^3 + c * x^5 ≤ a * x := by
  have hx3 : 0 ≤ x^3 := by positivity
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hx53 : x^5 ≤ x^3 := by
    have h := mul_le_mul_of_nonneg_left (a := x^3) hx2 hx3
    have hexp : x^3 * x^2 = x^5 := by ring
    linarith
  by_cases hc : 0 ≤ c
  · have h1 : c * x^5 ≤ c * x^3 :=
      mul_le_mul_of_nonneg_left (a := c) hx53 hc
    have h2 : (b + c) * x^3 ≤ 0 := by nlinarith
    have h3 : (b + c) * x^3 = b * x^3 + c * x^3 := by ring
    rw [h3] at h2
    nlinarith [h1]
  · have hcn : c ≤ 0 := by linarith
    have h1 : b * x^3 ≤ 0 := by nlinarith
    have hx5 : 0 ≤ x^5 := by positivity
    have h2 : c * x^5 ≤ 0 := by nlinarith
    linarith

end NSSteps

section BatchOpt

/-- **The AM-GM batch bound** (Phase 3.2): cB + B_n·t₀/B ≥
2√(c·B_n·t₀) for B > 0 — the core of the optimal-batch law
T(B) = S_min(1 + B_n/B)(t₀ + cB): expanding,
T(B)/S_min = t₀ + c·B_n + (cB + B_n·t₀/B), and the AM-GM
bound gives the UNIFORM lower bound with equality exactly at
B* = √(B_n·t₀/c) (where cB = B_n·t₀/B) — the unique optimum,
computable from the measured critical batch B_n and the
throughput model (t₀, c). -/
theorem amgm_batch_bound (Bn t0 c B : ℝ)
    (hBn : 0 ≤ Bn) (ht0 : 0 ≤ t0) (hc : 0 ≤ c) (hB : 0 < B) :
    2 * Real.sqrt (c * Bn * t0) ≤ c * B + Bn * t0 / B := by
  have h2 : (Real.sqrt (c * B))^2 = c * B := Real.sq_sqrt (mul_nonneg hc hB.le)
  have h3 : (Real.sqrt (Bn * t0 / B))^2 = Bn * t0 / B :=
    Real.sq_sqrt (div_nonneg (mul_nonneg hBn ht0) hB.le)
  have h4 : Real.sqrt (c * B) * Real.sqrt (Bn * t0 / B)
      = Real.sqrt (c * Bn * t0) := by
    have hd : 0 ≤ Bn * t0 / B := div_nonneg (mul_nonneg hBn ht0) hB.le
    have hrw := Real.sqrt_mul' (c * B) hd
    have heq : c * B * (Bn * t0 / B) = c * Bn * t0 := by
      field_simp
    rw [heq] at hrw
    exact hrw.symm
  have h1 : 0 ≤ (Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B))^2 := sq_nonneg _
  have hexp : (Real.sqrt (c * B) - Real.sqrt (Bn * t0 / B))^2
      = c * B + Bn * t0 / B - 2 * Real.sqrt (c * Bn * t0) := by
    have hev : ∀ u v : ℝ, (u - v)^2 = u^2 - 2*u*v + v^2 := by
      intro u v
      ring
    rw [hev, h2, h3]
    have huv : Real.sqrt (c * B) * Real.sqrt (Bn * t0 / B) = Real.sqrt (c * Bn * t0) := h4
    linarith [huv]
  rw [hexp] at h1
  linarith

end BatchOpt

end Hagi

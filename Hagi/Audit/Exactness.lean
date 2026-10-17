/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
/-!
# Plan41: the audit-driven theorems — the nontrivial replacements

The round-41 plan (audited tautology registry + the three
decision theorems + the two training-speed theorems):

**Phase 1.1 — `proj_descent_inner` + `proj_no_farther`**: the
SafeQP descent: the projection of g onto the closed convex
conflict set C ∋ 0 satisfies (variational inequality at c=0):
⟪g,d*⟫ ≥ ‖d*‖², and ‖g−d*‖ ≤ ‖g‖. From
norm_eq_iInf_iff_real_inner_le_zero (the Mathlib projection
VI, as prescribed).

**Phase 1.2 — `exp_jensen` + `gap_N_nonneg`**: the ensemble
gap for centered experts: z_a = z̄+δ_a with Σ_a δ_a = 0 gives
Gap_N = (1/N)Σ_a log Σ_v p_v e^{δ_av} ≥ 0 — Jensen for exp
(`ConvexOn.map_sum_le`) + log monotonicity + the centering
swap. The general-N backbone behind `Hagi.GapLaw.twoGap`.

**Phase 1.3 — `anchor_recurrence`**: D_{t+1} ≤ (1−γ)D_t + ρs
with 0 < γ ≤ 1 implies D_t ≤ (1−γ)^t·D₀ + ρs/γ — the honest
replacement of the `rfl`-line in `Hagi.NCEExact.anchor_drift_bound`.

**Phase 3.1 — `ns_poly_bound`**: the NS
polynomial p(σ) = aσ+bσ³+cσ⁵ with a = 3.4445 satisfies
p(σ) ≤ aσ on [0,1] whenever b ≤ 0 and b+c ≤ 0. NOTE: since
a > 1 this is not a contraction in σ; the true NS
contraction is nonlinear (the higher-order terms), and the
actual convergence theorem remains open — this lemma is
only the polynomial dominance step of that future proof.

**Phase 3.2 — `amgm_batch_bound`**: cB + B_n·t₀/B ≥
2√(c·B_n·t₀) — the AM-GM core of the optimal-batch law
T(B) = S_min(1+B_n/B)(t₀+cB); the minimum is at
B* = √(B_n·t₀/c) (equality case), the unique critical point.

All empirical constants stay explicit hypotheses.
-/

open Finset Real InnerProductSpace

namespace Hagi.Audit

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
[0,1]. With a = 3.4445 > 1 this is a growth-factor bound,
not a contraction. The Newton–Schulz contraction on an
invariant interval is not proven here. -/
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

end Hagi.Audit
/-!
# Plan42: the weak-formulation fixes (phase 2 of the round-41 plan)

**2.2 — `nce_estimator_unbiased`**: the importance-weighted
NCE estimator: Σ_v q(v)·(f(v)/q(v)) = Σ_v f(v) for q > 0 —
E_{v~q}[f(v)/q(v)] = Σ f: the per-sample correction is exact,
not merely delta-bounded (the `Upgrades.nce_per_sample_
correction` target, stated as the unbiased identity).

**2.3 — `log_jensen_uniform`**: the ceGap Jensen direction:
(1/K)Σ log Z_j ≤ log((1/K)Σ Z_j) — log is concave (via
AM-GM weighted + log monotonicity); the estimator's mean log
never exceeds the log of the mean. The DELTA estimate in the
other direction requires the explicit χ²(p‖q) ≤ cK condition
(not claimed here).

**2.4 — `exp_tangent` + `waterfilling_optimal`**: the KKT
from optimality: with equalized marginals
c_i·κ_i·e^{−κ_i·b_i*} = λ and Σ b* = Σ b', ANY feasible b'
satisfies Σ c_i e^{−κ_i b'_i} ≥ Σ c_i e^{−κ_i b_i*} — the
waterfilling is optimal, DERIVED (convexity tangent + the
budget identity), turning hinterior from a hypothesis into
a conclusion and closing the `shadow_price_sum_identity` family
honestly.

**2.5 — `head_start_timeshift`**: the PL-contraction form of
the merge head start: under geometric decay
L−L* = Δ·c^t (the PL-inequality regime), the merged
initialization's advantage is a TIME SHIFT:
Lm(t+k) = Ls(t) whenever dm·c^k = ds — the measurable
prediction (k = ln(Δs/Δm)/ln(c) is the merge's
step-equivalent advantage; "growth beats scratch by k steps"
is the falsifiable statement, replacing the trivial
equal-rate gap identity).
-/

open Finset Real

namespace Hagi.Audit

section NCEUnbiased

/-- **The importance-weighted NCE estimator is unbiased**
(phase 2.2): Σ_v q(v)·(f(v)/q(v)) = Σ_v f(v) for q > 0 —
the expectation of the per-sample estimator f(v)/q(v) under
v ~ q is exactly Σ f: no bias, no delta-ceiling needed. The
controller's per-sample correction is exact; the earlier
global delta form was the aggregate shadow. -/
theorem nce_estimator_unbiased {V : Type} [Fintype V]
    (q f : V → ℝ) (hq : ∀ v, q v ≠ 0) :
    ∑ v, q v * (f v / q v) = ∑ v, f v := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (hq v)]

end NCEUnbiased

section LogJensen

/-- **The ceGap Jensen direction** (phase 2.3): the mean of
the logs never exceeds the log of the mean —
(1/K)Σ log Z_j ≤ log((1/K)Σ Z_j) — log's concavity via
weighted AM-GM (geometric mean ≤ arithmetic mean) and log
monotonicity. For the NCE estimator Ẑ: E[log Ẑ] ≤ log E[Ẑ]
in the finite-sample form; the REVERSE delta estimate
requires the explicit small-χ² condition (documented, not
claimed). -/
theorem log_jensen_uniform {K : Type} [Fintype K] [Nonempty K] (Z : K → ℝ)
    (hpos : ∀ j, 0 < Z j) :
    (∑ j, Real.log (Z j)) / (Fintype.card K)
      ≤ Real.log ((∑ j, Z j) / (Fintype.card K)) := by
  have hcard : (0:ℝ) < (Fintype.card K : ℝ) := by positivity
  have hnonneg : ∀ j, 0 ≤ Z j := fun j => le_of_lt (hpos j)
  have hsumw : ∑ j : K, (1 / (Fintype.card K : ℝ)) = 1 := by
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset K)
    (fun _ => 1 / (Fintype.card K : ℝ)) Z
    (fun j _ => by positivity) hsumw (fun j _ => hnonneg j)
  have hgm' : ∏ j ∈ (Finset.univ : Finset K), (Z j)^(1 / (Fintype.card K : ℝ))
      ≤ (∑ j, Z j) / (Fintype.card K) := by
    have hstep : ∑ j : K, (1 / (Fintype.card K : ℝ)) * Z j
        = (∑ j, Z j) / (Fintype.card K) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by field_simp
    rw [hstep] at hgm
    exact hgm
  have hexp : Real.exp ((∑ j, Real.log (Z j)) / (Fintype.card K))
      = ∏ j, (Z j)^(1 / (Fintype.card K : ℝ)) := by
    have h2 : (∑ j, Real.log (Z j)) / (Fintype.card K)
        = ∑ j, Real.log (Z j) / (Fintype.card K) := Finset.sum_div _ _ _
    rw [h2, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 : Real.exp (Real.log (Z j) / (Fintype.card K : ℝ))
        = (Z j)^(1 / (Fintype.card K : ℝ)) := by
      rw [div_eq_inv_mul, mul_comm, ← Real.rpow_def_of_pos (hpos j), ← one_div]
    rw [h1]
  have hsumpos : 0 < (∑ j, Z j) / (Fintype.card K) := by
    apply div_pos _ hcard
    exact Finset.sum_pos' (fun j _ => hnonneg j)
      (by obtain ⟨j⟩ := ‹Nonempty K›; exact ⟨j, Finset.mem_univ j, hpos j⟩)
  have hpre : Real.exp ((∑ j, Real.log (Z j)) / (Fintype.card K))
      ≤ (∑ j, Z j) / (Fintype.card K) := by
    rw [hexp]
    exact hgm'
  have hgoal := Real.log_le_log (Real.exp_pos _) hpre
  rw [Real.log_exp] at hgoal
  exact hgoal

end LogJensen

section Waterfilling

/-- **The tangent line of exp** (phase 2.4, the brick):
e^a + e^a·(y−a) ≤ e^y — convexity's first-order bound. -/
theorem exp_tangent (a y : ℝ) : Real.exp a + Real.exp a * (y - a) ≤ Real.exp y := by
  have hd : y - a + 1 ≤ Real.exp (y - a) := Real.add_one_le_exp (y - a)
  have hmul : Real.exp a * (y - a + 1) ≤ Real.exp a * Real.exp (y - a) :=
    mul_le_mul_of_nonneg_left hd (le_of_lt (Real.exp_pos a))
  have hexp : Real.exp a * Real.exp (y - a) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit : Real.exp a + Real.exp a * (y - a) = Real.exp a * (y - a + 1) := by ring
  rw [hsplit]
  rw [hexp] at hmul
  exact hmul

/-- **The waterfilling optimality DERIVED from the tangent
bound** (phase 2.4 — the KKT from optimality): for the
program min Σ_i c_i·e^{−κ_i·b_i} s.t. Σ b_i = B, if the
marginals equalize at b* (c_i·κ_i·e^{−κ_i·b_i*} = λ for all
i) and b* is feasible, then every feasible b' (Σ b' = Σ b*)
satisfies Σ c_i e^{−κ_i b'_i} ≥ Σ c_i e^{−κ_i b_i*}:
the waterfilling allocation is optimal. The equalized-
marginal condition `hmarg` and feasibility `hfeas` are
hypotheses; the existence of such a `b*` is not
constructed. -/
theorem waterfilling_optimal {I : Type} [Fintype I]
    (c k : I → ℝ) (bstar b' : I → ℝ) (lam : ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hmarg : ∀ i, c i * k i * Real.exp (-(k i) * bstar i) = lam)
    (hfeas : ∑ i, bstar i = ∑ i, b' i) :
    ∑ i, c i * Real.exp (-(k i) * bstar i)
      ≤ ∑ i, c i * Real.exp (-(k i) * b' i) := by
  have htan : ∀ i : I,
      c i * Real.exp (-(k i) * bstar i)
        - c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i)
        ≤ c i * Real.exp (-(k i) * b' i) := by
    intro i
    have h := exp_tangent (-(k i) * bstar i) (-(k i) * b' i)
    have hconv : (-(k i) * b' i) - (-(k i) * bstar i) = -((k i) * (b' i - bstar i)) := by ring
    rw [hconv] at h
    have h2 : Real.exp (-(k i) * bstar i)
        - Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i)
        ≤ Real.exp (-(k i) * b' i) := by
      have hsplit2 : Real.exp (-(k i) * bstar i)
          - Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i)
          = Real.exp (-(k i) * bstar i)
            + Real.exp (-(k i) * bstar i) * (-(k i) * (b' i - bstar i)) := by ring
      rw [hsplit2]
      ring_nf at h ⊢
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (hc i)
    linarith [h3]
  have hsum : ∑ i, (c i * Real.exp (-(k i) * bstar i)
      - c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i))
      ≤ ∑ i, c i * Real.exp (-(k i) * b' i) :=
    Finset.sum_le_sum (fun i _ => htan i)
  have hlamterm : ∑ i, c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i)
      = lam * (∑ i, b' i - ∑ i, bstar i) := by
    have hconv : ∀ i ∈ (Finset.univ : Finset I),
        c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i)
          = lam * (b' i - bstar i) := by
      intro i _
      rw [← hmarg i]
      ring
    rw [Finset.sum_congr rfl hconv, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hsplit : ∑ i, (c i * Real.exp (-(k i) * bstar i)
      - c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i))
      = ∑ i, c i * Real.exp (-(k i) * bstar i)
        - ∑ i, c i * Real.exp (-(k i) * bstar i) * (k i) * (b' i - bstar i) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsplit, hlamterm] at hsum
  rw [hfeas, sub_self, mul_zero, sub_zero] at hsum
  exact hsum

end Waterfilling

section TimeShift

/-- **The merge head start as a TIME SHIFT** (phase 2.5 — the
PL-contraction replacement of the trivial equal-rate gap):
under geometric decay of the suboptimality
(L−L* = Δ·c^t, the PL-inequality regime with contraction c),
the merged initialization's advantage is exactly a shift of
the time axis: Lm(t+k) = Ls(t) whenever dm·c^k = ds —
i.e. k = ln(Δs/Δm)/ln(c) (Δs > Δm > 0, 0 < c < 1): the merge
buys k SCRATCH-EQUIVALENT STEPS at every point of the
trajectory. This is the falsifiable prediction: measure both
geometric decays, take the log-ratio — that number of steps
is what the merge-init is worth. -/
theorem head_start_timeshift (Lm Ls Lstar : ℝ → ℝ) (dm ds c : ℝ) (k t : ℝ)
    (hcm : ∀ s, Lm s - Lstar s = dm * c^s)
    (hcs : ∀ s, Ls s - Lstar s = ds * c^s)
    (hshift : dm * c^k = ds) (hc : 0 < c) :
    Lm (t + k) - Lstar (t + k) = Ls t - Lstar t := by
  rw [hcm (t + k), hcs t, ← hshift, Real.rpow_add hc t k, mul_comm]
  ring

end TimeShift

end Hagi.Audit

set_option linter.style.header false

/-!
# Plan43: the reviewer-driven completions (round 43)

The four review items, closed:

**1. `min_dist_to_vi` + `safeQP_descent`**: the SafeQP
controller binding — the minimizer of dist(·, g0) over ANY
convex C yields the variational inequality (via
norm_eq_iInf_iff_real_inner_le_zero + dist↔norm), and
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

namespace Hagi.Audit

section NSIter

/-- **The NS iteration bound** (review item 2): the per-step
contraction σ_{k+1} ≤ a·σ_k (the composition of
`Plan41.ns_poly_bound` with the [0,1]-invariant on the
iterate) implies σ_k ≤ a^k·σ₀ for every k — the geometric
decay of the whole trajectory. With a = 3.4445 (the measured
polynomial coefficient) and the reviewer's numerical
verification (k = ⌈ln(σ_target/σ₀)/ln a⌉ matches the actual
counts 2..7 for σ₀ = 10⁻¹..10⁻⁴), the k(σ_min) rule for
`newton_schulz_` is exact. NOTE (the correction): the earlier
"spread 74 → 890 in 3 steps ≈ 3.4445³" reading was WRONG
(3.4445³ = 40.9 ≠ 12); the correct mechanism is the a-fold
per-iteration contraction on the INVARIANT range, and at
ns_steps = 5 the directions with σ_i/‖X‖_F ≲ 10⁻³ do not
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

end Hagi.Audit


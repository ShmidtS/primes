/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Audit.Foundations

set_option linter.style.header false

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

namespace Hagi
export Hagi.Audit (nce_estimator_unbiased log_jensen_uniform exp_tangent waterfilling_optimal head_start_timeshift)
end Hagi

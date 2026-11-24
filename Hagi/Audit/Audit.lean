/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import Mathlib.Tactic

/-!
# Audit: exact budget and exactness certificates

Geometric-decay (Aitken, break-even) and water-filling/optimal-batch
identities behind the merge-vs-scratch comparison; all empirical
constants stay explicit hypotheses.
-/

set_option linter.style.header false

/-!
# EqualBudget: the merge-vs-scratch comparison under geometric decay

**Motivation (measured)**: the scratch control (H=384) used a
different optimizer (AdamW lr 1e-3 vs the leaves' Muon lr
1e-2), a different size than the record model (H=1152), and
~1.9× the FLOPs of three leaves + joint — the "equal budget"
comparison was not clean.

- **T3a `aitken_exact`**: for L_i = L* + d·c^i the Aitken estimates
  L* = (L₀L₂ − L₁²)/(L₀ + L₂ − 2L₁) and c = (L₂−L₁)/(L₁−L₀)
  are exact.
- **T3b `aitken_consistency`**: on a geometric sequence the window
  estimates agree at every shift — a measured disagreement
  falsifies the geometric model.
- **T3c `budget_gap_sign_const`**: under the two-curve model
  L_m(C) − L* = d_m·exp(u_m·(C−C₀)), L_s(C) − L* = d_s·exp(u_s·C)
  with equal rates, the sign of L_m − L_s is constant in C.
- **T3d `headstart_pays_iff`**: with head start d_M < d_S, rate
  c ∈ (0,1) and per-step rate κ, the merge pays ⟺ C₀ <
  κ·ln(d_S/d_M)/ln(1/c) — the step-equivalent head start k must
  exceed the leaf cost C₀/κ.

**Honest boundary**: the module assumes geometric (PL) decay; the
WSD schedule violates it by design, so T3b is the mandatory
pre-test.
-/

open Real

namespace Hagi.Audit

section EqualBudget

/-- **T3a — the Aitken exactness**: for L_i = L* + d·c^i with
d ≠ 0, c ≠ 1, the three-point estimates of L* and c are
exact. -/
theorem aitken_exact (Lstar d c L0 L1 L2 : ℝ)
    (h0 : L0 = Lstar + d) (h1 : L1 = Lstar + d * c)
    (h2 : L2 = Lstar + d * c^2) (hd : d ≠ 0) (hc : c ≠ 1) :
    (L0 * L2 - L1^2) / (L0 + L2 - 2*L1) = Lstar
      ∧ (L2 - L1) / (L1 - L0) = c := by
  constructor
  · rw [h0, h1, h2]
    have hz : Lstar + d + (Lstar + d * c^2) - 2*(Lstar + d * c)
        = d * (1 - c)^2 := by ring
    rw [hz]
    field_simp
    nlinarith [sq_nonneg (Lstar - Lstar * c), sq_nonneg (d * c - d)]
  · rw [h0, h1, h2]
    have hz2 : Lstar + d * c - (Lstar + d) = d * (c - 1) := by ring
    have hz3 : Lstar + d * c^2 - (Lstar + d * c) = d * c * (c - 1) := by ring
    rw [hz2, hz3]
    have hdc : d * (c - 1) ≠ 0 := by
      intro hcon
      rcases mul_eq_zero.mp hcon with h' | h'
      · exact absurd h' hd
      · exact absurd (sub_eq_zero.mp h') hc
    field_simp

/-- **T3b — the Aitken window consistency**: on a true
geometric trajectory the c-estimate
(L_{n+2}−L_{n+1})/(L_{n+1}−L_n) equals c at every window —
measured disagreement falsifies the geometric model (the WSD
schedule does by design; this test is mandatory before
applying T3c/T3d). -/
theorem aitken_consistency (Lstar d c : ℝ)
    (L : ℕ → ℝ) (hL : ∀ i, L i = Lstar + d * c^(i:ℕ))
    (hdne : d ≠ 0) (hcne : c ≠ 0) (hc1 : c ≠ 1) :
    ∀ k : ℕ, (L (k+2) - L (k+1)) / (L (k+1) - L k) = c := by
  intro k
  rw [hL (k+2), hL (k+1), hL k]
  have e1 : Lstar + d * c^((k+2:ℕ)) - (Lstar + d * c^((k+1:ℕ)))
      = d * c^(k:ℕ) * (c - 1) * c := by
    have h1 : (k+2:ℕ) = (k:ℕ) + 2 := by omega
    have h2 : (k+1:ℕ) = (k:ℕ) + 1 := by omega
    rw [h1, h2, pow_add, pow_add, pow_two, pow_one]
    ring
  have e2 : Lstar + d * c^((k+1:ℕ)) - (Lstar + d * c^(k:ℕ))
      = d * c^(k:ℕ) * (c - 1) := by
    have h2 : (k+1:ℕ) = (k:ℕ) + 1 := by omega
    rw [h2, pow_add, pow_one]
    ring
  rw [e1, e2]
  have hdenom : d * c^(k:ℕ) * (c - 1) ≠ 0 := by
    intro hcon
    rcases mul_eq_zero.mp hcon with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hdne
      · exact absurd h'' (pow_ne_zero k hcne)
    · exact absurd (sub_eq_zero.mp h') hc1
  rw [show d * c^(k:ℕ) * (c - 1) * c = c * (d * c^(k:ℕ) * (c - 1)) from by ring]
  field_simp

/-- **T3c — the budget-gap sign is C-constant at equal
rates**: under the two-exponential model with equal decay
rates, the sign of L_m − L_s is CONSTANT in C: the whole
budget comparison reduces to the constant comparison
d_m·exp(−u·C₀) < d_s. -/
theorem budget_gap_sign_const (dM dS u C C0 : ℝ)
    (_hdM : 0 < dM) (_hdS : 0 < dS) :
    dM * Real.exp (u * (C - C0)) < dS * Real.exp (u * C)
      ↔ dM * Real.exp (-(u * C0)) < dS := by
  have hpos : (0:ℝ) < Real.exp (u * C) := Real.exp_pos _
  have hsplit : dM * Real.exp (u * (C - C0))
      = (dM * Real.exp (-(u * C0))) * Real.exp (u * C) := by
    have h1 : Real.exp (u * (C - C0)) = Real.exp (-(u * C0)) * Real.exp (u * C) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h1, mul_assoc]
  rw [hsplit]
  exact mul_lt_mul_iff_of_pos_right hpos



/-- **T3d (two-sided break-even)**: with merged-pool head start
d_M < d_S, contraction rate c ∈ (0,1), per-step rate κ, and
leaf-compute cost C₀, the merged trajectory beats scratch net of
leaf cost **iff** C₀ < κ·ln(d_S/d_M)/ln(1/c). The exponent is
−C₀/κ (leaf compute *consumed* from the budget), so the
break-even budget is positive. -/
theorem headstart_pays_iff (dM dS c kappa C0 : ℝ)
    (hdM : 0 < dM) (hdS : 0 < dS) (hdSdM : dM < dS) (hc : 0 < c) (hc1 : c < 1)
    (hk : 0 < kappa) :
    dM * c^(-(C0 / kappa)) < dS ↔ C0 < (Real.log (dS / dM) / Real.log (1/c)) * kappa := by
  have hsum : Real.log c + Real.log (1/c) = 0 := by
    have hcne : c ≠ 0 := ne_of_gt hc
    have h2 : Real.log (1/c) = Real.log 1 - Real.log c := Real.log_div (one_ne_zero) hcne
    rw [h2, Real.log_one, zero_sub]; ring
  have hlnc : Real.log c < 0 := by
    have h1 : Real.log c < Real.log 1 := Real.log_lt_log hc (by linarith : c < (1:ℝ))
    rw [Real.log_one] at h1; exact h1
  have hln1c : 0 < Real.log (1/c) := by linarith
  have hB : 0 < Real.log (dS / dM) :=
    Real.log_pos ((one_lt_div hdM).mpr hdSdM)
  -- core: c^{−t} < dS/dM ↔ t·ln(1/c) < B  [log mono, both ways by contraposition]
  have key : c^(-(C0/kappa)) < dS / dM ↔ C0/kappa * Real.log (1/c) < Real.log (dS/dM) := by
    constructor
    · intro h
      have := Real.log_lt_log (Real.rpow_pos_of_pos hc _) h
      rw [Real.log_rpow hc] at this
      rw [show -(C0/kappa) * Real.log c = C0/kappa * Real.log (1/c) from by
      have h0 : -(C0/kappa) * Real.log c + C0/kappa * Real.log c = 0 := by ring
      have h1 : C0/kappa * Real.log c + C0/kappa * Real.log (1/c) = 0 := by
        have := hsum; nlinarith [hsum]
      linarith] at this
      exact this
    · intro h
      by_contra hcon
      push Not at hcon
      have hge : Real.log (dS/dM) ≤ Real.log (c^(-(C0/kappa))) :=
        Real.log_le_log (by positivity) hcon
      rw [Real.log_rpow hc] at hge
      rw [show -(C0/kappa) * Real.log c = C0/kappa * Real.log (1/c) from by
      have h0 : -(C0/kappa) * Real.log c + C0/kappa * Real.log c = 0 := by ring
      have h1 : C0/kappa * Real.log c + C0/kappa * Real.log (1/c) = 0 := by
        have := hsum; nlinarith [hsum]
      linarith] at hge
      linarith
  constructor
  · intro h
    have h1 : c^(-(C0/kappa)) < dS / dM := by
      rw [lt_div_iff₀ hdM]
      linarith
    have h2 := (key.mp h1)
    -- h2: (C0/κ)·L < B  ⟹ C0 < κ·B/L
    -- goal: C0 < (B/L)·κ; have h2: (C0/κ)·L < B; L>0, κ>0
    have hrew : Real.log (dS/dM) / Real.log (1/c) * kappa
        = Real.log (dS/dM) * kappa / Real.log (1/c) := by
      rw [div_mul_eq_mul_div]
    rw [hrew, lt_div_iff₀ hln1c]
    -- now: C0*L < B*κ; from h2: (C0/κ)·L < B multiply by κ
    have hkey : C0 / kappa * Real.log (1/c) * kappa = C0 * Real.log (1/c) := by
      rw [div_mul_eq_mul_div]
      rw [show C0 * Real.log (1/c) / kappa * kappa = C0 * Real.log (1/c) from by
        field_simp]
    nlinarith [h2, hkey]
  · intro h
    -- C0 < κ·B/L ⟹ (C0/κ)·L < B
    have h2 : C0/kappa * Real.log (1/c) < Real.log (dS/dM) := by
      have h3 : C0 * Real.log (1/c) < Real.log (dS/dM) * kappa := by
        have h5 : C0 * Real.log (1/c)
            < (Real.log (dS/dM) / Real.log (1/c) * kappa) * Real.log (1/c) :=
          mul_lt_mul_of_pos_right h hln1c
        rw [div_mul_eq_mul_div] at h5
        rw [show Real.log (dS/dM) * kappa / Real.log (1/c) * Real.log (1/c)
            = Real.log (dS/dM) * kappa from by field_simp] at h5
        exact h5
      have hkey : C0 / kappa * Real.log (1/c) * kappa = C0 * Real.log (1/c) := by
        rw [div_mul_eq_mul_div]
        rw [show C0 * Real.log (1/c) / kappa * kappa = C0 * Real.log (1/c) from by
          field_simp]
      nlinarith [h3, hkey]
    have h1 := key.mpr h2
    have h3 : c^(-(C0/kappa)) * dM < dS := (lt_div_iff₀ hdM).mp h1
    linarith

end EqualBudget

end Hagi.Audit

/-!
# Audit-driven decision theorems

**`proj_descent_inner` + `proj_no_farther`**: the SafeQP descent —
the projection of g onto a closed convex conflict set C ∋ 0
satisfies ⟪g,d*⟫ ≥ ‖d*‖² and ‖g−d*‖ ≤ ‖g‖
(`norm_eq_iInf_iff_real_inner_le_zero`).

**`exp_jensen` + `gap_N_nonneg`**: for centered experts
z_a = z̄+δ_a with Σ_a δ_a = 0, Gap_N = (1/N)Σ_a log Σ_v p_v e^{δ_av}
≥ 0 — Jensen for exp + the centering swap. The general-N backbone
behind `Hagi.twoGap`.

**`anchor_recurrence`**: D_{t+1} ≤ (1−γ)D_t + ρs with 0 < γ ≤ 1
implies D_t ≤ (1−γ)^t·D₀ + ρs/γ — the finite-t form behind the
anchor cadence criterion.

**`ns_poly_bound`**: p(σ) = aσ+bσ³+cσ⁵ ≤ aσ on [0,1] whenever
b ≤ 0 and b+c ≤ 0. Since a = 3.4445 > 1 this is a growth-factor
bound, not a contraction; the NS convergence theorem is not
claimed.

**`amgm_batch_bound`**: cB + B_n·t₀/B ≥ 2√(c·B_n·t₀) — the core
of the optimal-batch law T(B) = S_min(1+B_n/B)(t₀+cB).

All empirical constants stay explicit hypotheses.
-/

open Finset Real InnerProductSpace

namespace Hagi.Audit

/-- Jensen for exp over a finitely-supported probability:
exp(Σ p δ) ≤ Σ p·exp(δ) for p ≥ 0 with Σ p = 1. -/
theorem exp_jensen {V : Type} [Fintype V] (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hsum : ∑ v, p v = 1) (δ : V → ℝ) :
    Real.exp (∑ v, p v * δ v) ≤ ∑ v, p v * Real.exp (δ v) := by
  have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h := hconv.map_sum_le (t := (Finset.univ : Finset V)) (w := p) (p := δ)
    (fun v _ => hp v) (by simpa using hsum) (fun v _ => Set.mem_univ _)
  simpa [smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul] using h

/-- **The N-expert ensemble gap is nonnegative**: with logits
z_a = z̄ + δ_a and centered deviations (Σ_a δ_a v = 0),
Gap_N = (1/N)Σ_a log Σ_v p_v e^{δ_av} ≥ 0: per-expert Jensen, then
the centering makes Σ_a Σ_v p_v δ_av = 0. The general-N backbone of
`Hagi.Ensemble.GapLaw` (the N=2 case is `twoGap_nonneg`); the
empirical input is only the centering. -/
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

/-- **The anchor drift recurrence**: D_{t+1} ≤ (1−γ)D_t + ρs with
0 < γ ≤ 1 implies D_t ≤ (1−γ)^t·D₀ + ρs/γ. The stationary bound ρs/γ
is the t → ∞ limit; the anchor cadence criterion s ≤ γε/ρ applies once
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

/-- **The NS polynomial bound**: p(σ) = aσ + bσ³ + cσ⁵ with the
coefficient signs (b ≤ 0, b + c ≤ 0) satisfies p(σ) ≤ aσ on [0,1].
With a = 3.4445 > 1 this is a growth-factor bound, not a
contraction; the Newton–Schulz contraction on an
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
# Audit: weak-formulation identities

**`nce_estimator_unbiased`**: Σ_v q(v)·(f(v)/q(v)) = Σ_v f(v) for
q > 0 — the importance-weighted per-sample correction is exact.

**`log_jensen_uniform`**: (1/K)Σ log Z_j ≤ log((1/K)Σ Z_j); the
reverse delta estimate needs χ²(p‖q) ≤ cK and is not claimed.

**`exp_tangent` + `waterfilling_optimal`**: with equalized
marginals and an equal budget, any feasible allocation costs at least
the water-filling one — optimality is derived from the convexity
tangent plus the budget identity.

**`head_start_timeshift`**: under geometric decay L−L* = Δ·c^t,
Lm(t+k) = Ls(t) whenever dm·c^k = ds: the merge head start is a time
shift of k = ln(Δs/Δm)/ln(c) steps.
-/

open Finset Real

namespace Hagi.Audit

section NCEUnbiased

/-- **The importance-weighted NCE estimator is unbiased**:
Σ_v q(v)·(f(v)/q(v)) = Σ_v f(v) for q > 0 — the expectation of the
per-sample estimator f(v)/q(v) under v ~ q is exactly Σ f. -/
theorem nce_estimator_unbiased {V : Type} [Fintype V]
    (q f : V → ℝ) (hq : ∀ v, q v ≠ 0) :
    ∑ v, q v * (f v / q v) = ∑ v, f v := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (hq v)]

end NCEUnbiased

section LogJensen

/-- **The ceGap Jensen direction**: the mean of the logs never exceeds
the log of the mean — (1/K)Σ log Z_j ≤ log((1/K)Σ Z_j) — via weighted
AM-GM and log monotonicity. The reverse delta estimate requires an
explicit small-χ² condition (not claimed). -/
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

/-- The tangent line of exp: e^a + e^a·(y−a) ≤ e^y. -/
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

/-- **Water-filling optimality** (KKT): for min Σ_i c_i·e^{−κ_i·b_i}
subject to Σ b_i = B, if the marginals equalize at a feasible b*
(c_i·κ_i·e^{−κ_i·b_i*} = λ), then every feasible b' satisfies
Σ c_i e^{−κ_i b'_i} ≥ Σ c_i e^{−κ_i·b_i*}. `hmarg` and `hfeas` are
hypotheses; such a `b*` is not constructed. -/
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

/-- **The merge head start as a time shift**: under geometric decay
L−L* = Δ·c^t (Δs > Δm > 0, 0 < c < 1), Lm(t+k) = Ls(t) whenever
dm·c^k = ds, i.e. k = ln(Δs/Δm)/ln(c): the merge buys k
scratch-equivalent steps at every point of the trajectory. -/
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
# Audit: controller binding, NS iteration, batch optimum

**`min_dist_to_vi` + `safeQP_descent`**: the minimizer of dist(·, g0)
over a convex C yields the variational inequality, hence both
descent guarantees ‖ds‖² ≤ ⟪g0, ds⟫ and ‖g0−ds‖ ≤ ‖g0‖.

**`ns_iter_bound`**: σ_{k+1} ≤ a·σ_k implies σ_k ≤ a^k·σ₀.

**`amgm_equality` + `amgm_uniqueness` + `batch_T_min`**: the AM-GM
batch law — equality holds exactly at B*² = B_n·t₀/c, equality
forces B = B*, and T(B) = (1+B_n/B)(t₀+cB) ≥ t₀ + c·B_n +
2√(c·B_n·t₀) uniformly with equality iff B = B*.
-/

open Finset Real InnerProductSpace

namespace Hagi.Audit

section NSIter

/-- **The NS iteration bound**: σ_{k+1} ≤ a·σ_k implies
σ_k ≤ a^k·σ₀ for every k — the per-step factor a (3.4445 for the NS
polynomial) compounds over the trajectory; a > 1 means growth, so
the bound is useful only on an invariant range where `ns_poly_bound`
gives the effective factor. -/
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

/-- **The AM-GM equality case**: at B*² = B_n·t₀/c the AM-GM bound is
tight. -/
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

/-- **The AM-GM uniqueness**: equality in the AM-GM batch bound forces
B² = B_n·t₀/c. -/
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

/-- **The batch throughput minimum**: T(B) = (1 + B_n/B)(t₀ + cB) ≥
t₀ + c·B_n + 2√(c·B_n·t₀) uniformly over B > 0, with equality exactly at
B = B* = √(B_n·t₀/c). -/
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

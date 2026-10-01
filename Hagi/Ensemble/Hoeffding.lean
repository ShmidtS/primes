/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.GapLaw
set_option linter.style.header false

/-!
# R56: T1a — the Hoeffding kernel (chord route)

The admission-criterion core (open since round-47): for a
pool of experts with probability weights p and logit
deviations d whose pairwise disagreement is bounded by M,
the mixture generating function obeys

  ΣΣ p_u p_v e^{d_u − d_v} ≤ cosh M,

with the centering AUTOMATIC (product weights make
E[d_u − d_v] = 0 identically). Via the twoGap identity of
`Hagi.Ensemble.GapLaw`, the Jensen gap of any
bounded-disagreement pool is at most ½·log cosh M.

Route: the chord inequality of exp (convexity on [−M, M]),
double-summed with the constant-factoring lemmas.

**Honest boundary**: the log-cosh → quadratic reduction
(½ log cosh M ≤ M²/4) and the Hoeffding tail form
P(gap − mean ≥ t) are not proven here; the admission
criterion uses the exact ½·log cosh M bound.
-/

open Finset Real

namespace Hagi

theorem exp_chord (x M : ℝ) (hM : 0 < M) (hx : -M ≤ x) (hx2 : x ≤ M) :
    Real.exp x ≤ (M - x) / (2 * M) * Real.exp (-M)
      + (x + M) / (2 * M) * Real.exp M := by
  have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  set a := (M - x) / (2 * M) with ha
  set b := (x + M) / (2 * M) with hb
  have haneg : 0 ≤ a := by apply div_nonneg <;> linarith
  have hbneg : 0 ≤ b := by apply div_nonneg <;> linarith
  have hsum : a + b = 1 := by
    rw [ha, hb]; field_simp; ring_nf
  have key := hconv.2 (Set.mem_univ (-M)) (Set.mem_univ M) haneg hbneg hsum
  have hcomb : a • (-M) + b • M = x := by
    simp only [smul_eq_mul]
    rw [ha, hb]; field_simp; ring_nf
  rw [hcomb] at key
  simp only [smul_eq_mul] at key
  exact key

theorem sum_pair_weights {V : Type} [Fintype V] (p : V → ℝ) (hsum : ∑ v, p v = 1) :
    ∑ u, ∑ v, p u * p v = 1 := by
  have h1 : ∀ u : V, ∑ v, p u * p v = p u * ∑ v, p v := by
    intro u
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  simp only [hsum, mul_one]
theorem sum_pair_diff_zero {V : Type} [Fintype V] (p d : V → ℝ) (hsum : ∑ v, p v = 1) :
    ∑ u, ∑ v, p u * p v * (d u - d v) = 0 := by
  -- expand inner: A·p_v − B·p_v split, then factor each double sum
  have h1 : ∑ u, ∑ v, p u * p v * (d u - d v)
      = ∑ u, ∑ v, (p u * d u) * p v - ∑ u, ∑ v, (p v * d v) * p u := by
    have hsplit : ∀ u v : V, p u * p v * (d u - d v)
        = (p u * d u) * p v - (p v * d v) * p u := fun u v => by ring
    have h2 : ∀ u : V, ∑ v, p u * p v * (d u - d v)
        = ∑ v, ((p u * d u) * p v - (p v * d v) * p u) := fun u =>
      Finset.sum_congr rfl (fun v _ => hsplit u v)
    have h3 : ∀ u : V, ∑ v, ((p u * d u) * p v - (p v * d v) * p u)
        = ∑ v, (p u * d u) * p v - ∑ v, (p v * d v) * p u := fun u =>
      sum_sub_distrib (fun v => (p u * d u) * p v) (fun v => (p v * d v) * p u)
    rw [Finset.sum_congr rfl (fun u _ => (h2 u).trans (h3 u)), Finset.sum_sub_distrib]
  rw [h1]
  have hfact1 : ∀ u : V, ∑ v, (p u * d u) * p v = (p u * d u) * ∑ v, p v := fun u =>
    (Finset.mul_sum (s := Finset.univ) (f := fun v => p v) (a := p u * d u)).symm
  have hfact2 : ∀ v : V, ∑ u, (p v * d v) * p u = (p v * d v) * ∑ u, p u := fun v =>
    (Finset.mul_sum (s := Finset.univ) (f := fun u => p u) (a := p v * d v)).symm
  rw [Finset.sum_congr rfl (fun u _ => hfact1 u), hsum]
  rw [show ∑ u, ∑ v, (p v * d v) * p u = ∑ v, ∑ u, (p v * d v) * p u from Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun v _ => hfact2 v), hsum]
  simp only [mul_one]
  rw [show ∑ v, p v * d v = ∑ u, p u * d u from Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [sub_self]
theorem sum_pair_const {V : Type} [Fintype V] (p : V → ℝ) (c : ℝ) (hsum : ∑ v, p v = 1) :
    ∑ u, ∑ v, p u * p v * c = c := by
  -- inner: Σ_v (p u * p v) * c = (p u * c) * 1
  have hinner : ∀ u : V, ∑ v, p u * p v * c = p u * c := by
    intro u
    have hterm : ∀ v : V, p u * p v * c = (p u * c) * p v := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v), ← Finset.mul_sum, hsum, mul_one]
  -- outer: Σ_u p u * c = c
  have hterm2 : ∀ u : V, p u * c = c * p u := fun u => mul_comm _ _
  rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_congr rfl (fun u _ => hterm2 u)]
  calc ∑ u, c * p u = c * ∑ u, p u := (Finset.mul_sum (s := Finset.univ) (f := fun u => p u) (a := c)).symm
    _ = c * 1 := by rw [hsum]
    _ = c := by ring


/-- **T1a (Hoeffding kernel, product form)**: bounded
pairwise disagreement M forces the mixture generating
function ≤ cosh M. Centering is automatic for product
weights. With the twoGap identity: gap ≤ ½·log cosh M —
the admission certificate for bounded-disagreement pools. -/
theorem sum2_mul {V : Type} [Fintype V] (f : V → V → ℝ) (c : ℝ) :
    ∑ u, ∑ v, c * f u v = c * (∑ u, ∑ v, f u v) := by
  have hinner : ∀ u : V, ∑ v, c * f u v = c * ∑ v, f u v := by
    intro u
    exact (Finset.mul_sum (s := Finset.univ) (f := fun v => f u v) (a := c)).symm
  rw [Finset.sum_congr rfl (fun u _ => hinner u), ← Finset.mul_sum]

theorem exp_prod_le_cosh {V : Type} [Fintype V] (p d : V → ℝ) (M : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (hM : 0 < M) (hD : ∀ u v, abs (d u - d v) ≤ M) :
    ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) ≤ Real.cosh M := by
  have hchord : ∀ u v, Real.exp (d u - d v)
      ≤ (M - (d u - d v)) / (2 * M) * Real.exp (-M)
        + ((d u - d v) + M) / (2 * M) * Real.exp M :=
    fun u v => exp_chord _ M hM
      (by have := hD u v; rw [abs_le] at this; linarith)
      (by have := hD u v; rw [abs_le] at this; linarith)
  have hzero := sum_pair_diff_zero p d hsum
  -- chord-sum = e^{-M}/2 + e^{M}/2 = cosh M via the three sum identities
  have hlhs : ∑ u, ∑ v, p u * p v * Real.exp (d u - d v)
      ≤ ∑ u, ∑ v, p u * p v * ((M - (d u - d v)) / (2 * M) * Real.exp (-M)
          + ((d u - d v) + M) / (2 * M) * Real.exp M) :=
    Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left (hchord u v) (mul_nonneg (hp u) (hp v))))
  -- split chord-sum into two scaled double sums
  have hsplit : ∀ u v : V, p u * p v * ((M - (d u - d v)) / (2 * M) * Real.exp (-M)
          + ((d u - d v) + M) / (2 * M) * Real.exp M)
      = (p u * p v * (M - (d u - d v))) / (2 * M) * Real.exp (-M)
        + (p u * p v * ((d u - d v) + M)) / (2 * M) * Real.exp M :=
    fun u v => by ring
  -- ΣΣ p p (M − x) = M  (constant − zero)
  have hM1 : ∑ u, ∑ v, p u * p v * (M - (d u - d v)) = M := by
    have hsplit : ∀ u v : V, p u * p v * (M - (d u - d v))
        = (p u * p v) * M - p u * p v * (d u - d v) := fun u v => by ring
    have hinner : ∀ u : V, ∑ v, p u * p v * (M - (d u - d v))
        = (∑ v, (p u * p v) * M) - (∑ v, p u * p v * (d u - d v)) := by
      intro u
      rw [Finset.sum_congr rfl (fun v _ => hsplit u v)]
      exact sum_sub_distrib (fun v => (p u * p v) * M) (fun v => p u * p v * (d u - d v))
    rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_sub_distrib]
    rw [sum_pair_const p M hsum, hzero, sub_zero]
  -- ΣΣ p p (x + M) = M
  have hM2 : ∑ u, ∑ v, p u * p v * ((d u - d v) + M) = M := by
    have hsplit : ∀ u v : V, p u * p v * ((d u - d v) + M)
        = p u * p v * (d u - d v) + (p u * p v) * M := fun u v => by ring
    have hinner : ∀ u : V, ∑ v, p u * p v * ((d u - d v) + M)
        = (∑ v, p u * p v * (d u - d v)) + (∑ v, (p u * p v) * M) := by
      intro u
      rw [Finset.sum_congr rfl (fun v _ => hsplit u v)]
      rw [Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_add_distrib]
    rw [hzero, sum_pair_const p M hsum, zero_add]
  -- scaled: (ΣΣ…)/(2M) = M/(2M) = 1/2
  have hhalf : (1/2) * M / M = 1/2 := by field_simp
  -- final: chord-sum = (M/(2M))e^{−M} + (M/(2M))e^{M} = (e^{−M}+e^{M})/2
  -- chord-sum = e^{-M}·(1/2) + e^{M}·(1/2)
  have hfinal : ∑ u, ∑ v, p u * p v * ((M - (d u - d v)) / (2 * M) * Real.exp (-M)
          + ((d u - d v) + M) / (2 * M) * Real.exp M)
      = (Real.exp (-M) + Real.exp M) / 2 := by
    -- write the summand as A•x + B•y with constants A = e^{-M}/(2M), B = e^{M}/(2M)
    have hterm : ∀ u v : V, p u * p v * ((M - (d u - d v)) / (2 * M) * Real.exp (-M)
          + ((d u - d v) + M) / (2 * M) * Real.exp M)
        = ((1 / (2 * M)) * Real.exp (-M)) * (p u * p v * (M - (d u - d v)))
          + ((1 / (2 * M)) * Real.exp M) * (p u * p v * ((d u - d v) + M)) :=
      fun u v => by
        rw [div_eq_inv_mul]
        field_simp
    -- step 1: rewrite the double sum termwise
    rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => hterm u v))]
    -- step 2: split the inner add
    have hsplit : ∀ u : V, ∑ v, (((1 / (2 * M)) * Real.exp (-M)) * (p u * p v * (M - (d u - d v)))
            + ((1 / (2 * M)) * Real.exp M) * (p u * p v * ((d u - d v) + M)))
        = ((1 / (2 * M)) * Real.exp (-M)) * (∑ v, (p u * p v * (M - (d u - d v))))
          + ((1 / (2 * M)) * Real.exp M) * (∑ v, (p u * p v * ((d u - d v) + M))) := by
      intro u
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun u _ => hsplit u)]
    -- step 3: factor constants out of both outer sums (sum2_mul pattern)
    have hout : (∑ u, ((1 / (2 * M)) * Real.exp (-M)) * (∑ v, (p u * p v * (M - (d u - d v))))
          + (∑ u, ((1 / (2 * M)) * Real.exp M) * (∑ v, (p u * p v * ((d u - d v) + M)))))
        = ((1 / (2 * M)) * Real.exp (-M)) * (∑ u, ∑ v, p u * p v * (M - (d u - d v)))
          + ((1 / (2 * M)) * Real.exp M) * (∑ u, ∑ v, p u * p v * ((d u - d v) + M)) := by
      have h1 : (∑ u, ((1 / (2 * M)) * Real.exp (-M)) * (∑ v, (p u * p v * (M - (d u - d v)))))
          = ((1 / (2 * M)) * Real.exp (-M)) * (∑ u, ∑ v, p u * p v * (M - (d u - d v))) := by
        rw [← Finset.mul_sum]
      have h2 : (∑ u, ((1 / (2 * M)) * Real.exp M) * (∑ v, (p u * p v * ((d u - d v) + M))))
          = ((1 / (2 * M)) * Real.exp M) * (∑ u, ∑ v, p u * p v * ((d u - d v) + M)) :=
        (Finset.mul_sum (s := Finset.univ)
          (f := fun u => ∑ v, p u * p v * ((d u - d v) + M))
          (a := (1 / (2 * M)) * Real.exp M)).symm
      rw [h1, h2]
    rw [Finset.sum_add_distrib]
    have h3 : (∑ u, (1 / (2 * M)) * Real.exp (-M) * ∑ v, p u * p v * (M - (d u - d v)))
          + (∑ u, (1 / (2 * M)) * Real.exp M * ∑ v, p u * p v * (d u - d v + M))
        = ((1 / (2 * M)) * Real.exp (-M)) * (∑ u, ∑ v, p u * p v * (M - (d u - d v)))
          + ((1 / (2 * M)) * Real.exp M) * (∑ u, ∑ v, p u * p v * ((d u - d v) + M)) := by
      have ha : (∑ u, (1 / (2 * M)) * Real.exp (-M) * ∑ v, p u * p v * (M - (d u - d v)))
          = ((1 / (2 * M)) * Real.exp (-M)) * (∑ u, ∑ v, p u * p v * (M - (d u - d v))) :=
        (Finset.mul_sum (s := Finset.univ)
          (f := fun u => ∑ v, p u * p v * (M - (d u - d v)))
          (a := (1 / (2 * M)) * Real.exp (-M))).symm
      have hb : (∑ u, (1 / (2 * M)) * Real.exp M * ∑ v, p u * p v * (d u - d v + M))
          = ((1 / (2 * M)) * Real.exp M) * (∑ u, ∑ v, p u * p v * ((d u - d v) + M)) :=
        (Finset.mul_sum (s := Finset.univ)
          (f := fun u => ∑ v, p u * p v * (d u - d v + M))
          (a := (1 / (2 * M)) * Real.exp M)).symm
      rw [ha, hb]
    rw [h3, hM1, hM2]
    field_simp
  calc ∑ u, ∑ v, p u * p v * Real.exp (d u - d v)
      ≤ ∑ u, ∑ v, p u * p v * ((M - (d u - d v)) / (2 * M) * Real.exp (-M)
          + ((d u - d v) + M) / (2 * M) * Real.exp M) := hlhs
    _ = (Real.exp (-M) + Real.exp M) / 2 := hfinal
    _ = Real.cosh M := by
        rw [Real.cosh_eq M]
        ring
theorem log_cosh_le (M : ℝ) : Real.log (Real.cosh M) ≤ M ^ 2 / 2 := by
  have hc : Real.cosh M ≤ Real.exp (M ^ 2 / 2) := cosh_le_exp_half_sq M
  have hpos : 0 < Real.cosh M := Real.cosh_pos M
  have hlog : Real.log (Real.cosh M) ≤ Real.log (Real.exp (M ^ 2 / 2)) :=
    Real.log_le_log hpos (cosh_le_exp_half_sq M)
  rw [Real.log_exp] at hlog
  exact hlog

theorem half_log_cosh_le (M : ℝ) : Real.log (Real.cosh M) / 2 ≤ M ^ 2 / 4 := by
  have h := log_cosh_le M
  linarith [div_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 4)]

/-- **Full quadratic admission bound**: the Jensen gap of a
pool with pairwise disagreement ≤ M is at most M²/4 —
composition of exp_prod_le_cosh (cosh bound) with the
Mathlib cosh_le_exp_half_sq quadratic reduction. -/
theorem twoGap_bounded (V : Type) [Fintype V] (p d : V → ℝ) (M : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (hM : 0 < M) (hD : ∀ u v, abs (d u - d v) ≤ M) :
    Hagi.twoGap p d ≤ M ^ 2 / 4 := by
  have hcosh := Hagi.exp_prod_le_cosh p d M hp hsum hM hD
  have hquad : Real.cosh M ≤ Real.exp (M ^ 2 / 2) := cosh_le_exp_half_sq M
  have hle : ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) ≤ Real.exp (M ^ 2 / 2) :=
    le_trans hcosh hquad
  -- twoGap = ½ log (sum) ≤ ½ log (exp(M²/2)) = M²/4
  have hpos : 0 < ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) := by
    -- every term ≥ p_u p_v · e^{−M}, so the sum ≥ e^{−M}·ΣΣ p p = e^{−M} > 0
    have hone : ∑ u, ∑ v, p u * p v = 1 := Hagi.sum_pair_weights p hsum
    have hge : ∀ (u : V) (v : V),
        p u * p v * Real.exp (-M) ≤ p u * p v * Real.exp (d u - d v) := by
      intro u v
      have hd : -M ≤ d u - d v := by
        have := hD u v
        rw [abs_le] at this
        linarith
      have hexp : Real.exp (-M) ≤ Real.exp (d u - d v) := Real.exp_le_exp_of_le hd
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (hp u) (hp v))
    have hlb : (∑ u, ∑ v, p u * p v) * Real.exp (-M)
        ≤ ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) := by
      calc (∑ u, ∑ v, p u * p v) * Real.exp (-M)
          = ∑ u, ∑ v, p u * p v * Real.exp (-M) := by
              rw [mul_comm, ← Hagi.sum2_mul (f := fun u v => p u * p v) (c := Real.exp (-M))]
              exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by ring))
        _ ≤ ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) := by
          refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hge u v))
    rw [hone, one_mul] at hlb
    exact lt_of_lt_of_le (by positivity : (0:ℝ) < Real.exp (-M)) hlb
  have hlogmono : Real.log (∑ u, ∑ v, p u * p v * Real.exp (d u - d v))
      ≤ Real.log (Real.exp (M ^ 2 / 2)) := Real.log_le_log hpos hle
  rw [Real.log_exp] at hlogmono
  show (1/2) * Real.log (∑ u, ∑ v, p u * p v * Real.exp (d u - d v)) ≤ M ^ 2 / 4
  nlinarith [hlogmono]

/-- **The pre-gate skip certificate (R59)**: if the pool's
disagreement diameter M obeys M²/4 < ε (the T1a quadratic
gate), then the entire ensemble gain available from ANY merge
of this pool is below ε — skipping the GPU merge cycle loses
strictly less than ε nats. The controller decision SKIP is
certified by one scalar measurement (M). -/
theorem merge_skip_certificate (V : Type) [Fintype V] [Nonempty V] (p d : V → ℝ) (M eps : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (hM : 0 < M) (hD : ∀ u v, abs (d u - d v) ≤ M)
    (hgate : M ^ 2 / 4 < eps) :
    Hagi.twoGap p d < eps := by
  have hb := Hagi.twoGap_bounded V p d M hp hsum hM hD
  linarith

/-- **The materialized-gain ceiling through transport**: the
ensemble gain that actually reaches the output through a
transport channel of efficiency η ∈ [0,1] is at most η·G —
composing the exact gap (≤ ½log cosh M) with the η-transport
bound. The controller's effective value of a merge is
η·twoGap, and the admission gate must compare it — not the
raw gap — against ε. -/
theorem merge_value_ceiling (V : Type) [Fintype V] [Nonempty V] (p d : V → ℝ) (M eta : ℝ)
    (hp : ∀ v, 0 < p v) (hsum : ∑ v, p v = 1)
    (hM : 0 < M) (hD : ∀ u v, abs (d u - d v) ≤ M)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    eta * Hagi.twoGap p d ≤ M ^ 2 / 4 := by
  have hb : Hagi.twoGap p d ≤ M ^ 2 / 4 :=
    Hagi.twoGap_bounded V p d M (fun v => le_of_lt (hp v)) hsum hM hD
  have hgap0 : 0 ≤ Hagi.twoGap p d := Hagi.twoGap_nonneg hp hsum
  nlinarith [hb, hgap0, heta, heta1]

/-- **Pair generating function factorization**: the double pair sum factorizes into the product of the marginal generating functions — the first step of the sharp M2/8 route (the mu-canceling product bound, in progress). -/
theorem pair_factor {V : Type} [Fintype V] (p d : V → ℝ) :
    ∑ u, ∑ v, p u * p v * Real.exp (d u - d v)
      = (∑ u, p u * Real.exp (d u)) * (∑ v, p v * Real.exp (-(d v))) := by
  have hsplit : ∀ u v : V, p u * p v * Real.exp (d u - d v)
      = (p u * Real.exp (d u)) * (p v * Real.exp (-(d v))) := fun u v => by
    rw [show Real.exp (d u - d v) = Real.exp (d u) * Real.exp (-(d v)) from by
      rw [← Real.exp_add, show d u + -(d v) = d u - d v from by ring]]
    ring
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => hsplit u v))]
  exact Eq.symm (Fintype.sum_mul_sum (fun u => p u * Real.exp (d u))
    (fun v => p v * Real.exp (-(d v))))

/-- The chord-sum helper: the weighted chord value with mean μ. -/
theorem chord_weighted {V : Type} [Fintype V] (p d : V → ℝ) (D : ℝ)
    (hsum : ∑ v, p v = 1) :
    ∑ v, p v * ((D - d v) / (2 * D)) = (D - (∑ v, p v * d v)) / (2 * D) ∧
    ∑ v, p v * ((d v + D) / (2 * D)) = ((∑ v, p v * d v) + D) / (2 * D) := by
  constructor
  · have hsplit : ∀ v : V, p v * ((D - d v) / (2 * D))
        = (p v * D) / (2 * D) - (p v * d v) / (2 * D) := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_sub_distrib]
    rw [show (∑ v, (p v * D) / (2 * D)) = (∑ v, p v * D) / (2 * D) from by
      rw [← Finset.sum_div]]
    rw [show (∑ v, (p v * d v) / (2 * D)) = (∑ v, p v * d v) / (2 * D) from by
      rw [← Finset.sum_div]]
    rw [show (∑ v, p v * D) = D * (∑ v, p v) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => mul_comm (p v) D)]
    rw [hsum, mul_one]
    field_simp
  · have hsplit : ∀ v : V, p v * ((d v + D) / (2 * D))
        = (p v * d v) / (2 * D) + (p v * D) / (2 * D) := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_add_distrib]
    rw [show (∑ v, (p v * D) / (2 * D)) = (∑ v, p v * D) / (2 * D) from by
      rw [← Finset.sum_div]]
    rw [show (∑ v, (p v * d v) / (2 * D)) = (∑ v, p v * d v) / (2 * D) from by
      rw [← Finset.sum_div]]
    rw [show (∑ v, p v * D) = D * (∑ v, p v) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => mul_comm (p v) D)]
    rw [hsum, mul_one]
    field_simp

variable {k : Type} [Fintype k] [Nonempty k] [DecidableEq k]

/-- **Domain-orthogonality guarantees the ensemble gap**
(the tree-of-domains architecture theorem): if some token
pair (u,v) carries pairwise disagreement |d_u − d_v| ≥ δ
with positive softmax mass q = p_u·p_v — the signature of
orthogonal domain specialists (the A-expert specializes on
domain-A tokens while the B-expert stays at baseline) — the
Jensen gap is bounded BELOW:

  twoGap ≥ ½·log(1 + q·(cosh δ − 1)) > 0 for δ > 0.

Contrapositive = the R66/67 diagnosis made mathematical:
siblings on the SAME mix drive every pairwise disagreement
to 0 (collapse); siblings on ORTHOGONAL domains keep a
guaranteed floor. The correct HAGI tree is
sibling-per-domain, not sibling-per-seed. -/
theorem domain_disagreement_floor (p d : k → ℝ)
    (hp : ∀ v, 0 < p v) (hsum : ∑ v, p v = 1)
    (u v : k) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdis : delta ≤ abs (d u - d v)) :
    Real.log (1 + p u * p v * (Real.cosh delta - 1)) / 2
      ≤ Hagi.twoGap p d := by
  -- cosh lower bound on the (u,v) term
  have hdeltaabs : abs delta = delta := abs_of_nonneg hdelta
  have hmono : Real.cosh delta ≤ Real.cosh (d u - d v) := by
    apply Real.cosh_le_cosh.mpr
    rw [hdeltaabs]
    exact hdis
  -- isolate the (u,v) term inside the double cosh-sum
  have hinner : p u * p v * Real.cosh (d u - d v)
      ≤ ∑ b, p u * p b * Real.cosh (d u - d b) :=
    Finset.single_le_sum (f := fun b => p u * p b * Real.cosh (d u - d b))
      (fun b _ => mul_nonneg (mul_nonneg (hp u).le (hp b).le) (Real.cosh_pos _).le)
      (Finset.mem_univ v)
  have houter : p u * p v * Real.cosh (d u - d v)
      ≤ ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b) := by
    calc p u * p v * Real.cosh (d u - d v)
        ≤ ∑ b, p u * p b * Real.cosh (d u - d b) := hinner
      _ ≤ ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b) := by
          exact Finset.single_le_sum
            (f := fun a => ∑ b, p a * p b * Real.cosh (d a - d b))
            (fun a _ => Finset.sum_nonneg fun b _ =>
              mul_nonneg (mul_nonneg (hp a).le (hp b).le) (Real.cosh_pos _).le)
            (Finset.mem_univ u)
  -- the total sum ≥ 1 + q(cosh δ − 1):  split off the (u,v) mass
  have hsum1 : ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)
      = (p u * p v * Real.cosh (d u - d v))
        + (∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)
            - p u * p v * Real.cosh (d u - d v)) := by ring
  -- split the double sum into the (u,v) term and the rest
  have hsplituv : ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)
      = p u * p v * Real.cosh (d u - d v)
        + (∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b * Real.cosh (d a - d b))
        + ∑ b ∈ Finset.univ.erase v, p u * p b * Real.cosh (d u - d b) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun a => ∑ b, p a * p b * Real.cosh (d a - d b)) (Finset.mem_univ u)]
    rw [show ∑ b, p u * p b * Real.cosh (d u - d b)
        = (∑ b ∈ Finset.univ.erase v, p u * p b * Real.cosh (d u - d b)
          + p u * p v * Real.cosh (d u - d v)) from by
      rw [← Finset.sum_erase_add Finset.univ
        (fun b => p u * p b * Real.cosh (d u - d b)) (Finset.mem_univ v)]]
    ring
  -- the rest terms: cosh ≥ 1 everywhere
  have hrest1 : ∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b
      ≤ ∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b * Real.cosh (d a - d b) := by
    refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
    calc p a * p b = p a * p b * 1 := by ring
      _ ≤ p a * p b * Real.cosh (d a - d b) :=
          mul_le_mul_of_nonneg_left (one_le_cosh _) (mul_nonneg (hp a).le (hp b).le)
  have hrest2 : ∑ b ∈ Finset.univ.erase v, p u * p b
      ≤ ∑ b ∈ Finset.univ.erase v, p u * p b * Real.cosh (d u - d b) := by
    refine Finset.sum_le_sum (fun b _ => ?_)
    calc p u * p b = p u * p b * 1 := by ring
      _ ≤ p u * p b * Real.cosh (d u - d b) :=
          mul_le_mul_of_nonneg_left (one_le_cosh _) (mul_nonneg (hp u).le (hp b).le)
  -- the total weight identity split the same way
  have hwsplit : ∑ a, ∑ b, p a * p b
      = p u * p v
        + (∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b)
        + ∑ b ∈ Finset.univ.erase v, p u * p b := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun a => ∑ b, p a * p b) (Finset.mem_univ u)]
    rw [show ∑ b, p u * p b
        = (∑ b ∈ Finset.univ.erase v, p u * p b + p u * p v) from by
      rw [← Finset.sum_erase_add Finset.univ
        (fun b => p u * p b) (Finset.mem_univ v)]]
    ring
  have hpairsum : ∑ a, ∑ b, p a * p b = 1 := Hagi.sum_pair_weights p hsum
  -- assemble: sum ≥ q·coshδ + (1 − q), purely by linear arithmetic on atoms
  have hlower : 1 + p u * p v * (Real.cosh delta - 1)
      ≤ ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b) := by
    have huv' : p u * p v * Real.cosh delta ≤ p u * p v * Real.cosh (d u - d v) :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg (hp u).le (hp v).le)
    have hw : (1:ℝ) = p u * p v
        + (∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b)
        + ∑ b ∈ Finset.univ.erase v, p u * p b := by
      rw [← hpairsum, ← hwsplit]
    -- normalize hsplituv into the same shape and finish by linear arithmetic
    have hsplit' : ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)
        = p u * p v * Real.cosh (d u - d v)
        + (∑ a ∈ Finset.univ.erase u, ∑ b, p a * p b * Real.cosh (d a - d b))
        + ∑ b ∈ Finset.univ.erase v, p u * p b * Real.cosh (d u - d b) := by
      rw [← hsplituv]
    nlinarith [huv', hrest1, hrest2, hw, hsplit']
  -- convert to twoGap via the cosh identity
  have hcosh := Hagi.twoGap_cosh (p := p) (d := d)
  unfold Hagi.twoGap
  -- log monotone + positivity, then halve
  have hpossum : (0:ℝ) < ∑ a, ∑ b, p a * p b * Real.exp (d a - d b) := by
    obtain ⟨w⟩ := ‹Nonempty k›
    have hge : (0:ℝ) < p w * p w * Real.exp (d w - d w) := by
      have hc : (0:ℝ) < Real.exp (d w - d w) := Real.exp_pos _
      exact mul_pos (mul_pos (hp w) (hp w)) hc
    have hle : p w * p w * Real.exp (d w - d w)
        ≤ ∑ a, ∑ b, p a * p b * Real.exp (d a - d b) := by
      calc p w * p w * Real.exp (d w - d w)
          ≤ ∑ b, p w * p b * Real.exp (d w - d b) :=
            Finset.single_le_sum (f := fun b => p w * p b * Real.exp (d w - d b))
              (fun b _ => mul_nonneg (mul_nonneg (hp w).le (hp b).le) (Real.exp_pos _).le)
              (Finset.mem_univ w)
        _ ≤ ∑ a, ∑ b, p a * p b * Real.exp (d a - d b) :=
            Finset.single_le_sum
              (f := fun a => ∑ b, p a * p b * Real.exp (d a - d b))
              (fun a _ => Finset.sum_nonneg fun b _ =>
                mul_nonneg (mul_nonneg (hp a).le (hp b).le) (Real.exp_pos _).le)
              (Finset.mem_univ w)
    linarith
  -- back to exp form via hcosh
  have hposarg : (0:ℝ) < 1 + p u * p v * (Real.cosh delta - 1) := by
    have h1 : (0:ℝ) ≤ Real.cosh delta - 1 := by linarith [one_le_cosh delta]
    have h2 : (0:ℝ) ≤ p u * p v * (Real.cosh delta - 1) :=
      mul_nonneg (mul_nonneg (hp u).le (hp v).le) h1
    linarith
  -- chain in cosh form then convert
  have hcosheq : ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)
      = ∑ a, ∑ b, p a * p b * Real.exp (d a - d b) := hcosh.symm
  have hposcosh : (0:ℝ) < ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b) := by
    have := hcosheq
    calc (0:ℝ) < ∑ a, ∑ b, p a * p b * Real.exp (d a - d b) := hpossum
      _ = ∑ a, ∑ b, p a * p b * Real.cosh (d a - d b) := hcosheq.symm
  have hlogmono : Real.log (1 + p u * p v * (Real.cosh delta - 1))
      ≤ Real.log (∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)) :=
    Real.log_le_log hposarg hlower
  calc Real.log (1 + p u * p v * (Real.cosh delta - 1)) / 2
      = (1/2) * Real.log (1 + p u * p v * (Real.cosh delta - 1)) := by ring
    _ ≤ (1/2) * Real.log (∑ a, ∑ b, p a * p b * Real.cosh (d a - d b)) :=
        mul_le_mul_of_nonneg_left hlogmono (by norm_num)
    _ = Real.log (∑ a, ∑ b, p a * p b * Real.exp (d a - d b)) / 2 := by
        rw [hcosheq]
        ring
  -- the calc chain lands in a,b-binders; the goal is the u,v-spelling:
  rw [show 1 / 2 * Real.log (∑ u, ∑ v, p u * p v * Real.exp (d u - d v))
      = Real.log (∑ u, ∑ v, p u * p v * Real.exp (d u - d v)) / 2 from by ring]

end Hagi

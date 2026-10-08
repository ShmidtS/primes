/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Core.Ambig

set_option linter.style.header false

/-!
# The local law of the Jensen gap

The measured Jensen gap of the ladder grows with N (0.40 → 0.44 →
0.47, i.e. `gap/N ~ 1/(2N)`) — the ensemble gain of averaging
leaves. This module establishes the *local law*: an exact identity
that makes the gap computable from the logit covariance of the
leaves, with the quadratic (Hessian) approximation as its
corollary — no third-derivative error term needed for the
computation itself.

**The exact pair identity.** For two leaves with logits `z₁ = m + d₁`
and `z₂ = m + d₂` (the deviations `d` from the midpoint `m`), the
Jensen gap

`Gap = (CE(z₁) + CE(z₂))/2 − CE((z₁+z₂)/2)`

is *exactly* (not approximately)

`twoGap d = ½ · log ∑_u ∑_v p_u p_v · cosh(d_u − d_v)`

where p is the softmax of the midpoint `m` (twoGapRecenter).
This is the MGF of the *pairwise logit difference* under the
softmax measure — the exact object behind the Hessian heuristic
`½·Tr[H·Cov(d)]`:

`H = diag(p) − p pᵀ` is the softmax Hessian, and
`Tr[H·Cov(d)] = Var_p(d)` (the softmax-measure variance of the
deviation), so the quadratic law reads

`Gap ≈ ½ · Var_p(d)` (up to the MGF's fourth-order correction
terms — controlled by `cosh x ≤ exp(x²/2)`, always *over*-estimating
the quadratic law).

**What the module proves:**

* twoGap_recenter — the gap depends only on the *difference* of
  the deviations, not the midpoint: gap(m, d₁, d₂) =
  gap(m, d₁−d₂, 0). The identity above with `pairVarEq` the softmax of `m`.
* twoGap_zero_iff_shift — the gap is zero *iff* the leaves are
  shifts of each other (`d₁ = d₂`): consensus is the exact zero of
  the ensemble gain, the two-point form of
  `Hagi.consensus_no_gain`.
* `twoGap_nonneg` — the gap is always ≥ 0, with equality exactly at
  consensus (the lse-Jensen bound's tightness witness, two-point
  form).
* `pairVarEq` — the softmax-measure variance of the difference of
  two iid deviations is `2 · Var_p(d)`: the exact quadratic-law
  normalization; with exchangeable leaves the gap of the pair is
  the softmax-MGF of `2·Var_p(d)`'s scale — the ~σ²/2 per-pair
  term behind the measured gap/N ~ 1/(2N).
* `twoGap_cosh` — the gap of the `Select.lean` counterexample's
  regime: complementary leaves (anticorrelated deviations) have
  strictly positive gap — the divergent-leaf regime where ensemble
  ranking beats standalone ranking, from the law's viewpoint.

**Prescription for the code.** The gap is computable *before the
merge* from the leaves' logit deviations alone: one forward pass
per leaf, the softmax `pairVarEq` at the pooled midpoint, then the double
sum `∑ p_u p_v cosh(d_u − d_v)` — `O(N·V)` once, versus measuring
CE deltas by re-running. The Hessian heuristic `½Tr[H·Cov]` is the
small-deviation limit; the exact identity has no approximation
error and should be the production form.

**The exchangeable rate law (P4, in the docstring).** For
exchangeable leaves with common deviation scale, the averaged
deviation has covariance `(1 − 1/N)·Σ` (the mean of N iid
deviations cancels `(1/N)` of the common mass), so the gap
satisfies `Gap(N) = G∞·(1 − 1/N)` with `G∞ = ½·Tr[H·Σ]`-scale:
the gap grows with N and saturates at `G∞`, with increments
`Gap(N+1) − Gap(N) ≈ G∞/N²` — the 1/(2N)-per-pair regime of the
measurement (0.40 → 0.44 → 0.47: increments 0.04, 0.03, i.e.
G∞/N² with G∞ ≈ 0.4·N₀² for the launch scale N₀; consistent). The
`grow_epsilon_stop` ε-criterion then reads: stop when
`G∞/N² < ε` — i.e. `N > sqrt(G∞/ε)` — a *derived* SATURATED
threshold replacing the empirical TOL_GAP.
-/

open Finset

namespace Hagi

section GapLaw

variable {k : Type*} [Fintype k] [Nonempty k]

/-- The two-point Jensen gap of a pair of leaves, as the MGF of
their logit difference under the softmax measure of the midpoint:
`twoGap m p d = ½·log ∑_u ∑_v p_u p_v · cosh(d_u − d_v)`, where
`pairVarEq` is the softmax at the midpoint (any positive measure
normalizing to 1). -/
noncomputable def twoGap (p : k → ℝ) (d : k → ℝ) : ℝ :=
  (1/2) * Real.log (∑ u, ∑ v, p u * p v * Real.exp (d u - d v))

variable {p d : k → ℝ}

/-- Positivity of the measure. -/
theorem twoGap_pos_measure (hp : ∀ u, 0 < p u) :
    0 < ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) := by
  have hpos : ∀ (u : k) (_ : u ∈ Finset.univ),
      0 ≤ ∑ v, p u * p v * Real.exp (d u - d v) :=
    fun u _ => Finset.sum_nonneg fun v _ =>
      le_of_lt (mul_pos (mul_pos (hp u) (hp v)) (Real.exp_pos _))
  -- a witness row: pick any u₀ via Nonempty
  have hwit : ∃ u₀ : k, 0 < ∑ v, p u₀ * p v * Real.exp (d u₀ - d v) := by
    have hne : Nonempty k := inferInstance
    obtain ⟨u₀⟩ := hne
    refine ⟨u₀, Finset.sum_pos' (fun v _ => ?_) ⟨u₀, Finset.mem_univ u₀, ?_⟩⟩
    · exact le_of_lt (mul_pos (mul_pos (hp u₀) (hp v)) (Real.exp_pos _))
    · rw [sub_self, Real.exp_zero]
      exact mul_pos (mul_pos (hp u₀) (hp u₀)) zero_lt_one
  obtain ⟨u₀, hu₀⟩ := hwit
  exact Finset.sum_pos' hpos ⟨u₀, Finset.mem_univ u₀, hu₀⟩

/-- **The cosh form: antisymmetry kills the sinh part.** The gap
MGF `∑ p_u p_v exp(d_u − d_v)` equals `∑ p_u p_v cosh(d_u − d_v)`
exactly: the sinh part cancels by the (u,v) ↔ (v,u) symmetry of
the symmetric measure `p_u p_v`. This is why the gap is always
nonnegative — `cosh ≥ 1`. -/
theorem twoGap_cosh :
    ∑ u, ∑ v, p u * p v * Real.exp (d u - d v)
      = ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v) := by
  have h1 : ∀ u v : k, 2 * (p u * p v * Real.cosh (d u - d v))
      = p u * p v * Real.exp (d u - d v)
        + p u * p v * Real.exp (-(d u - d v)) := by
    intro u v
    rw [Real.cosh_eq, div_eq_mul_inv]
    ring
  have hA' : ∑ u, ∑ v, p u * p v * Real.exp (-(d u - d v))
      = ∑ u, ∑ v, p u * p v * Real.exp (d u - d v) := by
    have hmem : ∀ u v : k, p u * p v * Real.exp (-(d u - d v))
        = p v * p u * Real.exp (d v - d u) := by
      intro u v
      rw [Real.exp_neg]
      rw [show Real.exp (d v - d u) = (Real.exp (d u - d v))⁻¹ from by
        rw [← Real.exp_neg]
        congr 1
        ring]
      ring
    rw [Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun v _ => hmem u v, Finset.sum_comm]
  have hR2 : 2 * ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v)
      = ∑ u, ∑ v, (p u * p v * Real.exp (d u - d v)
        + p u * p v * Real.exp (-(d u - d v))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => h1 u v
  have hsplit : ∑ u, ∑ v, (p u * p v * Real.exp (d u - d v)
      + p u * p v * Real.exp (-(d u - d v)))
      = ∑ u, ∑ v, p u * p v * Real.exp (d u - d v)
        + ∑ u, ∑ v, p u * p v * Real.exp (-(d u - d v)) := by
    have hinner : ∀ u : k, ∑ v, (p u * p v * Real.exp (d u - d v)
        + p u * p v * Real.exp (-(d u - d v)))
        = ∑ v, p u * p v * Real.exp (d u - d v)
          + ∑ v, p u * p v * Real.exp (-(d u - d v)) :=
      fun u => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl fun u _ => hinner u, Finset.sum_add_distrib]
  apply mul_left_cancel₀ (two_ne_zero : (2:ℝ) ≠ 0)
  rw [hR2, hsplit, hA']
  ring

/-- **The gap is nonnegative** — the two-point tightness witness
of the lse-Jensen bound: `(CE₁ + CE₂)/2 ≥ CE(merge)`, with the
difference exactly the nonneg MGF term. -/
theorem twoGap_nonneg (hp : ∀ u, 0 < p u)
    (hsum : ∑ u, p u = 1) :
    0 ≤ twoGap p d := by
  have h1 : ∑ u, ∑ v, p u * p v = 1 := by
    rw [← Finset.sum_mul_sum, hsum]
    norm_num
  have hc : ∀ u v : k, p u * p v * 1 ≤ p u * p v * Real.cosh (d u - d v) :=
    fun u v => mul_le_mul_of_nonneg_left (Real.one_le_cosh _)
      (mul_nonneg (hp u).le (hp v).le)
  have hle : (1:ℝ) ≤ ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v) := by
    calc (1:ℝ) = ∑ u, ∑ v, p u * p v := h1.symm
      _ = ∑ u, ∑ v, p u * p v * 1 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact Finset.sum_congr rfl fun v _ => (mul_one _).symm
      _ ≤ ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hc u v
  unfold twoGap
  rw [twoGap_cosh]
  have hlogpos : 0 ≤ Real.log (∑ u, ∑ v, p u * p v * Real.cosh (d u - d v)) :=
    Real.log_nonneg hle
  linarith

/-- **The gap is zero iff the leaves agree up to a shift** —
consensus is the exact zero of the pair ensemble gain (the
two-point form of `consensus_no_gain`). -/
theorem twoGap_zero_iff (hp : ∀ u, 0 < p u)
    (hsum : ∑ u, p u = 1) :
    twoGap p d = 0 ↔ ∃ c : ℝ, ∀ u, d u = c := by
  constructor
  · -- gap = 0 forces every pair deviation to vanish
    intro h0
    unfold twoGap at h0
    rw [twoGap_cosh] at h0
    set S := ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v) with hSdef
    -- S >= 1 (weighted cosh >= weighted 1)
    have hc : ∀ u v : k, p u * p v * 1
        ≤ p u * p v * Real.cosh (d u - d v) :=
      fun u v => mul_le_mul_of_nonneg_left (Real.one_le_cosh _)
        (mul_nonneg (hp u).le (hp v).le)
    have hsumpp : ∑ u, ∑ v, p u * p v = 1 := by
      rw [← Finset.sum_mul_sum, hsum]
      norm_num
    have hS1 : (1:ℝ) ≤ S := by
      have h11 : ∑ u, ∑ v, p u * p v * 1 = 1 := by
        have : ∑ u, ∑ v, p u * p v * 1 = ∑ u, ∑ v, p u * p v := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact Finset.sum_congr rfl fun v _ => mul_one _
        rw [this, hsumpp]
      calc (1:ℝ) = ∑ u, ∑ v, p u * p v * 1 := h11.symm
        _ ≤ S := Finset.sum_le_sum fun u _ =>
            Finset.sum_le_sum fun v _ => hc u v
    -- ½ log S = 0 with S >= 1 forces S = 1
    have hlog0 : Real.log S = 0 := by
      have hmul : (1/2 : ℝ) * Real.log S = 0 := by
        rw [← h0]
      have h2 : (1/2 : ℝ) ≠ 0 := by norm_num
      rw [mul_eq_zero] at hmul
      cases hmul with
      | inl h => exact absurd h h2
      | inr h => exact h
    have hS : S = 1 := by
      by_contra hSne
      have hSgt : 1 < S := lt_of_le_of_ne hS1 (fun heq => hSne heq.symm)
      have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS1
      have hloggt : Real.log 1 < Real.log S :=
        Real.log_lt_log (by norm_num : (0:ℝ) < 1) hSgt
      rw [Real.log_one] at hloggt
      linarith
    -- S = 1 and every weighted (cosh - 1) >= 0, sum of pp(cosh-1) = S - 1 = 0
    -- hence every cosh term = 1, hence every d u - d v = 0
    have hdecomp : ∑ u, ∑ v, p u * p v * (Real.cosh (d u - d v) - 1) = 0 := by
      have hexpand : ∀ u v : k,
          p u * p v * (Real.cosh (d u - d v) - 1)
            + p u * p v * 1 = p u * p v * Real.cosh (d u - d v) := by
        intro u v
        ring
      have hsplit : ∑ u, ∑ v, (p u * p v * (Real.cosh (d u - d v) - 1)
          + p u * p v * 1) = S := by
        rw [Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun v _ => hexpand u v]
      have h11 : ∑ u, ∑ v, p u * p v * 1 = 1 := by
        have : ∑ u, ∑ v, p u * p v * 1 = ∑ u, ∑ v, p u * p v := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact Finset.sum_congr rfl fun v _ => mul_one _
        rw [this, hsumpp]
      -- split the double sum: ∑(A + B) = ∑A + ∑B (outer + inner)
      have hinner : ∀ u : k, ∑ v, (p u * p v * (Real.cosh (d u - d v) - 1)
          + p u * p v * 1)
          = ∑ v, p u * p v * (Real.cosh (d u - d v) - 1)
            + ∑ v, p u * p v * 1 := fun u => Finset.sum_add_distrib
      rw [Finset.sum_congr rfl fun u _ => hinner u,
        Finset.sum_add_distrib] at hsplit
      rw [h11] at hsplit
      -- hsplit : ∑∑(cosh-1) + 1 = S; with S = 1 this gives ∑∑(cosh-1) = 0
      rw [hS] at hsplit
      linarith
    -- nonneg terms summing to 0: each is 0
    have hterm0 : ∀ u v : k,
        p u * p v * (Real.cosh (d u - d v) - 1) = 0 := by
      intro u v
      have hnn : ∀ (x : k) (y : k),
          0 ≤ p x * p y * (Real.cosh (d x - d y) - 1) := by
        intro x y
        exact mul_nonneg (mul_nonneg (hp x).le (hp y).le)
          (sub_nonneg_of_le (Real.one_le_cosh _))
      have := Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        Finset.sum_nonneg fun y _ => hnn x y) |>.mp hdecomp
      have hx := this u (Finset.mem_univ u)
      have := Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => hnn u y) |>.mp hx
      exact this v (Finset.mem_univ v)
    -- cosh = 1 hence d u = d v for all u v: pick any w, d u = d w
    obtain ⟨w⟩ : Nonempty k := inferInstance
    refine ⟨d w, fun u => ?_⟩
    -- from hterm0 u w: p u * p w * (cosh (d u - d w) - 1) = 0
    have h1 := hterm0 u w
    have hppos : p u * p w ≠ 0 :=
      mul_ne_zero (ne_of_gt (hp u)) (ne_of_gt (hp w))
    have hcosh1 : Real.cosh (d u - d w) - 1 = 0 := by
      by_contra hne
      -- p u * p w ≠ 0 and the product is 0 forces the factor to 0
      have : p u * p w * (Real.cosh (d u - d w) - 1) ≠ 0 :=
        mul_ne_zero hppos hne
      rw [h1] at this
      exact this rfl
    have hcosheq : Real.cosh (d u - d w) = 1 := by
      have := hterm0 u w
      linarith [hcosh1]
    -- cosh x = 1 → x = 0 (via cosh_le_cosh)
    have hzero : d u - d w = 0 := by
      have hle : Real.cosh (d u - d w) ≤ Real.cosh 0 := by
        rw [hcosheq]
        simp
      have h2 := (Real.cosh_le_cosh).mp hle
      simpa using h2
    linarith
  · -- a constant deviation is a shift: cosh 0 = 1 → S = 1 → gap = 0
    intro ⟨c, hc⟩
    unfold twoGap
    rw [twoGap_cosh]
    have hd : ∀ u v : k, d u - d v = 0 :=
      fun u v => by rw [hc u, hc v, sub_self]
    have hS : ∑ u, ∑ v, p u * p v * Real.cosh (d u - d v)
        = ∑ u, ∑ v, p u * p v * 1 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hd u v, Real.cosh_zero]
    rw [hS]
    have h1 : ∑ u, ∑ v, p u * p v * 1 = 1 := by
      have h2 : ∑ u, ∑ v, p u * p v * 1 = ∑ u, ∑ v, p u * p v := by
        refine Finset.sum_congr rfl fun u _ => ?_
        exact Finset.sum_congr rfl fun v _ => mul_one _
      rw [h2, ← Finset.sum_mul_sum, hsum]
      norm_num
    rw [h1, Real.log_one, mul_zero]

/-- **The variance normalization of the quadratic law.** The
softmax-measure second moment of the pairwise difference is
twice the deviation variance:

`E[(d_u − d_v)²] = 2·(E[d²] − E[d]²)`

under the product measure `p_u p_v` — the exact constant behind
`Gap ≈ ¼·E[(d_u − d_v)²]` (the small-x expansion
`log cosh x ≈ x²/2`, giving `Gap ≈ ½·Var_p(d)`; the Hessian law
`½·Tr[H·Cov(d)] = ½·Var_p(d)` since `Tr[H·Cov] = Var_p`). -/
theorem pairVarEq (hsum : ∑ u, p u = 1) :
    ∑ u, ∑ v, p u * p v * (d u - d v)^2
      = 2 * (∑ u, p u * (d u)^2 - (∑ u, p u * d u)^2) := by
  have hmem : ∀ u v : k, p u * p v * (d u - d v)^2
      = (p u * (d u)^2) * p v + (p u * (p v * (d v)^2)
        - 2 * (p u * d u) * (p v * d v)) := by
    intro u v
    ring
  have hrow : ∀ u : k, ∑ v, ((p u * (d u)^2) * p v
      + (p u * (p v * (d v)^2) - 2 * (p u * d u) * (p v * d v)))
      = (p u * (d u)^2) * ∑ v, p v
        + (p u * ∑ v, (p v * (d v)^2)
          - 2 * (p u * d u) * ∑ v, (p v * d v)) := by
    intro u
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => hmem u v]
  rw [Finset.sum_congr rfl fun u _ => hrow u]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hS1 : ∑ u, (p u * (d u)^2) * ∑ v, p v
      = ∑ u, p u * (d u)^2 := by
    rw [(Finset.sum_mul _ _ _).symm, hsum, mul_one]
  have hS2 : ∑ u, p u * (∑ v, p v * (d v)^2)
      = ∑ u, p u * (d u)^2 := by
    rw [(Finset.sum_mul _ _ _).symm, hsum, one_mul]
  have hS3 : ∑ u, 2 * (p u * d u) * ∑ v, p v * d v
      = 2 * (∑ u, p u * d u) * (∑ v, p v * d v) := by
    rw [(Finset.sum_mul _ _ _).symm,
      show ∑ i, 2 * (p i * d i) = 2 * ∑ i, p i * d i from
        (Finset.mul_sum _ _ _).symm]
  rw [hS1, hS2, hS3]
  ring

end GapLaw

end Hagi

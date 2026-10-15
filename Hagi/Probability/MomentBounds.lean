/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.PinskerTV
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

open Finset Real

/-- Popoviciu: for bounded g : [a,b] with weights q summing to 1,
the weighted variance is at most (b-a)^2/4.  Three-step argument:
mu in [a,b] (barycenter), per-point squared deviation from midpoint
bounded by ((b-a)/2)^2, and variance minimality of the mean. -/
theorem popoviciu_var {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (a b : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) :
    ∑ v : V, q v * (g v - ∑ x : V, q x * g x) ^ 2
      ≤ (b - a) ^ 2 / 4 := by
  set μ := ∑ x : V, q x * g x with hμ
  have hμin : a ≤ μ ∧ μ ≤ b := by
    have h1 : ∑ v : V, q v * g v - a
        = ∑ v : V, q v * (g v - a) := by
      have heq : ∀ v : V, q v * g v - q v * a
          = q v * (g v - a) := fun v => by ring
      have hsa : ∑ v : V, q v * a = a := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a),
          ← Finset.mul_sum, hq1, mul_one]
      rw [show ∑ v : V, q v * (g v - a)
          = ∑ v : V, q v * g v - ∑ v : V, q v * a from by
        rw [Finset.sum_congr rfl (fun v _ => (heq v).symm),
          Finset.sum_sub_distrib], hsa]
    have h2 : b - ∑ v : V, q v * g v
        = ∑ v : V, q v * (b - g v) := by
      have heq : ∀ v : V, q v * b - q v * g v
          = q v * (b - g v) := fun v => by ring
      have hsb : ∑ v : V, q v * b = b := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) b),
          ← Finset.mul_sum, hq1, mul_one]
      rw [show ∑ v : V, q v * (b - g v)
          = ∑ v : V, q v * b - ∑ v : V, q v * g v from by
        rw [Finset.sum_congr rfl (fun v _ => (heq v).symm),
          Finset.sum_sub_distrib], hsb]
    have ha1 : ∑ v : V, q v * (g v - a) ≥ 0 :=
      Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hq v).le (by linarith [hlo v]))
    have ha2 : ∑ v : V, q v * (b - g v) ≥ 0 :=
      Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hq v).le (by linarith [hhi v]))
    constructor
    · rw [hμ]
      linarith [ha1, h1.symm, ha2, h2]
    · rw [hμ]
      linarith [ha1, h1.symm, ha2, h2]
  -- per-v: |g v - m| <= (b-a)/2 where m = (a+b)/2
  have hmid : ∀ v : V, (g v - (a + b) / 2) ^ 2
      ≤ ((b - a) / 2) ^ 2 := by
    intro v
    have he1 : |(2:ℝ) * (g v - (a + b) / 2)| = 2 * |g v - (a + b) / 2| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have he2 : |(2:ℝ) * (g v - (a + b) / 2)| ≤ b - a := by
      rw [abs_le]
      constructor
      · linarith [hlo v, hhi v]
      · linarith [hlo v, hhi v]
    have he3 : |(g v - (a + b) / 2)| ≤ (b - a) / 2 := by
      rw [abs_le]
      constructor
      · linarith [he2, hlo v, hhi v]
      · linarith [he2, hlo v, hhi v]
    exact sq_le_sq.mpr (he3.trans (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (b - a) / 2)]))
  -- variance minimal at mean: sum q(g-mu)^2 <= sum q(g-m)^2
  -- variance minimal at mean: sum q(g-mu)^2 <= sum q(g-m)^2
  have hvarmin : ∑ v : V, q v * (g v - ∑ x : V, q x * g x) ^ 2
      ≤ ∑ v : V, q v * (g v - (a + b) / 2) ^ 2 := by
    set μ := ∑ x : V, q x * g x with hμd
    have hμ1 : ∑ v : V, q v = 1 := hq1
    have key : ∀ c : ℝ, ∑ v : V, q v * (g v - c) ^ 2
        = (∑ v : V, q v * g v ^ 2) - 2 * c * μ + c ^ 2 := by
      intro c
      have expand : ∀ v : V, q v * (g v - c) ^ 2
          = q v * g v ^ 2 - q v * (2 * c * g v) + q v * c ^ 2 := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => by rw [expand v])]
      push_cast [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun v _ =>
        (by ring : q v * (2 * c * g v) = (q v * g v) * (2 * c)))]
      rw [← Finset.sum_mul, ← hμd]
      rw [Finset.sum_congr rfl (fun v _ => (by ring : q v * c ^ 2 = c ^ 2 * q v)),
        ← Finset.mul_sum, hμ1, mul_one]
      ring
    have hΔ : ∀ c : ℝ, ∑ v : V, q v * (g v - c) ^ 2
        = (∑ v : V, q v * (g v - μ) ^ 2) + (c - μ) ^ 2 := by
      intro c
      rw [key c, key μ]
      ring
    have hspec := hΔ ((a + b) / 2)
    have hnonneg : (0:ℝ) ≤ ((a + b) / 2 - μ) ^ 2 := sq_nonneg _
    linarith [hspec, hnonneg]
  -- bound each term by (b-a)^2/4
  have havg : ∑ v : V, q v * (g v - (a + b) / 2) ^ 2
      ≤ (b - a) ^ 2 / 4 := by
    have h1 : ∑ v : V, q v * (g v - (a + b) / 2) ^ 2
        ≤ ∑ v : V, q v * (((b - a) / 2) ^ 2) :=
      Finset.sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (hmid v) (hq v).le)
    have h2 : ∑ v : V, q v * (((b - a) / 2) ^ 2)
        = ((b - a) / 2) ^ 2 := by
      rw [Finset.sum_congr rfl (fun v _ =>
        (mul_comm (q v) (((b - a) / 2) ^ 2))),
        ← Finset.mul_sum, hq1, mul_one]
    rw [h2] at h1
    have h3 : ((b - a) / 2) ^ 2 = (b - a) ^ 2 / 4 := by field_simp; ring
    rw [h3] at h1
    exact h1
  exact le_trans hvarmin havg

/-- Chebyshev-Popoviciu: for g in [a,b] under weights q, the two-sided
deviation tail satisfies q{|g-mu| >= t} <= (b-a)^2/(4t^2).  Chain:
Markov on the squared deviation + Popoviciu variance bound. -/
theorem chebyshev_popoviciu {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (q g : V → ℝ) (a b t : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (ht : 0 < t) :
    ∑ v ∈ Finset.filter (fun v => t ≤ |g v - ∑ x : V, q x * g x|)
      Finset.univ, q v
      ≤ (b - a) ^ 2 / (4 * t ^ 2) := by
  set μ := ∑ x : V, q x * g x with hμd
  have hnng : ∀ v, (0:ℝ) ≤ (g v - μ) ^ 2 := fun v => sq_nonneg _
  have ht2 : (0:ℝ) < t ^ 2 := sq_pos_of_ne_zero (ne_of_gt ht)
  have hmk := markov_finite q (fun v => (g v - μ) ^ 2) (t ^ 2)
    hq hnng ht2
  have hsub : ∀ v : V, t ≤ |g v - μ| → t ^ 2 ≤ (g v - μ) ^ 2 := by
    intro v hv
    have habs : |t| ≤ |g v - μ| := by rw [abs_of_pos ht]; exact hv
    exact sq_le_sq.mpr habs
  set S1 := Finset.filter (fun v => t ≤ |g v - μ|) Finset.univ with hS1
  set S2 := Finset.filter (fun v => t ^ 2 ≤ (g v - μ) ^ 2) Finset.univ with hS2
  have hss : S1 ⊆ S2 := by
    intro v hv
    rw [hS1, Finset.mem_filter] at hv
    rw [hS2, Finset.mem_filter]
    exact ⟨hv.1, hsub v hv.2⟩
  have hcard : ∑ v ∈ S1, q v ≤ ∑ v ∈ S2, q v := by
    have hsplit : ∑ v ∈ S2, q v
        = ∑ v ∈ S1, q v + ∑ v ∈ S2 \ S1, q v := by
      have := Finset.sum_sdiff hss (f := q)
      linarith
    rw [hsplit]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg (fun v _ => le_of_lt (hq v)))
  -- chain: t^2 * prob(S1) <= Var <= (b-a)^2/4
  have hpop := popoviciu_var q g a b hq hq1 hlo hhi
  have hVar : ∑ v : V, q v * (g v - μ) ^ 2 ≤ (b - a) ^ 2 / 4 := hpop
  have hchain : t ^ 2 * ∑ v ∈ S1, q v ≤ (b - a) ^ 2 / 4 := by
    calc t ^ 2 * ∑ v ∈ S1, q v
        ≤ t ^ 2 * ∑ v ∈ S2, q v :=
          mul_le_mul_of_nonneg_left hcard (le_of_lt ht2)
      _ ≤ ∑ v : V, q v * (g v - μ) ^ 2 := hmk
      _ ≤ (b - a) ^ 2 / 4 := hVar
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * t ^ 2)]
  nlinarith [hchain, ht2]

/-- Cantelli (one-sided Chebyshev): for g in [a,b] under weights q,
the one-sided deviation tail satisfies q{g - mu >= t} <= sigma^2 /
(sigma^2 + t^2) with sigma^2 = (b-a)^2/4.  Proof: Markov on the
shifted square (g - mu + c)^2 with c = sigma^2/t, cross term
vanishes since sum q(g - mu) = 0, and (sigma^2 + c^2)(sigma^2 + t^2)
= sigma^2(t + c)^2 closes the algebra. -/
theorem cantelli_one_side {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (q g : V → ℝ) (a b t : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (ht : 0 < t) :
    ∑ v ∈ Finset.filter (fun v => t ≤ g v - ∑ x : V, q x * g x)
      Finset.univ, q v
      ≤ (b - a) ^ 2 / (4 * t ^ 2 + (b - a) ^ 2) := by
  set μ := ∑ x : V, q x * g x with hμd
  set σ2 := (b - a) ^ 2 / 4 with hσ2def
  have hσ2 : (0:ℝ) ≤ σ2 := by unfold σ2; positivity
  rcases lt_or_eq_of_le hσ2 with hσ2pos | hσ2zero
  · -- main case: sigma2 > 0
    have hpop := popoviciu_var q g a b hq hq1 hlo hhi
    have hVar : ∑ v : V, q v * (g v - μ) ^ 2 ≤ σ2 := hpop
    set c := σ2 / t with hc
    have hc_pos : 0 < c := div_pos hσ2pos ht
    have hdev : ∀ v : V, t ≤ g v - μ →
        (t + c) ^ 2 ≤ (g v - μ + c) ^ 2 := by
      intro v hv
      have h1 : t + c ≤ g v - μ + c := by linarith
      have h2 : (0:ℝ) ≤ t + c := by linarith
      have h3 : (0:ℝ) ≤ g v - μ + c := by linarith
      exact sq_le_sq.mpr
        (by rw [abs_of_nonneg h2, abs_of_nonneg h3]; exact h1)
    have hnng : ∀ v, (0:ℝ) ≤ (g v - μ + c) ^ 2 := fun v => sq_nonneg _
    have hthr : (0:ℝ) < (t + c) ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt (by linarith))
    have hmk := markov_finite q (fun v => (g v - μ + c) ^ 2)
      ((t + c) ^ 2) hq hnng hthr
    set S1 := Finset.filter (fun v => t ≤ g v - μ) Finset.univ with hS1
    set S2 := Finset.filter
      (fun v => (t + c) ^ 2 ≤ (g v - μ + c) ^ 2) Finset.univ with hS2
    have hss : S1 ⊆ S2 := by
      intro v hv
      rw [hS1, Finset.mem_filter] at hv
      rw [hS2, Finset.mem_filter]
      exact ⟨hv.1, hdev v hv.2⟩
    have hcard : ∑ v ∈ S1, q v ≤ ∑ v ∈ S2, q v := by
      have hsplit : ∑ v ∈ S2, q v
          = ∑ v ∈ S1, q v + ∑ v ∈ S2 \ S1, q v := by
        have := Finset.sum_sdiff hss (f := q)
        linarith
      rw [hsplit]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg (fun v _ => le_of_lt (hq v)))
    have hqμ : ∑ v : V, q v * (g v - μ) = 0 := by
      have hsplit : ∀ v : V, q v * (g v - μ)
          = q v * g v - q v * μ := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
      rw [Finset.sum_sub_distrib]
      have hB : ∑ v : V, q v * μ = μ := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) μ),
          ← Finset.mul_sum, hq1, mul_one]
      rw [hB]
      rw [hμd]
      ring
    have hE : ∑ v : V, q v * (g v - μ + c) ^ 2 ≤ σ2 + c ^ 2 := by
      have hexp : ∀ v : V, q v * (g v - μ + c) ^ 2
          = q v * (g v - μ) ^ 2 + 2 * c * (q v * (g v - μ))
            + q v * c ^ 2 := by
        intro v; ring
      rw [Finset.sum_congr rfl (fun v _ => hexp v)]
      have hcross : ∑ v : V, 2 * c * (q v * (g v - μ)) = 0 := by
        have hpull : ∑ v : V, 2 * c * (q v * (g v - μ))
            = 2 * c * ∑ v : V, q v * (g v - μ) := by
          rw [Finset.mul_sum]
        rw [hpull, hqμ, mul_zero]
      have hconst : ∑ v : V, q v * c ^ 2 = c ^ 2 := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) (c ^ 2)),
          ← Finset.mul_sum, hq1, mul_one]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross, hconst]
      linarith
    have hchain : (t + c) ^ 2 * ∑ v ∈ S1, q v ≤ σ2 + c ^ 2 := by
      calc (t + c) ^ 2 * ∑ v ∈ S1, q v
          ≤ (t + c) ^ 2 * ∑ v ∈ S2, q v :=
            mul_le_mul_of_nonneg_left hcard (le_of_lt hthr)
        _ ≤ ∑ v : V, q v * (g v - μ + c) ^ 2 := hmk
        _ ≤ σ2 + c ^ 2 := hE
    have htc : t * c = σ2 := by rw [hc]; field_simp
    have h4 : (b - a) ^ 2 = 4 * σ2 := by
      have : σ2 = (b - a) ^ 2 / 4 := rfl
      linarith [this]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * t ^ 2 + (b - a) ^ 2)]
    nlinarith [hchain, htc, h4]
  · -- degenerate: sigma2 = 0, so a = b, g constant, event empty
    have hab : (b - a) ^ 2 = 0 := by
      have : σ2 = (b - a) ^ 2 / 4 := rfl
      rw [hσ2def] at hσ2zero
      have h4 : (4:ℝ) ≠ 0 := by norm_num
      field_simp at hσ2zero
      linarith [hσ2zero]
    have hba : b = a := by
      have := sq_eq_zero_iff.mp hab
      linarith
    have hg : ∀ v : V, g v = a := by
      intro v; rw [← hba]; linarith [hlo v, hhi v]
    have hμa : μ = a := by
      unfold μ
      rw [Finset.sum_congr rfl (fun v _ => by rw [hg v])]
      rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a)]
      rw [← Finset.mul_sum, hq1, mul_one]
    have hfalse : ∀ v : V, t ≤ g v - μ → False := by
      intro v hv
      rw [hμa, hg v] at hv
      linarith
    have hempty : Finset.filter (fun v => t ≤ g v - μ) Finset.univ = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hμa, hg v, sub_self]
      simp [ht]
    rw [hempty, Finset.sum_empty]
    have hR : (0:ℝ) ≤ (b - a) ^ 2 / (4 * t ^ 2 + (b - a) ^ 2) := by
      rw [hab]
      positivity
    linarith


/-- Mean absolute deviation Popoviciu: for g in [a,b] under weights q,
the expected absolute deviation from the mean satisfies
E|g - mu| <= (b - a)/2.  Cauchy-Schwarz on (sqrt q, sqrt q * |g - mu|)
gives (E|g-mu|)^2 <= Var, then Popoviciu variance bound and sqrt
monotonicity. -/
theorem popoviciu_abs_dev {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (a b : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) :
    ∑ v : V, q v * |g v - ∑ x : V, q x * g x| ≤ (b - a) / 2 := by
  set μ := ∑ x : V, q x * g x with hμd
  have hpop := popoviciu_var q g a b hq hq1 hlo hhi
  -- per-term: q v * |g v - mu| = sqrt(q v) * (sqrt(q v) * |g v - mu|)
  have hterm : ∀ v : V, Real.sqrt (q v) * (Real.sqrt (q v) * |g v - μ|)
      = q v * |g v - μ| := by
    intro v
    have h : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (le_of_lt (hq v))
    linear_combination |g v - μ| * h
  -- Cauchy-Schwarz on sqrt q and sqrt q * |g - mu|
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := Finset.univ) (f := fun v => Real.sqrt (q v))
    (g := fun v => Real.sqrt (q v) * |g v - μ|)
  rw [Finset.sum_congr rfl (fun v _ => hterm v)] at hcs
  -- first factor: sum q = 1; second: sum q * (g-mu)^2
  have hf1 : ∑ v : V, Real.sqrt (q v) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl
      (fun v _ => Real.sq_sqrt (le_of_lt (hq v))), hq1]
  have hf2 : ∑ v : V, (Real.sqrt (q v) * |g v - μ|) ^ 2
      = ∑ v : V, q v * (g v - μ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun v _ => by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (hq v)), sq_abs])]
  rw [hf1, hf2] at hcs
  -- hcs : (sum q |g-mu|)^2 <= 1 * Var <= (b-a)^2/4
  have hsq : (∑ v : V, q v * |g v - μ|) ^ 2 ≤ (b - a) ^ 2 / 4 := by
    rw [one_mul] at hcs
    linarith
  have hnn : (0:ℝ) ≤ ∑ v : V, q v * |g v - μ| :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hq v)) (abs_nonneg _))
  have hba : (0:ℝ) ≤ b - a := by
    have := Classical.arbitrary V
    linarith [hlo ‹V›, hhi ‹V›]
  -- sqrt both sides
  have hs1 : Real.sqrt ((∑ v : V, q v * |g v - μ|) ^ 2)
      ≤ Real.sqrt ((b - a) ^ 2 / 4) := by
    apply Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnn] at hs1
  have hhalf : Real.sqrt ((b - a) ^ 2 / 4) = (b - a) / 2 := by
    have h4 : (0:ℝ) < 4 := by norm_num
    have hs : Real.sqrt ((b - a) ^ 2 / 4)
        = Real.sqrt ((b - a) ^ 2) / Real.sqrt 4 :=
      Real.sqrt_div (sq_nonneg (b - a)) 4
    rw [hs, Real.sqrt_sq hba, show Real.sqrt 4 = 2 by norm_num]
  rwa [hhalf] at hs1


/-- Bhatia-Davis: sharpened Popoviciu variance bound Var_q(g) <=
(b - mu)(mu - a) for g in [a,b], mu the weighted mean.  Proof is pure
algebra: per-vertex (b - g)(g - a) >= 0, summed with weights it gives
E g^2 <= (a + b) mu - a b, combined with the variance identity
Var = E g^2 - mu^2.  Note (b-mu)(mu-a) <= (b-a)^2/4 recovers
popoviciu_var. -/
theorem bhatia_davis {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (a b : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) :
    ∑ v : V, q v * (g v - ∑ x : V, q x * g x) ^ 2
      ≤ (b - ∑ x : V, q x * g x) * (∑ x : V, q x * g x - a) := by
  set μ := ∑ x : V, q x * g x with hμd
  -- expand per-v: (b - g v) * (g v - a) >= 0
  have hper : ∀ v : V, (0:ℝ) ≤ (b - g v) * (g v - a) := by
    intro v
    exact mul_nonneg (by linarith [hhi v]) (by linarith [hlo v])
  -- sum with weights: E[(b-g)(g-a)] >= 0
  have hsum : (0:ℝ) ≤ ∑ v : V, q v * ((b - g v) * (g v - a)) :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hq v)) (hper v))
  -- expand: E[(b-g)(g-a)] = b*mu - ab - (E g^2 - a*b) ... compute:
  -- q*((b-g)(g-a)) = q*(b*g - b*a - g^2 + a*g)
  have hexp : ∑ v : V, q v * ((b - g v) * (g v - a))
      = ∑ v : V, (q v * (b * g v) + q v * (a * g v))
        - ∑ v : V, (q v * (b * a) + q v * g v ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hsum' : ∑ v : V, (q v * (b * g v) + q v * (a * g v))
      - ∑ v : V, (q v * (b * a) + q v * g v ^ 2)
      = b * μ - b * a - (∑ v : V, q v * g v ^ 2) + a * μ := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hbg : ∑ v : V, q v * (b * g v) = b * μ := by
      rw [Finset.sum_congr rfl (fun v _ =>
        show q v * (b * g v) = b * (q v * g v) from by ring),
        Finset.mul_sum]
    have hba : ∑ v : V, q v * (b * a) = b * a := by
      rw [Finset.sum_congr rfl (fun v _ =>
        show q v * (b * a) = b * a * q v from by ring)]
      rw [← Finset.mul_sum, hq1, mul_one]
    have hag : ∑ v : V, q v * (a * g v) = a * μ := by
      rw [Finset.sum_congr rfl (fun v _ =>
        show q v * (a * g v) = a * (q v * g v) from by ring),
        Finset.mul_sum]
    rw [hbg, hba, hag]
    ring
  rw [hexp, hsum'] at hsum
  -- variance identity: Var = E g^2 - mu^2
  have hvar : ∑ v : V, q v * (g v - μ) ^ 2
      = ∑ v : V, q v * g v ^ 2 - μ ^ 2 := by
    have hterm : ∀ v : V, q v * (g v - μ) ^ 2
        = (q v * g v ^ 2 + q v * μ ^ 2) - 2 * μ * (q v * g v) := by
      intro v; ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hcross : ∑ v : V, 2 * μ * (q v * g v) = 2 * μ * μ := by
      have hpull : ∑ v : V, 2 * μ * (q v * g v)
          = 2 * μ * ∑ v : V, q v * g v := by
        rw [← Finset.mul_sum]
      rw [hpull]
    have hconst : ∑ v : V, q v * μ ^ 2 = μ ^ 2 := by
      rw [Finset.sum_congr rfl (fun v _ =>
        show q v * μ ^ 2 = μ ^ 2 * q v from by ring)]
      rw [← Finset.mul_sum, hq1, mul_one]
    rw [hcross, hconst]
    ring
  -- chain: Var = E g^2 - mu^2 <= b*mu + a*mu - a*b - mu^2 = (b-mu)(mu-a)
  rw [hvar]
  linarith [hsum, hexp]


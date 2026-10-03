/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.FreeEnergy
import Hagi.Ensemble.Hoeffding

set_option linter.style.header false
/-!
# R106: PoE logZ second-order stability — the sharp per-expert (1/8)·ΣwR² law

For the product-of-experts normalizer

`Z_w = Σ_v exp(Σ_i w_i·z_{i,v})`

(= the geometric-pool partition function of `geometric_pool_identity`,
with per-expert normalizers `Z_i = Σ_v exp(z_{i,v})`), the
"fast-inference" approximation is the LINEAR-pool normalizer

`Z_approx = Π_i Z_i^{w_i}`  (log Z_approx = Σ_i w_i·log Z_i),

which needs only softmax-speed arithmetic. This module certifies the
approximation by the SHARP second-order law

`|log Z_w − log Z_approx| ≤ (1/8)·Σ_i w_i·(R_i)²`,

where `R_i` dominates the range of expert `i`'s centered deviation
from the pooled mean `μ = Σ_l w_l·z_l`: `∀ u v, (z i u − μ u) − (z i v − μ v) ≤ R i`
(`poe_logZ_second_order`).

**The route** (three pillars, no Hessian machinery):

1. **Hoeffding's lemma, finite form** (`mgf_hoeffding_ab`,
   `mgf_hoeffding`): for a probability vector `q` and `h` with
   range ≤ D, `log E_q[e^h] ≤ E_q[h] + D²/8`. Proof: the chord
   bound of exp (convexity on [a,b] — the R56 route) reduces to
   the two-point Bernoulli MGF `1 − θ + θ·e^s ≤ e^{θs + s²/8}`
   (`bern_mgf_bound`), proven by calculus: F(s) = θs + s²/8 −
   log(1−θ+θeˢ) has F(0) = F'(0) = 0 and slope monotone by the
   Bernoulli-variance bound ρ(1−ρ) ≤ ¼. This closes the round-68
   OPEN item ("the transcendental (b−a)²/8 step, absent from
   Mathlib") in the direction needed here.
2. **Log-sum-exp deviation bounds** (`lse_shift_lower`,
   `lse_shift_upper`): the deviation of lse from `x` to `y` is
   `log E_{σ(x)}[e^{y−x}]`; pillar 1 gives the upper second-order
   bound, exp-Jensen the lower (supporting-hyperplane) bound.
3. **The assembly** (`poe_logZ_second_order`): per-expert
   `lse_shift_upper` at x := μ (the POOLED MEAN), y := z i, then
   weight by w i and sum — the linear terms cancel EXACTLY
   (after the sum swap each is σ(μ)_v · Σ_i w_i(z_i v − μ v) =
   σ(μ)_v · 0, the centering identity `sum_w_center`). The gap's
   sign is `lse_shift_lower` (Jensen at the center via
   `weighted_center_le`).

**HONEST CORRECTION of the audit's form.** The audit claimed the
pairwise law `|·| ≤ (1/8)·Σ_{i,j} w_i w_j D_{ij}²` with D the
pairwise logit diameter. That form is FALSE — counterexample
z₁ = (1,−1), z₂ = (0,0), w = (½,½): the true gap is
½·log[cosh(1)/cosh²(½)] ≈ 0.0968 > ⅛·ΣΣ w w D² = 0.0625. The
sharp law is the PER-EXPERT range form above (constant 1/8,
asymptotically tight: z₁ = (A,−A), z₂ = (−A,A), equal weights,
R = 2A gives gap = log cosh A ~ A²/2 = R²/8). Under a pairwise
diameter hypothesis the provable constant is ½
(`poe_logZ_pairwise`, via R i := 2·Σ_j w_j D_ij and the weighted
Cauchy–Schwarz `weighted_var_bound`). The audit's M²/8 per-token
form holds as `poe_softmax_speed` — when each expert's spread
around μ is ≤ M (the K = 2 case has μ = the midpoint, recovering
the pairwise statement).

**Runtime prescription** (`poe_softmax_speed`,
`poe_sequence_speed`): with per-token centered range ≤ M_t, the
per-token normalizer error of softmax-speed PoE pooling is ≤
M_t²/8 — compute pooled mean logits plus the correction, no
long-exponent products; the full-sequence product composes by
summing per-token gaps: total error ≤ (1/8)·Σ_t M_t² (no
cross-token cancellation claimed).

**Process note**: an earlier draft chased an elaborate
exchangeable-MIDPOINT assembly claiming the audit's pairwise 1/8;
it was mathematically wrong (per the counterexample above) and
was deleted. The correct proof is the simple per-expert route —
this is a caution against proving a false target.
-/

open Finset Real

namespace Hagi

/-! ## Pillar 0: the scalar (b−a)²/8 kernel -/

/-- The denominator of the two-point Bernoulli MGF. -/
private noncomputable def bernDenom (θ : ℝ) : ℝ → ℝ :=
  fun t => 1 - θ + θ * Real.exp t

/-- The tilted Bernoulli weight ρ(t) = θeᵗ/(1−θ+θeᵗ). -/
private noncomputable def bernRho (θ : ℝ) : ℝ → ℝ :=
  fun t => θ * Real.exp t / bernDenom θ t

/-- The Hoeffding surplus F(t) = θt + t²/8 − log(1−θ+θeᵗ). -/
private noncomputable def bernF (θ : ℝ) : ℝ → ℝ :=
  fun t => θ * t + t ^ 2 / 8 - Real.log (bernDenom θ t)

private theorem bernDenom_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    0 < bernDenom θ t := by
  have hp : 0 < θ * Real.exp t := mul_pos h0 (Real.exp_pos t)
  have hq : 0 < 1 - θ := by linarith
  unfold bernDenom
  linarith

private theorem bernDenom_ne_zero {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    bernDenom θ t ≠ 0 :=
  ne_of_gt (bernDenom_pos h0 h1 t)

private theorem bernRho_hasDerivAt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    HasDerivAt (bernRho θ)
      (θ * (1 - θ) * Real.exp t / (bernDenom θ t) ^ 2) t := by
  have hc : HasDerivAt (fun t => (1 - θ : ℝ)) 0 t := hasDerivAt_const _ _
  have he : HasDerivAt (fun t => θ * Real.exp t) (θ * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul θ
  have hdd : HasDerivAt (fun t => 1 - θ + θ * Real.exp t) (θ * Real.exp t) t := by
    simpa [Pi.add_def] using hc.add he
  have hdiv : HasDerivAt (fun t => θ * Real.exp t / (1 - θ + θ * Real.exp t))
      ((θ * Real.exp t * (1 - θ + θ * Real.exp t)
        - θ * Real.exp t * (θ * Real.exp t))
        / (1 - θ + θ * Real.exp t) ^ 2) t :=
    he.div hdd (by
      have hq : (0:ℝ) < 1 - θ := by linarith
      have hp : (0:ℝ) < θ * Real.exp t := mul_pos h0 (Real.exp_pos t)
      intro hcon
      linarith)
  have hval : θ * (1 - θ) * Real.exp t / (bernDenom θ t) ^ 2
      = (θ * Real.exp t * (1 - θ + θ * Real.exp t)
        - θ * Real.exp t * (θ * Real.exp t))
        / (1 - θ + θ * Real.exp t) ^ 2 := by
    unfold bernDenom
    field_simp
    ring
  unfold bernRho
  rw [hval]
  exact hdiv

private theorem bernRho_deriv_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    θ * (1 - θ) * Real.exp t / (bernDenom θ t) ^ 2 ≤ 1 / 4 := by
  have hden : (0:ℝ) < (bernDenom θ t) ^ 2 :=
    sq_pos_of_ne_zero (bernDenom_ne_zero h0 h1 t)
  have hkey : ((1 - θ) - θ * Real.exp t) ^ 2
      = (bernDenom θ t) ^ 2 - 4 * (θ * (1 - θ) * Real.exp t) := by
    unfold bernDenom
    ring
  have hsq : (0:ℝ) ≤ ((1 - θ) - θ * Real.exp t) ^ 2 := sq_nonneg _
  rw [div_le_iff₀ hden]
  nlinarith [hkey, hsq]

private theorem bernRho_cont {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Continuous (bernRho θ) := by
  unfold bernRho bernDenom
  refine Continuous.div (by continuity) (by continuity) (fun t => ?_)
  have hq : (0:ℝ) < 1 - θ := by linarith
  have hp : (0:ℝ) < θ * Real.exp t := mul_pos h0 (Real.exp_pos t)
  intro hcon
  linarith

private theorem bernRho_diff {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Differentiable ℝ (bernRho θ) := by
  have hd : Differentiable ℝ (fun t => 1 - θ + θ * Real.exp t) :=
    (differentiable_const (1 - θ)).add (Real.differentiable_exp.const_mul θ)
  unfold bernRho
  exact (Real.differentiable_exp.const_mul θ).div hd (bernDenom_ne_zero h0 h1)

private theorem bernRho_slope {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∀ a b : ℝ, a < b → bernRho θ b - bernRho θ a ≤ (b - a) / 4 := by
  intro a b hab
  obtain ⟨ξ, -, hξ⟩ := exists_deriv_eq_slope (bernRho θ) hab
    ((bernRho_cont h0 h1).continuousOn)
    ((bernRho_diff h0 h1).differentiableOn)
  have hval : deriv (bernRho θ) ξ
      = θ * (1 - θ) * Real.exp ξ / (bernDenom θ ξ) ^ 2 :=
    (bernRho_hasDerivAt h0 h1 ξ).deriv
  rw [hval] at hξ
  have hb : θ * (1 - θ) * Real.exp ξ / (bernDenom θ ξ) ^ 2 ≤ 1 / 4 :=
    bernRho_deriv_le h0 h1 ξ
  have hne : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hsplit : bernRho θ b - bernRho θ a
      = (θ * (1 - θ) * Real.exp ξ / (bernDenom θ ξ) ^ 2) * (b - a) := by
    rw [hξ]
    field_simp
  rw [hsplit]
  have h2 := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr (le_of_lt hab))
  have h3 : (1 / 4) * (b - a) = (b - a) / 4 := by ring
  rw [h3] at h2
  exact h2

private theorem bernF_hasDerivAt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    HasDerivAt (bernF θ) (θ + t / 4 - bernRho θ t) t := by
  have hc : HasDerivAt (fun t => (1 - θ : ℝ)) 0 t := hasDerivAt_const _ _
  have he : HasDerivAt (fun t => θ * Real.exp t) (θ * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul θ
  have hdd : HasDerivAt (fun t => 1 - θ + θ * Real.exp t) (θ * Real.exp t) t := by
    simpa only [Pi.add_def, zero_add] using hc.add he
  have hdd' : HasDerivAt (bernDenom θ) (θ * Real.exp t) t := by
    have h : HasDerivAt (fun t => 1 - θ + θ * Real.exp t) (θ * Real.exp t) t := hdd
    exact h
  have h1' : HasDerivAt (fun t => θ * t) θ t := by
    simpa using (hasDerivAt_id t).const_mul θ
  have h2 : HasDerivAt (fun t => t ^ 2 / 8) (2 * t / 8) t := by
    simpa using (hasDerivAt_pow 2 t).div_const (8 : ℝ)
  have h3 : HasDerivAt (fun t => Real.log (bernDenom θ t))
      ((θ * Real.exp t) / bernDenom θ t) t :=
    hdd'.log (bernDenom_ne_zero h0 h1 t)
  have hsum : HasDerivAt (fun t => θ * t + t ^ 2 / 8 - Real.log (bernDenom θ t))
      (θ + 2 * t / 8 - (θ * Real.exp t) / bernDenom θ t) t :=
    (h1'.add h2).sub h3
  have hval : θ + 2 * t / 8 - (θ * Real.exp t) / bernDenom θ t
      = θ + t / 4 - bernRho θ t := by
    unfold bernRho
    ring
  unfold bernF
  rw [hval] at hsum
  exact hsum

private theorem bernF_zero {θ : ℝ} (_h0 : 0 < θ) (_h1 : θ < 1) :
    bernF θ 0 = 0 := by
  have hd1 : bernDenom θ 0 = 1 := by
    unfold bernDenom
    rw [Real.exp_zero]
    ring
  unfold bernF
  rw [hd1]
  norm_num

private theorem bernF_slope_zero {θ : ℝ} (_h0 : 0 < θ) (_h1 : θ < 1) :
    θ + 0 / 4 - bernRho θ 0 = 0 := by
  have hrho : bernRho θ 0 = θ := by
    unfold bernRho bernDenom
    rw [Real.exp_zero]
    norm_num
  rw [hrho]
  norm_num

private theorem bernF_mono_slope {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∀ a b : ℝ, a ≤ b → θ + a / 4 - bernRho θ a ≤ θ + b / 4 - bernRho θ b := by
  intro a b hab
  by_cases hab' : a = b
  · rw [hab']
  · have hlt : a < b := lt_of_le_of_ne hab hab'
    have hs := bernRho_slope h0 h1 a b hlt
    have hquarter : a / 4 ≤ b / 4 :=
      div_le_div_of_nonneg_right hab (by norm_num)
    linarith

private theorem bernF_nonneg {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∀ t : ℝ, 0 ≤ bernF θ t := by
  intro t
  have hFdiff : Differentiable ℝ (bernF θ) :=
    fun x => (bernF_hasDerivAt h0 h1 x).differentiableAt
  have hFcont : Continuous (bernF θ) := hFdiff.continuous
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_deriv_eq_slope (bernF θ) hneg
      hFcont.continuousOn hFdiff.differentiableOn
    have hval : deriv (bernF θ) ξ = θ + ξ / 4 - bernRho θ ξ :=
      (bernF_hasDerivAt h0 h1 ξ).deriv
    rw [hval] at hξ
    have hξle : θ + ξ / 4 - bernRho θ ξ ≤ θ + 0 / 4 - bernRho θ 0 :=
      bernF_mono_slope h0 h1 ξ 0 (le_of_lt hξmem.2)
    have hzero := bernF_slope_zero h0 h1
    have hsplit : bernF θ 0 - bernF θ t
        = (θ + ξ / 4 - bernRho θ ξ) * (0 - t) := by
      rw [hξ]
      field_simp
    have hle : (θ + ξ / 4 - bernRho θ ξ) * (0 - t) ≤ 0 := by nlinarith
    have hF0 := bernF_zero h0 h1
    linarith
  · exact (bernF_zero h0 h1).ge
  · obtain ⟨ξ, hξmem, hξ⟩ := exists_deriv_eq_slope (bernF θ) hpos
      hFcont.continuousOn hFdiff.differentiableOn
    have hval : deriv (bernF θ) ξ = θ + ξ / 4 - bernRho θ ξ :=
      (bernF_hasDerivAt h0 h1 ξ).deriv
    rw [hval] at hξ
    have hξge : θ + 0 / 4 - bernRho θ 0 ≤ θ + ξ / 4 - bernRho θ ξ :=
      bernF_mono_slope h0 h1 0 ξ (le_of_lt hξmem.1)
    have hzero := bernF_slope_zero h0 h1
    have hsplit : bernF θ t - bernF θ 0
        = (θ + ξ / 4 - bernRho θ ξ) * (t - 0) := by
      rw [hξ]
      field_simp
    have hge : (0:ℝ) ≤ (θ + ξ / 4 - bernRho θ ξ) * (t - 0) := by
      nlinarith
    have hF0 := bernF_zero h0 h1
    linarith

/-- **The Bernoulli MGF step** (Hoeffding's nugget): for θ ∈ [0,1]
and any s, `1 − θ + θ·eˢ ≤ e^{θs + s²/8}`. Route: F(s) = θs + s²/8 −
log(1−θ+θeˢ) lies above its tangent at 0 (F(0) = F'(0) = 0, slope
monotone by the Bernoulli-variance bound ρ(1−ρ) ≤ 1/4). This is
the transcendental (b−a)²/8 step that round-68 recorded as absent. -/
theorem bern_mgf_bound (θ s : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 - θ + θ * Real.exp s ≤ Real.exp (θ * s + s ^ 2 / 8) := by
  rcases eq_or_lt_of_le hθ0 with rfl | h0
  · have h1 : (1:ℝ) ≤ Real.exp (s ^ 2 / 8) := Real.one_le_exp (by positivity)
    have h2 : (0:ℝ) * s + s ^ 2 / 8 = s ^ 2 / 8 := by ring
    have h3 : ((1:ℝ) - 0) + 0 * Real.exp s = 1 := by ring
    rw [h3, h2]
    exact h1
  rcases lt_or_eq_of_le hθ1 with h1' | rfl
  · have hFpos := bernF_nonneg h0 h1' s
    have hlog : Real.log (bernDenom θ s) ≤ θ * s + s ^ 2 / 8 := by
      unfold bernF at hFpos
      linarith
    have hposX : 0 < bernDenom θ s := bernDenom_pos h0 h1' s
    have hexp : 1 - θ + θ * Real.exp s
        = Real.exp (Real.log (bernDenom θ s)) := by
      have hdef : 1 - θ + θ * Real.exp s = bernDenom θ s := rfl
      rw [hdef, Real.exp_log hposX]
    rw [hexp]
    exact Real.exp_le_exp.mpr hlog
  · have h1 : ((1:ℝ) - 1) + 1 * Real.exp s = Real.exp s := by ring
    have h2 : Real.exp s ≤ Real.exp (1 * s + s ^ 2 / 8) := by
      refine Real.exp_le_exp.mpr ?_
      have h3 : (0:ℝ) ≤ s ^ 2 / 8 := by positivity
      linarith
    rw [h1]
    exact h2

/-! ## Pillar 1: Hoeffding's lemma, finite form -/

/-- The chord bound of exp on a general interval [a, b]. -/
theorem exp_chord_ab (a b x : ℝ) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp x ≤ (b - x) / (b - a) * Real.exp a
      + (x - a) / (b - a) * Real.exp b := by
  have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have w1 : (0:ℝ) ≤ (b - x) / (b - a) := by
    apply div_nonneg <;> linarith
  have w2 : (0:ℝ) ≤ (x - a) / (b - a) := by
    apply div_nonneg <;> linarith
  have hne : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have key := hconv.2 (Set.mem_univ a) (Set.mem_univ b) w1 w2 hsum
  have hm1 : ((b - x) / (b - a)) * a = ((b - x) * a) / (b - a) :=
    (div_mul_eq_mul_div _ _ _)
  have hm2 : ((x - a) / (b - a)) * b = ((x - a) * b) / (b - a) :=
    (div_mul_eq_mul_div _ _ _)
  have hcomb : ((b - x) / (b - a)) * a + ((x - a) / (b - a)) * b = x := by
    rw [hm1, hm2, ← add_div, div_eq_iff hne]
    ring
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at key
  rw [hcomb] at key
  exact key

/-- **Hoeffding's lemma, finite form (explicit endpoints)**: for a
probability vector `q` on V and logits `h` with `a ≤ h ≤ b`,
`log E_q[e^h] ≤ E_q[h] + (b−a)²/8` — the sharp constant. -/
theorem mgf_hoeffding_ab {V : Type} [Fintype V] [Nonempty V]
    (q h : V → ℝ) (hq : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (a b : ℝ) (hlo : ∀ v, a ≤ h v) (hhi : ∀ v, h v ≤ b) :
    Real.log (∑ v, q v * Real.exp (h v)) ≤ ∑ v, q v * h v + (b - a) ^ 2 / 8 := by
  have hsumpos : 0 < ∑ v, q v * Real.exp (h v) := by
    obtain ⟨v0, -, hv0ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
      rw [hq1]; exact one_ne_zero)
    have hv0pos : 0 < q v0 := lt_of_le_of_ne (hq v0) (fun hc => hv0ne hc.symm)
    exact Finset.sum_pos' (fun v _ =>
      mul_nonneg (hq v) (Real.exp_pos _).le)
      ⟨v0, Finset.mem_univ v0, mul_pos hv0pos (Real.exp_pos _)⟩
  set μ : ℝ := ∑ v, q v * h v with hμdef
  have hqa : ∑ v, q v * a = a := by
    rw [← Finset.sum_mul, hq1, one_mul]
  have hqb : ∑ v, q v * b = b := by
    rw [← Finset.sum_mul, hq1, one_mul]
  have hab : a ≤ b :=
    le_trans (hlo (Classical.arbitrary V)) (hhi (Classical.arbitrary V))
  rcases lt_or_eq_of_le hab with hablt | habeq
  · -- a < b: the chord route
    have hne : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hablt)
    have hμlo : a ≤ μ := by
      have h1 : ∑ v, q v * a ≤ ∑ v, q v * h v :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hlo v) (hq v))
      calc a = ∑ v, q v * a := hqa.symm
        _ ≤ ∑ v, q v * h v := h1
        _ = μ := hμdef.symm
    have hμhi : μ ≤ b := by
      have h1 : ∑ v, q v * h v ≤ ∑ v, q v * b :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hhi v) (hq v))
      calc μ = ∑ v, q v * h v := hμdef
        _ ≤ ∑ v, q v * b := h1
        _ = b := hqb
    have hchord : ∀ v : V, Real.exp (h v)
        ≤ (b - h v) / (b - a) * Real.exp a
          + (h v - a) / (b - a) * Real.exp b :=
      fun v => exp_chord_ab a b (h v) hablt (hlo v) (hhi v)
    have hsumle : ∑ v, q v * Real.exp (h v)
        ≤ ∑ v, q v * ((b - h v) / (b - a) * Real.exp a
          + (h v - a) / (b - a) * Real.exp b) :=
      Finset.sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (hchord v) (hq v))
    have hdistr : ∀ v : V, q v * ((b - h v) / (b - a) * Real.exp a
        + (h v - a) / (b - a) * Real.exp b)
        = q v * ((b - h v) / (b - a)) * Real.exp a
          + q v * ((h v - a) / (b - a)) * Real.exp b := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hdistr v), Finset.sum_add_distrib] at hsumle
    have hsum2 : ∑ v, q v * (b - h v) = b - μ := by
      have hsplit : ∀ v : V, q v * (b - h v) = q v * b - q v * h v :=
        fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_sub_distrib,
        ← Finset.sum_mul, hq1, one_mul, hμdef]
    have hinner : ∑ v, q v * ((b - h v) / (b - a)) = (b - μ) / (b - a) := by
      have hsplit : ∀ v : V, q v * ((b - h v) / (b - a))
          = (q v * (b - h v)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => hsplit v), ← Finset.sum_div, hsum2]
    have hpart1 : ∑ v, q v * ((b - h v) / (b - a)) * Real.exp a
        = ((b - μ) / (b - a)) * Real.exp a := by
      rw [← Finset.sum_mul, hinner]
    have hsum2' : ∑ v, q v * (h v - a) = μ - a := by
      have hsplit : ∀ v : V, q v * (h v - a) = q v * h v - q v * a :=
        fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_sub_distrib,
        ← Finset.sum_mul, hq1, one_mul, hμdef]
    have hinner' : ∑ v, q v * ((h v - a) / (b - a)) = (μ - a) / (b - a) := by
      have hsplit : ∀ v : V, q v * ((h v - a) / (b - a))
          = (q v * (h v - a)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => hsplit v), ← Finset.sum_div, hsum2']
    have hpart2 : ∑ v, q v * ((h v - a) / (b - a)) * Real.exp b
        = ((μ - a) / (b - a)) * Real.exp b := by
      rw [← Finset.sum_mul, hinner']
    rw [hpart1, hpart2] at hsumle
    have hexpb : Real.exp b = Real.exp a * Real.exp (b - a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    set θ : ℝ := (μ - a) / (b - a) with hθdef
    have hθge : (0:ℝ) ≤ θ := by
      rw [hθdef]
      apply div_nonneg <;> linarith
    have hθle : θ ≤ 1 := by
      rw [hθdef, div_le_one (by linarith : (0:ℝ) < b - a)]
      linarith
    have hchordval : ((b - μ) / (b - a)) * Real.exp a
        + ((μ - a) / (b - a)) * Real.exp b
        = Real.exp a * (1 - θ + θ * Real.exp (b - a)) := by
      rw [hexpb, hθdef]
      field_simp
      ring
    rw [hchordval] at hsumle
    have hbern := bern_mgf_bound θ (b - a) hθge hθle
    have hstep : Real.exp a * (1 - θ + θ * Real.exp (b - a))
        ≤ Real.exp (μ + (b - a) ^ 2 / 8) := by
      have h1 : Real.exp a * Real.exp (θ * (b - a) + (b - a) ^ 2 / 8)
          = Real.exp (a + (θ * (b - a) + (b - a) ^ 2 / 8)) :=
        (Real.exp_add _ _).symm
      have h2 : a + (θ * (b - a) + (b - a) ^ 2 / 8)
          = μ + (b - a) ^ 2 / 8 := by
        rw [hθdef]
        field_simp
        ring
      calc Real.exp a * (1 - θ + θ * Real.exp (b - a))
          ≤ Real.exp a * Real.exp (θ * (b - a) + (b - a) ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hbern (Real.exp_pos _).le
        _ = Real.exp (a + (θ * (b - a) + (b - a) ^ 2 / 8)) := h1
        _ = Real.exp (μ + (b - a) ^ 2 / 8) := by rw [h2]
    have hlog : Real.log (∑ v, q v * Real.exp (h v))
        ≤ μ + (b - a) ^ 2 / 8 :=
      le_trans (Real.log_le_log hsumpos (le_trans hsumle hstep)) (by
        rw [Real.log_exp])
    exact hlog
  · -- a = b: h is constant
    have hconst : ∀ v : V, h v = a := by
      intro v
      exact le_antisymm (by rw [habeq] at *; exact hhi v) (hlo v)
    have hsumc : ∑ v, q v * Real.exp (h v) = Real.exp a := by
      rw [Finset.sum_congr rfl (fun v _ => by rw [hconst v]),
        ← Finset.sum_mul, hq1, one_mul]
    have hmean : μ = a := by
      rw [hμdef, Finset.sum_congr rfl (fun v _ => by rw [hconst v]),
        ← Finset.sum_mul, hq1, one_mul]
    rw [hsumc, Real.log_exp, hmean]
    have hsq : (0:ℝ) ≤ (b - a) ^ 2 / 8 := by positivity
    linarith


/-! ## Pillar 1b: the range form -/

/-- **Hoeffding's lemma, range form**: with D dominating the
pairwise range of `h`, `log E_q[e^h] ≤ E_q[h] + D²/8`. -/
theorem mgf_hoeffding {V : Type} [Fintype V] [Nonempty V]
    (q h : V → ℝ) (hq : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : ℝ) (hD : ∀ u v, h u - h v ≤ D) :
    Real.log (∑ v, q v * Real.exp (h v)) ≤ ∑ v, q v * h v + D ^ 2 / 8 := by
  obtain ⟨wmax, -, hwmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty h
  obtain ⟨wmin, -, hwmin⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty h
  have hmaxv : ∀ v : V, h v ≤ h wmax := by
    intro v
    have hle := Finset.le_sup' (f := h) (Finset.mem_univ v)
    rw [hwmax] at hle
    exact hle
  have hminv : ∀ v : V, h wmin ≤ h v := by
    intro v
    have hle := Finset.inf'_le (f := h) (Finset.mem_univ v)
    rw [hwmin] at hle
    exact hle
  have hmain := mgf_hoeffding_ab q h hq hq1 (h wmin) (h wmax) hminv hmaxv
  have hrange : h wmax - h wmin ≤ D := hD wmax wmin
  have hpos : (0:ℝ) ≤ D := by
    have h0 : h wmin - h wmin = 0 := sub_self _
    have := hD wmin wmin
    rw [h0] at this
    exact this
  have hx0 : h wmin ≤ h wmax := by
    have hle := Finset.inf'_le (f := h) (Finset.mem_univ wmax)
    rw [hwmin] at hle
    exact hle
  have hsq : (h wmax - h wmin) ^ 2 ≤ D ^ 2 := by
    nlinarith [hrange, hpos, hx0, sq_nonneg (h wmax - h wmin), sq_nonneg D]
  have hsq8 : (h wmax - h wmin) ^ 2 / 8 ≤ D ^ 2 / 8 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  linarith

/-! ## Pillar 2: the log-sum-exp deviation bounds -/

/-- The softmax of the logits `x` over a finite vocabulary. -/
noncomputable def smax {V : Type} [Fintype V] (x : V → ℝ) : V → ℝ :=
  fun v => Real.exp (x v) / ∑ u, Real.exp (x u)

theorem sum_exp_pos {V : Type} [Fintype V] [Nonempty V] (x : V → ℝ) :
    0 < ∑ v, Real.exp (x v) :=
  Finset.sum_pos (fun _v _ => Real.exp_pos _) Finset.univ_nonempty

theorem smax_pos {V : Type} [Fintype V] [Nonempty V] (x : V → ℝ) (v : V) :
    0 < smax x v :=
  div_pos (Real.exp_pos _) (sum_exp_pos x)

theorem smax_nonneg {V : Type} [Fintype V] [Nonempty V] (x : V → ℝ) (v : V) :
    0 ≤ smax x v :=
  le_of_lt (smax_pos x v)

theorem smax_sum_one {V : Type} [Fintype V] [Nonempty V] (x : V → ℝ) :
    ∑ v, smax x v = 1 := by
  have hdiv : ∑ v, Real.exp (x v) / ∑ u, Real.exp (x u)
      = (∑ v, Real.exp (x v)) / ∑ u, Real.exp (x u) :=
    (Finset.sum_div _ _ _).symm
  unfold smax
  rw [hdiv, div_self (ne_of_gt (sum_exp_pos x))]

theorem sum_smax_exp {V : Type} [Fintype V] [Nonempty V] {x : V → ℝ}
    (g : V → ℝ) :
    ∑ v, smax x v * Real.exp (g v)
      = (∑ v, Real.exp (x v + g v)) / (∑ v, Real.exp (x v)) := by
  have hterm : ∀ v : V, smax x v * Real.exp (g v)
      = Real.exp (x v + g v) / (∑ u, Real.exp (x u)) := by
    intro v
    unfold smax
    rw [div_mul_eq_mul_div]
    congr 1
    rw [← Real.exp_add]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_div]

/-- **The supporting-hyperplane (first-order) bound for lse**:
`lse(x) + ⟨σ(x), y − x⟩ ≤ lse(y)` — exp-Jensen in the softmax
measure of `x`. -/
theorem lse_shift_lower {V : Type} [Fintype V] [Nonempty V] (x y : V → ℝ) :
    Real.log (∑ v, Real.exp (x v)) + ∑ v, smax x v * (y v - x v)
      ≤ Real.log (∑ v, Real.exp (y v)) := by
  have hZx := sum_exp_pos x
  have hZy := sum_exp_pos y
  have hjen := (convexOn_exp : ConvexOn ℝ Set.univ Real.exp).map_sum_le
    (t := Finset.univ) (w := smax x) (p := fun v => y v - x v)
    (fun v _ => smax_nonneg x v) (smax_sum_one x)
    (fun v _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjen
  have hE : ∑ v, smax x v * Real.exp (y v - x v)
      = (∑ v, Real.exp (y v)) / (∑ v, Real.exp (x v)) := by
    rw [sum_smax_exp (x := x) (fun v => y v - x v)]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by
      congr 1
      ring)
  rw [hE] at hjen
  have hlog := Real.log_le_log (Real.exp_pos _) hjen
  rw [Real.log_div (ne_of_gt hZy) (ne_of_gt hZx)] at hlog
  have hexplog : Real.log (Real.exp (∑ v, smax x v * (y v - x v)))
      = ∑ v, smax x v * (y v - x v) := Real.log_exp _
  rw [hexplog] at hlog
  linarith

/-- **The second-order (Hoeffding) bound for lse**: the deviation
`lse(y) − lse(x)` exceeds the first-order term by at most
`r²/8` whenever the range of `y − x` is dominated by r. -/
theorem lse_shift_upper {V : Type} [Fintype V] [Nonempty V] (x y : V → ℝ)
    (r : ℝ) (hr : ∀ u v, (y u - x u) - (y v - x v) ≤ r) :
    Real.log (∑ v, Real.exp (y v)) ≤ Real.log (∑ v, Real.exp (x v))
      + ∑ v, smax x v * (y v - x v) + r ^ 2 / 8 := by
  have hZx := sum_exp_pos x
  have hZy := sum_exp_pos y
  have hH := mgf_hoeffding (smax x) (fun v => y v - x v)
    (fun v => smax_nonneg x v) (smax_sum_one x) r hr
  have hE : ∑ v, smax x v * Real.exp ((fun v => y v - x v) v)
      = (∑ v, Real.exp (y v)) / (∑ v, Real.exp (x v)) := by
    rw [sum_smax_exp (x := x) (fun v => y v - x v)]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by
      congr 1
      ring)
  rw [hE] at hH
  rw [Real.log_div (ne_of_gt hZy) (ne_of_gt hZx)] at hH
  linarith


/-! ## Pillar 3: the weighted-center assembly lemma -/

/-- If each `c + ⟨q, d x⟩ ≤ F x` and the `d` are centered under
the weights ρ (`∑ ρ d = 0` pointwise), then `c ≤ ∑ ρ F` — the
Jensen-at-the-center pattern used twice in the main theorem. -/
theorem weighted_center_le {X V : Type} [Fintype X] [Fintype V] [Nonempty V]
    (F : X → ℝ) (c : ℝ) (ρ : X → ℝ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (q : V → ℝ) (_hq0 : ∀ v, 0 ≤ q v) (_hq1 : ∑ v, q v = 1)
    (d : X → V → ℝ) (hd : ∀ v, ∑ x, ρ x * (d x v) = 0)
    (hlow : ∀ x, c + ∑ v, q v * d x v ≤ F x) :
    c ≤ ∑ x, ρ x * F x := by
  have hsum : ∑ x, ρ x * (c + ∑ v, q v * d x v) ≤ ∑ x, ρ x * F x :=
    Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (hlow x) (hρ0 x))
  have hsplit : ∀ x : X, ρ x * (c + ∑ v, q v * d x v)
      = ρ x * c + ρ x * ∑ v, q v * d x v := fun x => by ring
  have hcross : ∑ x, ρ x * ∑ v, q v * d x v
      = ∑ v, q v * ∑ x, ρ x * d x v := by
    have hstep1 : ∀ x : X, ρ x * ∑ v, q v * d x v
        = ∑ v, ρ x * (q v * d x v) := fun x =>
      Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun x _ => hstep1 x), Finset.sum_comm]
    have hstep2 : ∀ v : V, ∑ x, ρ x * (q v * d x v)
        = q v * ∑ x, ρ x * d x v := by
      intro v
      rw [Finset.sum_congr rfl (fun x _ => (by ring :
        ρ x * (q v * d x v) = q v * (ρ x * d x v))), ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hstep2 v)]
  have hkey : ∑ x, ρ x * (c + ∑ v, q v * d x v)
      = ∑ x, ρ x * c + ∑ v, q v * ∑ x, ρ x * d x v := by
    rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
      hcross]
  rw [hkey, ← Finset.sum_mul, hρ1, one_mul] at hsum
  have hzero : ∑ v, q v * ∑ x, ρ x * d x v = 0 := by
    have hterm : ∀ v : V, q v * ∑ x, ρ x * d x v = 0 := by
      intro v
      rw [hd v, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    simp
  rw [hzero, add_zero] at hsum
  exact hsum

/-! ## The weighted algebra identities -/

theorem sum_w_center {K V : Type} [Fintype K] (z : K → V → ℝ) (w : K → ℝ)
    (hw1 : ∑ i, w i = 1) (v : V) :
    ∑ i, w i * (z i v - ∑ l, w l * z l v) = 0 := by
  have hsplit : ∀ i : K, w i * (z i v - ∑ l, w l * z l v)
      = w i * z i v - w i * (∑ l, w l * z l v) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
    ← Finset.sum_mul, hw1, one_mul, sub_self]

/-! ## The main theorem: the sharp per-expert (1/8)·ΣwR² law -/

/-- **R106 main theorem: PoE logZ second-order stability, SHARP
per-expert range form.** For logits `z i : V → ℝ` of experts `i`
with pool weights `w` (nonnegative, summing to 1), let

`Z_w = ∑ v exp(∑ i w i · z i v)` (the geometric-pool / PoE
partition function of `geometric_pool_identity`) and

`Z_approx = ∏ i Z_i^{w i}` with `Z_i = ∑ v exp(z i v)`
(the linear-pool fast approximation, `log Z_approx =
∑ i w i · log Z_i`).

Then the softmax-speed approximation error is bounded by the
SHARP second-order law

`|log Z_w − log Z_approx| ≤ (1/8)·∑_i w_i·(R i)²`,

where each `R i` dominates the RANGE of the centered deviation
`z i − μ` around the pooled mean `μ = ∑_l w_l·z_l`:
`∀ u v, (z i u − μ u) − (z i v − μ v) ≤ R i`.

Route (deliberately without midpoints — see the module header):
the per-expert second-order bound `lse_shift_upper` at the POOLED
MEAN `x := μ, y := z i` gives
`lse(z i) ≤ lse(μ) + ⟨σ(μ), z i − μ⟩ + (R i)²/8`; weighting by
`w i` and summing, the linear terms cancel EXACTLY — after the
sum swap, each is `σ(μ)_v · ∑_i w_i (z i v − μ v) = σ(μ)_v · 0`
by the centering identity (`sum_w_center`). The gap's sign is
`lse_shift_lower` (Jensen at the center, `weighted_center_le`).

Sharpness: two experts z₁ = (A,−A), z₂ = (−A,A), equal weights,
R = 2A: the gap is `log cosh A ~ A²/2 = R²/8` — asymptotically
tight. NOTE: the audit's pairwise form
`(1/8)·∑_{ij} w_i w_j D_ij²` is REFUTED (see `poe_logZ_pairwise`
and the module header); the per-expert range form above is the
correct sharp law, and ½ is the provable pairwise constant. -/
theorem poe_logZ_second_order {V K : Type} [Fintype V] [Nonempty V]
    [Fintype K]
    (z : K → V → ℝ) (w : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (R : K → ℝ)
    (hR : ∀ i u v,
      (z i u - ∑ l, w l * z l u) - (z i v - ∑ l, w l * z l v) ≤ R i) :
    abs (Real.log (∑ v, Real.exp (∑ i, w i * z i v))
         - ∑ i, w i * Real.log (∑ v, Real.exp (z i v)))
      ≤ (1 / 8) * ∑ i, w i * (R i) ^ 2 := by
  -- Step 1: the gap is nonnegative (Jensen at the pooled mean).
  have hgap0 : Real.log (∑ v, Real.exp (∑ l, w l * z l v))
      ≤ ∑ i, w i * Real.log (∑ v, Real.exp (z i v)) := by
    refine weighted_center_le
      (fun i => Real.log (∑ v, Real.exp (z i v)))
      (Real.log (∑ v, Real.exp (∑ l, w l * z l v))) w hw hw1
      (smax (fun v => ∑ l, w l * z l v))
      (fun v => smax_nonneg _ v) (smax_sum_one _)
      (fun i v => z i v - ∑ l, w l * z l v)
      (fun v => sum_w_center z w hw1 v)
      (fun i => lse_shift_lower (fun v => ∑ l, w l * z l v) (z i))
  -- Step 2: per-expert second-order bound at the pooled mean.
  have hper : ∀ i : K, Real.log (∑ v, Real.exp (z i v))
      ≤ Real.log (∑ v, Real.exp (∑ l, w l * z l v))
        + ∑ v, smax (fun u => ∑ l, w l * z l u) v
            * (z i v - ∑ l, w l * z l v)
        + (R i) ^ 2 / 8 := fun i =>
    lse_shift_upper (fun u => ∑ l, w l * z l u) (z i) (R i) (hR i)
  -- Step 3: weight and sum.
  have hsum : ∑ i, w i * Real.log (∑ v, Real.exp (z i v))
      ≤ ∑ i, w i * (Real.log (∑ v, Real.exp (∑ l, w l * z l v))
        + ∑ v, smax (fun u => ∑ l, w l * z l u) v
            * (z i v - ∑ l, w l * z l v)
        + (R i) ^ 2 / 8) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hper i) (hw i))
  -- Step 4: the linear term vanishes (swap sums, factor σ(μ),
  -- centering identity).
  have hlin : ∑ i, w i * ∑ v, smax (fun u => ∑ l, w l * z l u) v
      * (z i v - ∑ l, w l * z l v) = 0 := by
    have hstep1 : ∀ i : K, w i * ∑ v, smax (fun u => ∑ l, w l * z l u) v
        * (z i v - ∑ l, w l * z l v)
        = ∑ v, w i * (smax (fun u => ∑ l, w l * z l u) v
          * (z i v - ∑ l, w l * z l v)) :=
      fun i => (Finset.mul_sum _ _ _)
    have hstep2 : ∀ v : V, ∑ i, w i * (smax (fun u => ∑ l, w l * z l u) v
        * (z i v - ∑ l, w l * z l v))
        = smax (fun u => ∑ l, w l * z l u) v
          * ∑ i, w i * (z i v - ∑ l, w l * z l v) := by
      intro v
      rw [Finset.sum_congr rfl (fun i _ => (by ring :
        w i * (smax (fun u => ∑ l, w l * z l u) v
          * (z i v - ∑ l, w l * z l v))
        = smax (fun u => ∑ l, w l * z l u) v
          * (w i * (z i v - ∑ l, w l * z l v)))), ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => hstep1 i), Finset.sum_comm,
      Finset.sum_congr rfl (fun v _ => hstep2 v)]
    have hterm : ∀ v : V, smax (fun u => ∑ l, w l * z l u) v
        * ∑ i, w i * (z i v - ∑ l, w l * z l v) = 0 := by
      intro v
      rw [sum_w_center z w hw1 v, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    simp
  -- Step 5: flatten the weighted constant and tail.
  have hterm : ∀ i : K, w i * (Real.log (∑ v, Real.exp (∑ l, w l * z l v))
      + ∑ v, smax (fun u => ∑ l, w l * z l u) v
          * (z i v - ∑ l, w l * z l v)
      + (R i) ^ 2 / 8)
      = w i * Real.log (∑ v, Real.exp (∑ l, w l * z l v))
        + w i * (∑ v, smax (fun u => ∑ l, w l * z l u) v
            * (z i v - ∑ l, w l * z l v))
        + w i * ((R i) ^ 2 / 8) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hA : ∑ i, w i * Real.log (∑ v, Real.exp (∑ l, w l * z l v))
      = Real.log (∑ v, Real.exp (∑ l, w l * z l v)) := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have hRt : ∑ i, w i * ((R i) ^ 2 / 8)
      = (1 / 8) * ∑ i, w i * (R i) ^ 2 := by
    have hsplit : ∀ i : K, w i * ((R i) ^ 2 / 8)
        = (1 / 8) * (w i * (R i) ^ 2) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
  rw [hA, hlin, hRt] at hsum
  -- Step 6: assemble the absolute value (the gap is ≥ 0).
  rw [abs_of_nonpos (by linarith)]
  linarith

/-! ## Corollaries -/

/-- **Uniform-range runtime form**: if every expert's centered
deviation from the pooled mean has range ≤ M, the per-token
normalizer error of softmax-speed PoE pooling is ≤ M²/8 — compute
pooled mean logits plus the M²/8 correction, no long-exponent
products. (The audit's M²/8 per-token form is exactly this:
each expert's spread around μ is ≤ M — the K = 2 case has
μ = the midpoint, recovering the pairwise statement.) -/
theorem poe_softmax_speed {V K : Type} [Fintype V] [Nonempty V] [Fintype K]
    (z : K → V → ℝ) (w : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (M : ℝ)
    (hM : ∀ i u v,
      (z i u - ∑ l, w l * z l u) - (z i v - ∑ l, w l * z l v) ≤ M) :
    abs (Real.log (∑ v, Real.exp (∑ i, w i * z i v))
         - ∑ i, w i * Real.log (∑ v, Real.exp (z i v)))
      ≤ M ^ 2 / 8 := by
  have h := poe_logZ_second_order z w hw hw1 (fun _ => M) hM
  have hsumR : ∑ i, w i * ((fun _ => (M : ℝ)) i) ^ 2 = M ^ 2 := by
    simp only []
    rw [← Finset.sum_mul, hw1, one_mul]
  rw [hsumR] at h
  have hconv : (1 / 8) * M ^ 2 = M ^ 2 / 8 := by ring
  linarith

/-- The decomposition of the centered deviation into pairwise
differences: `z i v − μ v = ∑_j w_j (z i v − z j v)`. -/
theorem sum_w_decomp {K V : Type} [Fintype K] (z : K → V → ℝ) (w : K → ℝ)
    (hw1 : ∑ i, w i = 1) (i : K) (v : V) :
    ∑ j, w j * (z i v - z j v) = z i v - ∑ l, w l * z l v := by
  have hsplit : ∀ j : K, w j * (z i v - z j v)
      = w j * z i v - w j * z j v := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_sub_distrib,
    ← Finset.sum_mul, hw1, one_mul]

/-- **Weighted Cauchy–Schwarz / variance bound**: for probability
weights `w`, `(∑_j w_j d_j)² ≤ ∑_j w_j d_j²`. Route: double-sum
expansion plus `(d_j − d_k)² ≥ 0` (i.e. 2ab ≤ a² + b²), then the
weights sum to 1 on each side. -/
theorem weighted_var_bound {K : Type} [Fintype K] (w : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (d : K → ℝ) :
    (∑ j, w j * d j) ^ 2 ≤ ∑ j, w j * (d j) ^ 2 := by
  set Q : ℝ := ∑ j, w j * (d j) ^ 2 with hQ
  have hprod : (∑ j, w j * d j) ^ 2
      = ∑ j, ∑ k, (w j * d j) * (w k * d k) := by
    rw [sq, Finset.sum_mul_sum]
  have hterm : ∀ j k : K, (w j * d j) * (w k * d k)
      ≤ w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2 := by
    intro j k
    have hww : (0:ℝ) ≤ w j * w k := mul_nonneg (hw j) (hw k)
    have hcs : d j * d k ≤ ((d j) ^ 2 + (d k) ^ 2) / 2 := by
      have h2 : (0:ℝ) ≤ (d j - d k) ^ 2 := sq_nonneg _
      nlinarith
    calc (w j * d j) * (w k * d k)
        = w j * w k * (d j * d k) := by ring
      _ ≤ w j * w k * (((d j) ^ 2 + (d k) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hcs hww
      _ = w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2 := by ring
  have hsumle : ∑ j, ∑ k, (w j * d j) * (w k * d k)
      ≤ ∑ j, ∑ k, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2 :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
  have hsplit : ∀ j k : K, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2
      = (w j * w k * (d j) ^ 2 + w j * w k * (d k) ^ 2) / 2 :=
    fun j k => by ring
  have hf1 : ∑ j, ∑ k, w j * w k * (d j) ^ 2 = Q := by
    have hinner : ∀ j : K, ∑ k, w j * w k * (d j) ^ 2
        = w j * (d j) ^ 2 := by
      intro j
      rw [Finset.sum_congr rfl (fun k _ => (by ring :
        w j * w k * (d j) ^ 2 = w j * (d j) ^ 2 * w k)),
        ← Finset.mul_sum, hw1, mul_one]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  have hf2 : ∑ j, ∑ k, w j * w k * (d k) ^ 2 = Q := by
    have hinner : ∀ k : K, ∑ j, w j * w k * (d k) ^ 2
        = w k * (d k) ^ 2 := by
      intro k
      rw [Finset.sum_congr rfl (fun j _ => (by ring :
        w j * w k * (d k) ^ 2 = w k * (d k) ^ 2 * w j)),
        ← Finset.mul_sum, hw1, mul_one]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun k _ => hinner k)]
  have hfinal : ∑ j, ∑ k, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2
      = Q := by
    have h1 : ∀ j k : K, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2
        = w j * w k * (d j) ^ 2 / 2 + w j * w k * (d k) ^ 2 / 2 :=
      fun j k => by ring
    have hsplit : ∑ j, ∑ k, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2
        = ∑ j, ∑ k, w j * w k * (d j) ^ 2 / 2
          + ∑ j, ∑ k, w j * w k * (d k) ^ 2 / 2 := by
      rw [Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => h1 j k))]
      simp only [Finset.sum_add_distrib]
    have hdiv1 : ∑ j, ∑ k, w j * w k * (d j) ^ 2 / 2 = Q / 2 := by
      simp only [← Finset.sum_div]
      rw [hf1]
    have hdiv2 : ∑ j, ∑ k, w j * w k * (d k) ^ 2 / 2 = Q / 2 := by
      simp only [← Finset.sum_div]
      rw [hf2]
    rw [hsplit, hdiv1, hdiv2]
    ring
  calc (∑ j, w j * d j) ^ 2
      = ∑ j, ∑ k, (w j * d j) * (w k * d k) := hprod
    _ ≤ ∑ j, ∑ k, w j * w k * ((d j) ^ 2 + (d k) ^ 2) / 2 := hsumle
    _ = Q := hfinal

/-- **R106 pairwise corollary — the HONEST constant ½.** With
`D` dominating the pairwise logit diameters
(`∀ v, |z i v − z j v| ≤ D i j`),

`|log Z_w − log Z_approx| ≤ (1/2)·∑_{i,j} w_i w_j·(D_ij)²`.

Route: `R i := 2·∑_j w_j D_ij` dominates the range of the
centered deviation via the identity
`(z i u − μ u) − (z i v − μ v) = ∑_j w_j[(z i u − z j u) − (z i v − z j v)]`
(each bracket ≤ 2·D_ij by the triangle inequality), then the
weighted variance bound `weighted_var_bound` absorbs the inner
square: `(2∑_j w_j D_ij)² ≤ 4∑_j w_j D_ij²`.

**HONESTY NOTE — the audit's pairwise 1/8 constant is REFUTED**:
for z₁ = (1,−1), z₂ = (0,0), w = (½,½), the true gap is
`½·log[cosh(1)/cosh²(½)] ≈ 0.0968` (R115 numeric fix) while
`⅛·∑_{ij} w_i w_j D_ij² = 0.0625` (with D = 1) — the claimed
bound FAILS. The sharp law is the per-expert range form
(`poe_logZ_second_order`, constant 1/8); ½ is the provable
pairwise constant. -/
theorem poe_logZ_pairwise {V K : Type} [Fintype V] [Nonempty V] [Fintype K]
    (z : K → V → ℝ) (w : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (D : K → K → ℝ) (hD : ∀ i j v, abs (z i v - z j v) ≤ D i j) :
    abs (Real.log (∑ v, Real.exp (∑ i, w i * z i v))
         - ∑ i, w i * Real.log (∑ v, Real.exp (z i v)))
      ≤ (1 / 2) * ∑ i, ∑ j, w i * w j * (D i j) ^ 2 := by
  -- the per-expert range is dominated by 2·Σ_j w_j D_ij
  have hR : ∀ i u v,
      (z i u - ∑ l, w l * z l u) - (z i v - ∑ l, w l * z l v)
        ≤ 2 * ∑ j, w j * D i j := by
    intro i u v
    have hdecomp : ∀ x : V,
        z i x - ∑ l, w l * z l x = ∑ j, w j * (z i x - z j x) :=
      fun x => (sum_w_decomp z w hw1 i x).symm
    rw [hdecomp u, hdecomp v]
    have h1 : ∀ j ∈ (Finset.univ : Finset K),
        w j * (z i u - z j u) ≤ w j * D i j := by
      intro j _
      have h := abs_le.mp (hD i j u)
      exact mul_le_mul_of_nonneg_left (by linarith) (hw j)
    have h2 : ∀ j ∈ (Finset.univ : Finset K),
        w j * (-(D i j)) ≤ w j * (z i v - z j v) := by
      intro j _
      have h := abs_le.mp (hD i j v)
      exact mul_le_mul_of_nonneg_left (by linarith) (hw j)
    have hu := Finset.sum_le_sum h1
    have hv := Finset.sum_le_sum h2
    have hv' : -(∑ j, w j * D i j)
        ≤ ∑ j, w j * (z i v - z j v) := by
      have hneg : ∑ j, w j * (-(D i j))
          = -(∑ j, w j * D i j) := by
        rw [← Finset.sum_neg_distrib]
        congr 1
        exact funext fun j => by ring
      rw [hneg] at hv
      exact hv
    linarith
  have hmain := poe_logZ_second_order z w hw hw1
    (fun i => 2 * ∑ j, w j * D i j) hR
  refine le_trans hmain ?_
  -- (1/8)·Σ_i w_i (2Σ_j w_j D_ij)² ≤ (1/2)·Σ_ij w_i w_j D_ij²
  have hterm : ∀ i : K, (1 / 8) * (w i * (2 * ∑ j, w j * D i j) ^ 2)
      ≤ (1 / 2) * ∑ j, w i * w j * (D i j) ^ 2 := by
    intro i
    have hcs := weighted_var_bound w hw hw1 (fun j => D i j)
    have hwi := hw i
    have hre : ∑ j, w i * w j * (D i j) ^ 2
        = w i * ∑ j, w j * (D i j) ^ 2 := by
      rw [Finset.sum_congr rfl (fun j _ => (by ring :
        w i * w j * (D i j) ^ 2 = w i * (w j * (D i j) ^ 2))),
        ← Finset.mul_sum]
    rw [hre]
    have hmul : w i * ((2 * ∑ j, w j * D i j) ^ 2)
        ≤ w i * (4 * ∑ j, w j * (D i j) ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hwi
    nlinarith
  have hsplit : (1 / 8) * ∑ i, w i * ((fun i => 2 * ∑ j, w j * D i j) i : ℝ) ^ 2
      = ∑ i, (1 / 8) * (w i * (2 * ∑ j, w j * D i j) ^ 2) := by
    rw [Finset.mul_sum]
  have hsplit2 : (1 / 2) * ∑ i, ∑ j, w i * w j * (D i j) ^ 2
      = ∑ i, ((1 / 2) * ∑ j, w i * w j * (D i j) ^ 2) := Finset.mul_sum _ _ _
  rw [hsplit, hsplit2]
  exact Finset.sum_le_sum (fun i _ => hterm i)

/-- **R106 sequence form**: the full-sequence product composes by
summing per-token gaps — total normalizer error ≤ (1/8)·Σ_t M_t²
when every token's experts have centered range ≤ M_t. No
cross-token cancellation is claimed (honest per-token budget). -/
theorem poe_sequence_speed {T V K : Type} [Fintype T] [Fintype V]
    [Nonempty V] [Fintype K]
    (z : T → K → V → ℝ) (w : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (M : T → ℝ)
    (hM : ∀ t i u v,
      (z t i u - ∑ l, w l * z t l u) - (z t i v - ∑ l, w l * z t l v)
        ≤ M t) :
    ∑ t, abs (Real.log (∑ v, Real.exp (∑ i, w i * z t i v))
         - ∑ i, w i * Real.log (∑ v, Real.exp (z t i v)))
      ≤ (1 / 8) * ∑ t, (M t) ^ 2 := by
  have hper : ∀ t : T,
      abs (Real.log (∑ v, Real.exp (∑ i, w i * z t i v))
         - ∑ i, w i * Real.log (∑ v, Real.exp (z t i v)))
        ≤ (M t) ^ 2 / 8 :=
    fun t => poe_softmax_speed (z t) w hw hw1 (M t) (hM t)
  have hsum : ∑ t, abs (Real.log (∑ v, Real.exp (∑ i, w i * z t i v))
       - ∑ i, w i * Real.log (∑ v, Real.exp (z t i v)))
      ≤ ∑ t, (M t) ^ 2 / 8 :=
    Finset.sum_le_sum (fun t _ => hper t)
  have hrw : ∑ t, (M t) ^ 2 / 8 = (1 / 8) * ∑ t, (M t) ^ 2 := by
    rw [← Finset.sum_div]
    ring
  rw [hrw] at hsum
  exact hsum


end Hagi

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.Chord
set_option linter.style.header false

/-!
# Foundations.Hoeffding — конечная лемма Хёфдинга

Скалярное Bernoulli-MGF-ядро `(b−a)²/8` и лемма Хёфдинга в
конечной и range-формах; зависимости — только Chord.
-/

open Finset Real

namespace Hagi.Foundations

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

/-- The Bernoulli MGF step: for `θ ∈ [0,1]` and any `s`,
`1 - θ + θ * exp s ≤ exp (θ * s + s ^ 2 / 8)`. Route: the
surplus `F(s) = θs + s²/8 − log(1−θ+θeˢ)` lies above its
tangent at 0 (slope monotone by `ρ(1−ρ) ≤ 1/4`). -/
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

end Hagi.Foundations

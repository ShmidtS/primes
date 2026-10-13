/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info

/-!
# Pinsker inequality, finite form (R375)

The CMI-stage-2 workhorse (Steinke–Zakynthinou bounded-CMI ⟹
generalization route, plan §2): for distributions `q, p` on a
finite type and any `f : V → [0,1]`,

  |E_q f − E_p f| ≤ 2·√(KL(q‖p))

— the constant-4 Pinsker bound, proved WITHOUT calculus:

- KL ≥ −2·ln A where A = ∑ √(q·p) (per-term `log_le_sub_one`
  with the normalization trick — Jensen for free);
- TV ≤ 2√2·H, H² = 1 − A (Cauchy–Schwarz on √-split sums);
- A ≤ 1 (Cauchy–Schwarz);
- assembly: |Δ| ≤ 2√(2(1−A)) ≤ 2√KL.

The sharp constant-2 Pinsker needs the binary-KL calculus —
recorded as the follow-up; the CMI assembly only needs
√(C·CMI) form.
-/

open Hagi.Prelude Real
open scoped NNReal

namespace Hagi.Information

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- **Pinsker (constant 4), finite form**: for positive
distributions `q, p` (summing to 1) and any `f : V → [0,1]`,

  |∑ q·f − ∑ p·f| ≤ 2 * sqrt (klDef q p). -/
theorem pinsker4_fin (q p f : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * f v) ≤ 2 * Real.sqrt (klDef q p) := by
  classical
  set A : ℝ := ∑ v, Real.sqrt (q v * p v) with hA
  have hApos : 0 < A :=
    Finset.sum_pos (fun v _ => Real.sqrt_pos.mpr (mul_pos (hq v) (hp v)))
      Finset.univ_nonempty
  -- Σ q·√(p/q) = A
  have hsum : ∑ v, q v * Real.sqrt (p v / q v) = A := by
    rw [hA]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hL : (0:ℝ) ≤ q v * Real.sqrt (p v / q v) :=
      mul_nonneg (hq v).le (Real.sqrt_nonneg _)
    have hsq : (q v * Real.sqrt (p v / q v)) ^ 2 = q v * p v := by
      rw [mul_pow, Real.sq_sqrt (div_pos (hp v) (hq v)).le]
      field_simp
    calc q v * Real.sqrt (p v / q v)
        = Real.sqrt ((q v * Real.sqrt (p v / q v)) ^ 2) :=
          (Real.sqrt_sq hL).symm
      _ = Real.sqrt (q v * p v) := by rw [hsq]
  -- Jensen-free: Σ q ln t ≤ ln A  where Σ q t = A
  have hjensen : ∑ v, q v * Real.log (Real.sqrt (p v / q v)) ≤ Real.log A := by
    have h1 : ∀ v : V, Real.log (Real.sqrt (p v / q v) / A)
        ≤ Real.sqrt (p v / q v) / A - 1 :=
      fun v => Real.log_le_sub_one_of_pos
        (div_pos (Real.sqrt_pos.mpr (div_pos (hp v) (hq v))) hApos)
    have h2 : ∑ v, q v * (Real.sqrt (p v / q v) / A - 1) = 0 := by
      have hexp : ∀ v : V, q v * (Real.sqrt (p v / q v) / A - 1)
          = q v * Real.sqrt (p v / q v) / A - q v := by
        intro v
        ring
      rw [Finset.sum_congr rfl (fun v _ => hexp v)]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      rw [show ∑ v, q v * Real.sqrt (p v / q v) = A from hsum]
      rw [hsumq]
      field_simp
      ring
    have h3 : ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
        ≤ ∑ v, q v * (Real.sqrt (p v / q v) / A - 1) :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h1 v) (hq v).le
    rw [h2] at h3
    have h4 : ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
        = ∑ v, q v * Real.log (Real.sqrt (p v / q v)) - Real.log A := by
      have hexp : ∀ v : V,
          q v * Real.log (Real.sqrt (p v / q v) / A)
            = q v * Real.log (Real.sqrt (p v / q v)) - q v * Real.log A := by
        intro v
        rw [Real.log_div (Real.sqrt_pos.mpr (div_pos (hp v) (hq v))).ne'
          hApos.ne']
        rw [mul_sub]
        try rw [mul_div_cancel₀ (hq v).ne']
      calc ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
          = ∑ v, (q v * Real.log (Real.sqrt (p v / q v))
              - q v * Real.log A) :=
            Finset.sum_congr rfl fun v _ => hexp v
        _ = ∑ v, q v * Real.log (Real.sqrt (p v / q v))
              - ∑ v, q v * Real.log A :=
              Finset.sum_sub_distrib _ _
        _ = ∑ v, q v * Real.log (Real.sqrt (p v / q v)) - Real.log A := by
            rw [Finset.sum_congr rfl
              (fun v _ => mul_comm (q v) (Real.log A))]
            rw [← Finset.mul_sum, hsumq, mul_one]
    rw [h4] at h3
    linarith
  -- KL = 2·Σ q ln√(q/p) = -2·Σ q ln√(p/q) ≥ -2 ln A
  have hklform : klDef q p
      = -2 * ∑ v, q v * Real.log (Real.sqrt (p v / q v)) := by
    unfold klDef
    have hterm : ∀ v : V,
        q v * Real.log (q v / p v)
          = -2 * (q v * Real.log (Real.sqrt (p v / q v))) := by
      intro v
      rw [Real.log_div (hq v).ne' (hp v).ne',
        show Real.log (Real.sqrt (p v / q v))
          = Real.log (p v / q v) / 2 from
          Real.log_sqrt (div_pos (hp v) (hq v)).le,
        Real.log_div (hp v).ne' (hq v).ne']
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    try rw [← Finset.mul_sum]
  -- final KL-part: KL ≥ -2 ln A ≥ 2(1 - A)
  have hkl : 2 * (1 - A) ≤ klDef q p := by
    have hlog : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos hApos
    have hge : -2 * Real.log A ≥ -2 * (A - 1) := by nlinarith
    have h1 : -2 * (A - 1) = 2 * (1 - A) := by ring
    rw [h1] at hge
    have hklraw : -2 * Real.log A ≤ klDef q p := by
      rw [hklform]
      have hin : ∑ v, q v * Real.log (Real.sqrt (p v / q v)) ≤ Real.log A := hjensen
      nlinarith [hin]
    linarith
  -- TV part: |Eq f - Ep f| ≤ Σ_{q≥p} (q - p) =: δ ≤ 2√2·H, H² = 1 - A
  set d : V → ℝ := fun v => q v - p v with hd
  set up : V → Prop := fun v => p v ≤ q v with hup
  -- E_q f - E_p f = Σ d·f
  have hdiff : ∑ v, q v * f v - ∑ v, p v * f v = ∑ v, (q v - p v) * f v := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  -- TV machinery: F = up-set, split, bound
  letI : DecidablePred (fun v : V => p v ≤ q v) := fun v => Classical.dec _
  set F : Finset V := Finset.univ.filter (fun v => p v ≤ q v) with hF
  have hsplit : ∑ v, (q v - p v) * f v
      = (∑ v ∈ F, (q v - p v) * f v) + ∑ v ∈ Fᶜ, (q v - p v) * f v :=
    (Finset.sum_add_sum_compl F (fun v => (q v - p v) * f v)).symm
  have hcompl : ∀ v ∈ Fᶜ, (q v - p v) * f v ≤ 0 := by
    intro v hv
    have hv' : ¬ (p v ≤ q v) := by
      have h1 : v ∉ F := Finset.mem_compl.mp hv
      by_contra hc
      exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
    nlinarith [(hf v).1]
  have hcomplsum : ∑ v ∈ Fᶜ, (q v - p v) * f v ≤ 0 := Finset.sum_nonpos hcompl
  -- upper bound: Σ d f ≤ Σ_F d
  have hupper : ∑ v, (q v - p v) * f v ≤ ∑ v ∈ F, (q v - p v) := by
    have hterm : ∀ v ∈ F, (q v - p v) * f v ≤ (q v - p v) := by
      intro v hv
      have hv' : p v ≤ q v := (Finset.mem_filter.mp hv).2
      nlinarith [(hf v).2]
    calc ∑ v, (q v - p v) * f v
        = (∑ v ∈ F, (q v - p v) * f v) + ∑ v ∈ Fᶜ, (q v - p v) * f v := hsplit
      _ ≤ (∑ v ∈ F, (q v - p v)) + 0 := by
          refine add_le_add (Finset.sum_le_sum hterm) hcomplsum
      _ = ∑ v ∈ F, (q v - p v) := by ring
  -- lower bound: -Σ d f ≤ Σ_F d  (by symmetry, using Σ d = 0)
  have hsumzero : ∑ v, (q v - p v) = 0 := by
    rw [Finset.sum_sub_distrib, hsumq, hsump, sub_self]
  -- δ := Σ_F (q - p) equals Σ_{Fᶜ} (p - q), both nonneg
  have hdelta_pos : (0:ℝ) ≤ ∑ v ∈ F, (q v - p v) := by
    have hterm : ∀ v ∈ F, (0:ℝ) ≤ q v - p v := by
      intro v hv
      have := (Finset.mem_filter.mp hv).2
      linarith
    exact Finset.sum_nonneg hterm
  have hsplit0 : (∑ v ∈ F, (q v - p v)) + (∑ v ∈ Fᶜ, (q v - p v)) = 0 := by
    have := Finset.sum_add_sum_compl F (fun v => q v - p v)
    linarith [this, hsumzero]
  -- |Σ d f| ≤ δ: upper via hupper, lower via complement side
  have hlower : -(∑ v, (q v - p v) * f v) ≤ ∑ v ∈ F, (q v - p v) := by
    -- -Σ df = Σ_{Fᶜ}(p-q)f - Σ_F (q-p)f  ≤ Σ_{Fᶜ}(p-q)
    have hterm : ∀ v : V, (p v - q v) * f v = -((q v - p v) * f v) := by
      intro v; ring
    have hsplit2 : ∑ v, (p v - q v) * f v
        = (∑ v ∈ F, (p v - q v) * f v) + ∑ v ∈ Fᶜ, (p v - q v) * f v :=
      (Finset.sum_add_sum_compl F (fun v => (p v - q v) * f v)).symm
    -- Σ_F (p-q)f ≤ 0
    have hFle : ∑ v ∈ F, (p v - q v) * f v ≤ 0 := by
      refine Finset.sum_nonpos fun v hv => ?_
      have hv' : p v ≤ q v := (Finset.mem_filter.mp hv).2
      nlinarith [(hf v).1]
    -- Σ_{Fᶜ}(p-q)f ≤ Σ_{Fᶜ}(p-q)
    have hcle : ∑ v ∈ Fᶜ, (p v - q v) * f v ≤ ∑ v ∈ Fᶜ, (p v - q v) := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hv' : ¬ (p v ≤ q v) := by
        have h1 : v ∉ F := Finset.mem_compl.mp hv
        by_contra hc
        exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      nlinarith [(hf v).2]
    -- Σ_{Fᶜ}(p-q) = δ
    have hcomp : ∑ v ∈ Fᶜ, (p v - q v) = ∑ v ∈ F, (q v - p v) := by
      have hsumcompl : ∑ v ∈ Fᶜ, (q v - p v) = -(∑ v ∈ F, (q v - p v)) := by
        have hall := Finset.sum_add_sum_compl F (fun v => q v - p v)
        have htot : (∑ v ∈ F, (q v - p v)) + (∑ v ∈ Fᶜ, (q v - p v))
            = ∑ v, (q v - p v) := hall
        rw [hsumzero] at htot
        linarith
      have hneg : ∑ v ∈ Fᶜ, (p v - q v) = -(∑ v ∈ Fᶜ, (q v - p v)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [hneg, hsumcompl, neg_neg]
    -- combine: -Σdf = Σ_F(p-q)f + Σ_{Fᶜ}(p-q)f ≤ 0 + δ = δ
    have hnegform : -(∑ v, (q v - p v) * f v)
        = ∑ v, (p v - q v) * f v := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hnegform, hsplit2]
    have hstep : (∑ v ∈ F, (p v - q v) * f v)
        + ∑ v ∈ Fᶜ, (p v - q v) * f v ≤ ∑ v ∈ F, (q v - p v) := by
      have h1 := add_le_add hFle hcle
      rw [hcomp] at h1
      linarith
    exact hstep
  have habs : abs (∑ v, (q v - p v) * f v) ≤ ∑ v ∈ F, (q v - p v) :=
    abs_le.mpr ⟨by linarith, hupper⟩
  -- Cauchy: δ = Σ_F (√q-√p)(√q+√p) ≤ √(Σ_F(√q-√p)²)·√(Σ_F(√q+√p)²)
  have hcauchy : ∑ v ∈ F, (q v - p v)
      ≤ Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
    have hterm : ∀ v ∈ F, (q v - p v)
        = (Real.sqrt (q v) - Real.sqrt (p v))
          * (Real.sqrt (q v) + Real.sqrt (p v)) := by
      intro v hv
      conv_lhs => rw [show q v = (Real.sqrt (q v)) ^ 2 from
          (Real.sq_sqrt (hq v).le).symm,
        show p v = (Real.sqrt (p v)) ^ 2 from (Real.sq_sqrt (hp v).le).symm]
      rw [mul_comm, ← sq_sub_sq]
    have hrewrite : ∑ v ∈ F, (q v - p v)
        = ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v))
            * (Real.sqrt (q v) + Real.sqrt (p v)) :=
      Finset.sum_congr rfl hterm
    rw [hrewrite]
    -- Cauchy-Schwarz on F
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun v => Real.sqrt (q v) - Real.sqrt (p v))
      (fun v => Real.sqrt (q v) + Real.sqrt (p v))
    have hP0 : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 :=
      Finset.sum_nonneg fun v _ => sq_nonneg _
    have hQ0 : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 :=
      Finset.sum_nonneg fun v _ => sq_nonneg _
    have hxy : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v))
        * (Real.sqrt (q v) + Real.sqrt (p v)) := by
      rw [← hrewrite]
      exact hdelta_pos
    have hPQ : (Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)) ^ 2
        = (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
          * (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hQ0]
    have hr : (0:ℝ) ≤ Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
      positivity
    nlinarith [hxy, hPQ, hr, hsq]
  -- Σ_all (√q-√p)² = 2(1-A) ≥ Σ_F;  Σ_all (√q+√p)² = 2(1+A) ≤ 4
  have hallsub : ∑ v, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 = 2 * (1 - A) := by
    have hterm : ∀ v : V, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2
        = (q v + p v) - 2 * Real.sqrt (q v * p v) := by
      intro v
      rw [sub_sq, Real.sq_sqrt (hq v).le, Real.sq_sqrt (hp v).le,
        Real.sqrt_mul (hq v).le (p v)]
      ring
    have hsplit : ∑ v, ((q v + p v) - 2 * Real.sqrt (q v * p v))
        = (∑ v, q v + ∑ v, p v) - 2 * ∑ v, Real.sqrt (q v * p v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), hsplit, hA, hsumq, hsump]
    ring
  have halladd : ∑ v, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 = 2 * (1 + A) := by
    have hterm : ∀ v : V, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2
        = (q v + p v) + 2 * Real.sqrt (q v * p v) := by
      intro v
      rw [add_sq, Real.sq_sqrt (hq v).le, Real.sq_sqrt (hp v).le,
        Real.sqrt_mul (hq v).le (p v)]
      ring
    have hsplit : ∑ v, ((q v + p v) + 2 * Real.sqrt (q v * p v))
        = (∑ v, q v + ∑ v, p v) + 2 * ∑ v, Real.sqrt (q v * p v) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), hsplit, hA, hsumq, hsump]
    ring
  have hFsub : ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 ≤ 2 * (1 - A) := by
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun v => (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
      (Finset.subset_univ F) (fun v _ _ => sq_nonneg _)
    rw [hallsub] at hmono
    exact hmono
  have hAle : A ≤ 1 := by
    have hkey := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun v => Real.sqrt (q v)) (fun v => Real.sqrt (p v))
    have hlhs : ∑ v, Real.sqrt (q v) * Real.sqrt (p v) = A := by
      rw [hA]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Real.sqrt_mul (hq v).le (p v)]
    have hsq1 : ∑ v, (Real.sqrt (q v)) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun v _ => Real.sq_sqrt (hq v).le, hsumq]
    have hsq2 : ∑ v, (Real.sqrt (p v)) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun v _ => Real.sq_sqrt (hp v).le, hsump]
    rw [hlhs, hsq1, hsq2] at hkey
    have hpos : (0:ℝ) ≤ A := hApos.le
    calc A ≤ Real.sqrt (A ^ 2) := (Real.sqrt_sq hpos).symm.le
      _ ≤ Real.sqrt (1 * 1) := Real.sqrt_le_sqrt hkey
      _ = 1 := by norm_num
  have hFadd : ∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 ≤ 4 := by
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun v => (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)
      (Finset.subset_univ F) (fun v _ _ => sq_nonneg _)
    rw [halladd] at hmono
    have h4 : 2 * (1 + A) ≤ 4 := by linarith [hAle]
    linarith
  -- assemble: |Eq f - Ep f| ≤ δ ≤ √(2(1-A))·2 = 2√(2(1-A)) ≤ 2√KL
  have hdelta1 : ∑ v ∈ F, (q v - p v)
      ≤ 2 * Real.sqrt (2 * (1 - A)) := by
    have h1 := hcauchy
    have h2 : Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        ≤ Real.sqrt (2 * (1 - A)) := Real.sqrt_le_sqrt hFsub
    have h3 : Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)
        ≤ 2 := by
      refine le_trans (Real.sqrt_le_sqrt hFadd) ?_
      norm_num
    have hprod := mul_le_mul h2 h3 (by positivity) (by positivity)
    have hkey := le_trans hcauchy hprod
    have hsplit3 : 2 * Real.sqrt (2 * (1 - A))
        = 2 * Real.sqrt (2 * (1 - A)) := rfl
    nlinarith [hkey, Real.sqrt_nonneg (2 * (1 - A))]
  -- |Δ| ≤ 2√(2(1-A)) and 2(1-A) ≤ KL: conclude |Δ| ≤ 2√KL
  rw [hdiff]
  calc abs (∑ v, (q v - p v) * f v)
      ≤ ∑ v ∈ F, (q v - p v) := habs
    _ ≤ 2 * Real.sqrt (2 * (1 - A)) := hdelta1
    _ ≤ 2 * Real.sqrt (klDef q p) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkl) (by norm_num)

/-- **Generalization = stability + information** (R376, the
sup-pair core of the Steinke–Zakynthinou CMI proof): for
distributions `q, p` (the conditional hypothesis laws on the
two selections of a sup-pair) and losses `f, g` (evaluated on
the two points, both in [0,1]), the expected swap gap obeys

  |E_q f − E_p g| ≤ E_q|f − g| + 2·√(KL(q‖p)):

the first term is the algorithmic STABILITY of the loss under
point swap, the second is the INFORMATION the hypothesis
carries about the selection — exactly the decomposition the
bounded-CMI theorem iterates over the sample. -/
theorem gen_pair_bound (q p : V → ℝ) (f g : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (hg : ∀ v, 0 ≤ g v ∧ g v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * g v)
      ≤ ∑ v, q v * abs (f v - g v) + 2 * Real.sqrt (klDef q p) := by
  -- decompose: x = (E_q f - E_q g) + (E_q g - E_p g)
  have hsplit : ∑ v, q v * f v - ∑ v, p v * g v
      = (∑ v, q v * (f v - g v)) + ((∑ v, q v * g v) - (∑ v, p v * g v)) := by
    have h1 : ∑ v, q v * (f v - g v) = ∑ v, q v * f v - ∑ v, q v * g v := by
      rw [Finset.sum_congr rfl (fun v _ => (mul_sub (q v) (f v) (g v))),
        Finset.sum_sub_distrib]
    rw [h1]
    linarith
  -- part 1: |E_q (f−g)| ≤ E_q |f−g|
  have hpart1 : abs (∑ v, q v * (f v - g v))
      ≤ ∑ v, q v * abs (f v - g v) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : ∑ v, -(q v * abs (f v - g v)) ≤ ∑ v, q v * (f v - g v) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_abs_le _) (hq v).le
      rw [Finset.sum_neg_distrib] at h1
      exact h1
    · exact Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (le_abs_self _) (hq v).le
  -- part 2: |E_q g − E_p g| ≤ 2√KL
  have hpart2 : abs (∑ v, q v * g v - ∑ v, p v * g v)
      ≤ 2 * Real.sqrt (klDef q p) :=
    Hagi.Information.pinsker4_fin q p g hq hp hsumq hsump hg
  -- triangle assembly
  have htr : abs ((∑ v, q v * (f v - g v)) + (∑ v, q v * g v - ∑ v, p v * g v))
      ≤ abs (∑ v, q v * (f v - g v))
        + abs (∑ v, q v * g v - ∑ v, p v * g v) :=
    abs_add_le _ _
  rw [hsplit]
  exact le_trans htr (add_le_add hpart1 hpart2)

end Hagi.Information

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence

/-!
# MuonWD — weight decay replaces the bounded-gradient axiom

The R224 core (source: arXiv:2507.01598): the Muon update is
ORTHOGONALIZED — its norm is bounded by CONSTRUCTION
(spectral normalization: the msign/NS preconditioner maps
ANY gradient to a direction of uniformly bounded norm ≤ C),
INDEPENDENT of the gradient magnitude. With weight decay the
parameter recursion

  θ_{t+1} = (1 − ηλ)·θ_t − η·U_t,   ‖U_t‖ ≤ C

is a contraction with a uniformly bounded additive term:
‖θ_t‖ stays bounded FOREVER, WITHOUT any assumption that the
gradients are bounded. The bounded-gradient axiom (§3) is
discharged by (orthogonalized update + weight decay), not
assumed.

* `muon_wd_recursion`: the WD+Muon recursion is exactly the
  contraction form ρ·x + δ with ρ = 1 − ηλ, δ = η·C;
* `wd_boundedness`: the FOREVER bound — ‖θ_t‖ ≤ ρ^t·‖θ₀‖ +
  C/λ: the stationary radius C/λ is INDEPENDENT of the
  gradient scale; the axiom is gone, the price is the
  explicit WD floor C/λ;
* honesty note (no separate theorem): the bounds above use
  only the uniform C, never ‖g_t‖ — while hC holds, the
  gradient scale does not enter anywhere; a burst cannot
  push the trajectory out of the bound.
-/

namespace Hagi

open Finset

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **The WD+Muon recursion is a contraction**: with the
orthogonalized update uniformly bounded (hC — the spectral
normalization contract, source 2507.01598), η ≥ 0,
0 ≤ ηλ ≤ 1, the norm recursion is exactly ρ·x + δ with
ρ = 1 − ηλ, δ = η·C — regardless of gradient magnitudes. -/
theorem muon_wd_recursion (theta : ℕ → W) (U : ℕ → W)
    (eta lam C : ℝ) (t : ℕ)
    (heta : 0 ≤ eta) (hlam0 : 0 ≤ eta * lam)
    (hlam1 : eta * lam ≤ 1)
    (hstep : theta (t + 1) = (1 - eta * lam) • theta t
      - eta • U t)
    (hC : ∀ s, ‖U s‖ ≤ C) :
    ‖theta (t + 1)‖ ≤ (1 - eta * lam) * ‖theta t‖ + eta * C := by
  have hrho : 0 ≤ 1 - eta * lam := by linarith
  rw [hstep]
  have hU : eta * ‖U t‖ ≤ eta * C :=
    mul_le_mul_of_nonneg_left (hC t) heta
  have htri := norm_sub_le ((1 - eta * lam) • theta t) (eta • U t)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrho,
    Real.norm_eq_abs, abs_of_nonneg heta] at htri
  exact le_trans htri (by linarith)

/-- **The forever bound**: under the WD+Muon recursion with
0 ≤ ηλ < 1, the parameter norm NEVER exceeds the geometric
tail plus the stationary radius C/λ — no bounded-gradient
assumption anywhere; the price is the explicit WD floor. -/
theorem wd_boundedness (theta : ℕ → W) (U : ℕ → W)
    (eta lam C : ℝ) (T : ℕ)
    (heta : 0 ≤ eta) (hpos : 0 < eta * lam)
    (hlam1 : eta * lam ≤ 1)
    (hstep : ∀ t, theta (t + 1) = (1 - eta * lam) • theta t
      - eta • U t)
    (hC : ∀ s, ‖U s‖ ≤ C) :
    ‖theta T‖ ≤ (1 - eta * lam) ^ T * ‖theta 0‖ + C / lam := by
  have hrho : 0 ≤ 1 - eta * lam := by linarith
  have hrho1 : 1 - eta * lam < 1 := by linarith
  have hrec : ∀ t < T, ‖theta (t + 1)‖
      ≤ (1 - eta * lam) * ‖theta t‖ + eta * C :=
    fun t _ => muon_wd_recursion theta U eta lam C t heta
      hpos.le hlam1 (hstep t) hC
  have hmain := Hagi.Foundations.recurrence_upper (1 - eta * lam)
    (eta * C) (fun t => ‖theta t‖) T hrho hrho1 hrec
  have hlam : 0 < lam := by
    by_contra h
    push_neg at h
    nlinarith [heta, h]
  have hne : (1 - eta * lam) ≠ 1 := by
    intro h
    have : eta * lam = 0 := by linarith
    linarith [hpos]
  have hfrac : (1 - (1 - eta * lam) ^ T)
      / (1 - (1 - eta * lam))
      = ∑ i ∈ Finset.range T, (1 - eta * lam) ^ i := by
    rw [geom_sum_eq hne T]
    field_simp
    ring
  have hsumle : ∑ i ∈ Finset.range T, (1 - eta * lam) ^ i
      ≤ 1 / (eta * lam) := by
    have h1 := Hagi.Foundations.geom_sum_le_inv (1 - eta * lam) T
      hrho (by linarith)
    rw [sub_sub_cancel] at h1
    exact h1
  have hlampos : (0:ℝ) < lam := hlam
  have hsplit : eta * C * ((1 - (1 - eta * lam) ^ T)
      / (1 - (1 - eta * lam))) ≤ C / lam := by
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hmul : eta * C * ((1 - (1 - eta * lam) ^ T)
        / (1 - (1 - eta * lam))) ≤ eta * C * (1 / (eta * lam)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by
        exact mul_nonneg heta hC0)
      rw [hfrac]
      exact hsumle
    have hcancel : eta * C * (1 / (eta * lam)) = C / lam := by
      have hne : eta * lam ≠ 0 := ne_of_gt hpos
      have heta2 : eta ≠ 0 := by
        intro heq
        rw [heq] at hpos
        simp at hpos
      field_simp
    rw [hcancel] at hmul
    exact hmul
  linarith [hmain, hsplit]


end Hagi

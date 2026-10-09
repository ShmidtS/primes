/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence

/-!
# MuonWD — weight decay заменяет аксиому ограниченного градиента

Рекурсия `θ_{t+1} = (1 − ηλ)·θ_t − η·U_t` с равномерно
ограниченным ортогонализованным шагом `‖U_t‖ ≤ C`
(независимо от величины градиента).

* `muon_wd_recursion`: шаг нормы —
  `‖θ_{t+1}‖ ≤ (1 − ηλ)·‖θ_t‖ + η·C`;
* `wd_boundedness`: при `0 < ηλ ≤ 1` —
  `‖θ_T‖ ≤ (1 − ηλ)^T·‖θ_0‖ + C/λ`: стационарный радиус C/λ
  не зависит от масштаба градиентов (аксиома ограниченности
  градиентов не нужна; цена — явный WD-пол).
-/

namespace Hagi

open Finset

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- При `0 ≤ eta`, `0 ≤ eta·lam ≤ 1`, шаге
`θ (t+1) = (1 − eta·lam) • θ t − eta • U t` и
`‖U s‖ ≤ C` для всех s —
`‖θ (t+1)‖ ≤ (1 − eta·lam)·‖θ t‖ + eta·C`. -/
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

/-- При `0 ≤ eta`, `0 < eta·lam ≤ 1`, шаге
`θ (t+1) = (1 − eta·lam) • θ t − eta • U t` и
`‖U s‖ ≤ C` —
`‖θ T‖ ≤ (1 − eta·lam)^T·‖θ 0‖ + C/lam`. -/
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

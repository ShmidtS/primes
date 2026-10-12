/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# Weight decay as an implicit norm constraint (R372)

Formal core of the weight-decay-as-regularizer view
(plan §2; arXiv:2507.01598 family): the update
`w(t+1) = (1 − ηλ)·w(t) − η·g(t)` with `ηλ ∈ [0,1]` and
gradients bounded by `G` keeps the weights inside the FIXED
ball `max(‖w(0)‖, G/λ)` forever — no external bounded-weight
axiom: the decay term ITSELF enforces the norm constraint
(the implicit spectral-norm-constraint equivalence). The
invariant is self-repairing: the contraction (1 − ηλ) pulls
the norm back toward the budget `G/λ`.
-/

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Weight-decay norm invariant**: under the decaying SGD
update with `0 ≤ ηλ ≤ 1`, `λ > 0` and gradients uniformly
bounded by `G`, the whole trajectory stays in the ball
`max(‖w 0‖, G/λ)` — weight decay IS the norm constraint. -/
theorem wd_norm_bound (w g : ℕ → X) (eta lam G : ℝ)
    (hlam : 0 < lam) (hetal : 0 ≤ eta * lam) (hetau : eta * lam ≤ 1)
    (hG : ∀ t, ‖g t‖ ≤ G)
    (hrec : ∀ t, w (t + 1) = (1 - eta * lam) • (w t) - eta • (g t))
    (t : ℕ) :
    ‖w t‖ ≤ max ‖w 0‖ (G / lam) := by
  have heta : (0:ℝ) ≤ eta := by
    by_contra hc
    have hlt : eta < 0 := by linarith
    have hn : eta * lam < 0 := by nlinarith
    linarith [hetal]
  have hcontr : (0:ℝ) ≤ 1 - eta * lam := by linarith
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
      set M := max (norm (w 0)) (G / lam) with hM
      have hstep : ‖w (t + 1)‖
          ≤ (1 - eta * lam) * ‖w t‖ + eta * G := by
        calc ‖w (t + 1)‖
            = ‖(1 - eta * lam) • (w t) - eta • (g t)‖ := by
              rw [hrec t]
          _ ≤ ‖(1 - eta * lam) • (w t)‖ + ‖eta • (g t)‖ :=
              norm_sub_le _ _
          _ = (1 - eta * lam) * ‖w t‖ + eta * ‖g t‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg hcontr,
                Real.norm_of_nonneg heta]
          _ ≤ (1 - eta * lam) * ‖w t‖ + eta * G := by
              gcongr
              exact hG t
      rcases lt_or_ge (lam * M) G with hGM | hGM
      · -- the ball IS the budget: lam * M < G
        have hMle : M ≤ G / lam := by
          rw [le_div_iff₀ hlam]
          nlinarith
        have hchain : ‖w t‖ ≤ G / lam := ih.trans hMle
        have hsplit : (1 - eta * lam) * ‖w t‖ + eta * G
            ≤ (1 - eta * lam) * (G / lam) + eta * G := by
          gcongr
          try exact hchain
        have hcancel : (1 - eta * lam) * (G / lam) + eta * G
            = G / lam := by
          have hkey : (eta * lam) * (G / lam) = eta * G := by
            field_simp
          nlinarith [hkey]
        refine hstep.trans
          (hsplit.trans (le_of_eq hcancel) |>.trans (le_max_right _ _))
      · -- gradient budget fits inside the invariant ball
        have h2 : eta * G ≤ eta * (lam * M) :=
          mul_le_mul_of_nonneg_left hGM heta
        have h3 : eta * (lam * M) = eta * lam * M := by ring
        rw [h3] at h2
        refine hstep.trans ?_
        nlinarith [ih, h2, mul_nonneg hcontr (norm_nonneg (w t))]

end Hagi.Step

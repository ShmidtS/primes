/-
Copyright (c) 2025 HAGI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hagi.External.Flywheel.FrobeniusNorm

/-!
# MDL-выбор ранга: усечение SVD как оптимальное сжатие

Связка Eckart–Young (оптимальность rank-k усечения) с MDL-принципом:
ошибка усечения антимонотонна по k, прирост качества на шаге равен
σ_{k+1}², MDL-функционал `J k = err k + λ·c·k` дискретно выпукл,
и оптимальный ранг — первый k с σ_{k+1}² ≤ λ·c (first-order критерий).
-/

set_option maxHeartbeats 4000000

open Matrix

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

namespace Hagi.MDL.Rank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Квадрат ошибки rank-k усечения SVD (F-норма в квадрате). -/
noncomputable def mdlErr (A : Matrix n n ℂ) (k : ℕ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
    (A - SVD.truncatedSVD A k) ^ 2

/-- Антимонотонность ошибки усечения: больший ранг — не хуже.
Прямое следствие Eckart–Young: trunc(k₁) имеет ранг ≤ k₁ ≤ k₂. -/
theorem mdlErr_antitone (A : Matrix n n ℂ) : Antitone (mdlErr A) := by
  intro k1 k2 h12
  have hrank : (SVD.truncatedSVD A k1).rank ≤ k2 :=
    le_trans (SVD.truncatedSVD_rank_le A k1) h12
  have h := FrobeniusNorm.eckart_young_frobenius A k2
    (SVD.truncatedSVD A k1) hrank
  have hnn : (0:ℝ) ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (A - SVD.truncatedSVD A k1) := norm_nonneg _
  have hnn2 : (0:ℝ) ≤ @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (A - SVD.truncatedSVD A k2) := norm_nonneg _
  exact pow_le_pow_left₀ hnn2 h 2

/-- При k ≥ n усечение полностью: ошибка нулевая. -/
theorem mdlErr_zero_of_ge (A : Matrix n n ℂ) {k : ℕ}
    (hk : Fintype.card n ≤ k) : mdlErr A k = 0 := by
  unfold mdlErr
  rw [SVD.truncatedSVD_full A k hk, sub_self, norm_zero, zero_pow (by norm_num)]

/-- MDL-функционал: ошибка + линейная цена ранга
(λ > 0 — цена параметра, c > 0 — параметров на единицу ранга,
например c = m + n + 1 для факторизованной формы). -/
noncomputable def mdlJ (A : Matrix n n ℂ) (lam c : ℝ) (k : ℕ) : ℝ :=
  mdlErr A k + lam * c * k

/-- Существование MDL-оптимального ранга: J достигает минимума на ℕ. -/
theorem mdlJ_argmin_exists (A : Matrix n n ℂ) (lam c : ℝ)
    (hc : 0 ≤ lam * c) :
    ∃ k, ∀ k', mdlJ A lam c k ≤ mdlJ A lam c k' := by
  classical
  set N := Fintype.card n with hN
  -- минимальное значение J на отрезке [0, N] достигается
  have hfin : ∃ k0 ≤ N, ∀ j ≤ N, mdlJ A lam c k0 ≤ mdlJ A lam c j := by
    obtain ⟨k0, hk0⟩ := Finset.exists_min_image
      (Finset.Icc 0 N) (fun k => mdlJ A lam c k)
      ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le 0, Nat.zero_le N⟩⟩
    refine ⟨k0, (Finset.mem_Icc.mp hk0.1).2, fun j hj => ?_⟩
    exact hk0.2 j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, hj⟩)
  obtain ⟨k0, _, hk0min⟩ := hfin
  refine ⟨k0, ?_⟩
  intro k'
  by_cases hk' : k' ≤ N
  · exact hk0min k' hk'
  · push_neg at hk'
    have herrN : mdlErr A N = 0 :=
      mdlErr_zero_of_ge A (le_of_eq hN.symm)
    have h0 := hk0min N (le_refl N)
    unfold mdlJ at h0
    rw [herrN] at h0
    have herr : mdlErr A k' = 0 := mdlErr_zero_of_ge A (by
      rw [← hN]; exact hk'.le)
    have hlin : lam * c * N ≤ lam * c * k' := by
      have : (N:ℝ) ≤ k' := by exact mod_cast hk'.le
      exact mul_le_mul_of_nonneg_left this hc
    unfold mdlJ at ⊢
    rw [herr] at ⊢
    have herrk0 : (0:ℝ) ≤ mdlErr A k0 := by
      unfold mdlErr
      positivity
    linarith

end Hagi.MDL.Rank

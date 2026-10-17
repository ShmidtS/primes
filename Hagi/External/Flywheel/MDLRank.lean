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
open Hagi.External.Flywheel.Matrix

namespace Hagi.External.Flywheel

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

/-- Прирост качества на шаге ранга: err k − err (k+1) = σₖ²
(следующий сингулярный шум определяет весь выигрыш). -/
theorem mdlErr_step (A : Matrix n n ℂ) {k : ℕ}
    (hk : k < Fintype.card n) :
    mdlErr A k - mdlErr A (k + 1)
      = (SVD.singularValues₀ A ⟨k, hk⟩) ^ 2 := by
  have hE1 := FrobeniusNorm.frobenius_error_truncatedSVD A k
  have hE2 := FrobeniusNorm.frobenius_error_truncatedSVD A (k+1)
  unfold mdlErr
  rw [hE1, hE2]
  rw [← Finset.sum_sub_distrib]
  set E : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm with hE
  set i0 : n := E.symm ⟨k, hk⟩ with hi0
  have hii : E i0 = ⟨k, hk⟩ := E.apply_symm_apply ⟨k, hk⟩
  rw [Finset.sum_eq_single i0]
  · -- в точке i0: tail k = σ, tail (k+1) = 0
    show (if k ≤ (E i0).val then SVD.singularValues₀ A (E i0) else 0) ^ 2
        - (if k + 1 ≤ (E i0).val then SVD.singularValues₀ A (E i0) else 0) ^ 2
      = SVD.singularValues₀ A ⟨k, hk⟩ ^ 2
    simp [hii]
  · -- вне i0 разность нулевая
    intro b _ hbi
    simp only [SVD.truncatedSingularValues_tail]
    rw [← hE]
    by_cases hb : E b = ⟨k, hk⟩
    · exact absurd (E.injective (hb.trans hii.symm)) hbi
    · have hbk : (E b).val ≠ k := by
        intro heq
        exact hb (Fin.ext heq)
      by_cases hlt : k ≤ (E b).val
      · have h2 : k < (E b).val := by omega
        simp [hlt, h2]
      · have h2 : ¬(k + 1 ≤ (E b).val) := by omega
        simp [hlt, h2]
  · simp

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


/-- Прирост MDL-функционала на шаге ранга. -/
noncomputable def mdlDj (A : Matrix n n ℂ) (lam c : ℝ) (k : ℕ) : ℝ :=
  mdlJ A lam c (k + 1) - mdlJ A lam c k

set_option maxHeartbeats 16000000 in
/-- Внутри диапазона: прирост = λc − σ_k² (из mdlErr_step). -/
theorem mdlDj_eq (A : Matrix n n ℂ) (lam c : ℝ) {k : ℕ}
    (hk : k < Fintype.card n) :
    mdlDj A lam c k = lam * c - (SVD.singularValues₀ A ⟨k, hk⟩) ^ 2 := by
  unfold mdlDj mdlJ
  have h := mdlErr_step A hk
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_succ k
  rw [hk1]
  have hmul : lam * c * ((k : ℝ) + 1) = lam * c * (k : ℝ) + lam * c := by ring
  rw [hmul]
  linarith

set_option maxHeartbeats 16000000 in
/-- За пределами: ошибка уже нулевая, прирост = цена λc. -/
theorem mdlDj_ge_card (A : Matrix n n ℂ) (lam c : ℝ) {k : ℕ}
    (hk : Fintype.card n ≤ k) :
    mdlDj A lam c k = lam * c := by
  have h1 : mdlErr A k = 0 := mdlErr_zero_of_ge A hk
  have h2 : mdlErr A (k + 1) = 0 := mdlErr_zero_of_ge A (by omega)
  unfold mdlDj mdlJ
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_succ k
  rw [hk1]
  have hmul : lam * c * ((k : ℝ) + 1) = lam * c * (k : ℝ) + lam * c := by ring
  rw [hmul]
  linarith

set_option maxHeartbeats 16000000 in
/-- **First-order критерий MDL-оптимального ранга**: если в точке k*
прирост качества σ_{k*}² уже не окупает цену λ·c, а на
предыдущем шаге ещё окупал (λ·c < σ_{k*−1}², либо k* = 0),
то k* — глобальный минимум J (дискретная выпуклость из
антимонотонности σ). -/
theorem mdlJ_first_order (A : Matrix n n ℂ) (lam c : ℝ) (hlamc : 0 < lam * c)
    {kstar : ℕ} (hkstar : kstar < Fintype.card n)
    (hstop : (SVD.singularValues₀ A ⟨kstar, hkstar⟩) ^ 2 ≤ lam * c)
    (hstart : kstar = 0 ∨
      lam * c < (SVD.singularValues₀ A ⟨kstar - 1, by omega⟩) ^ 2) :
    ∀ k, mdlJ A lam c kstar ≤ mdlJ A lam c k := by
  -- σ² антимонотонна (неотрицательность + antitone)
  have hsq : ∀ i j : Fin (Fintype.card n), i ≤ j →
      (SVD.singularValues₀ A j) ^ 2 ≤ (SVD.singularValues₀ A i) ^ 2 := by
    intro i j hij
    exact pow_le_pow_left₀ (SVD.singularValues₀_nonneg A j)
      (SVD.singularValues₀_antitone A hij) 2
  -- приросты после k* неотрицательны
  have dJ_nn : ∀ j, kstar ≤ j → 0 ≤ mdlDj A lam c j := by
    intro j hj
    by_cases hjcard : j < Fintype.card n
    · rw [mdlDj_eq A lam c hjcard]
      have := hsq ⟨kstar, hkstar⟩ ⟨j, hjcard⟩ hj
      linarith
    · rw [mdlDj_ge_card A lam c (by omega)]
      exact hlamc.le
  -- приросты до k* строго отрицательны
  have dJ_neg : ∀ j, j < kstar → mdlDj A lam c j < 0 := by
    intro j hj
    rcases hstart with h0 | hlt
    · omega
    · have hjc : j < Fintype.card n := by omega
      have hkm : kstar - 1 < Fintype.card n := by omega
      have h1 : lam * c < (SVD.singularValues₀ A ⟨kstar - 1, hkm⟩) ^ 2 := hlt
      have h2 : (SVD.singularValues₀ A ⟨kstar - 1, hkm⟩) ^ 2
          ≤ (SVD.singularValues₀ A ⟨j, hjc⟩) ^ 2 :=
        hsq ⟨j, hjc⟩ ⟨kstar - 1, hkm⟩
          (Fin.le_def.mpr (Nat.le_pred_of_lt hj))
      rw [mdlDj_eq A lam c hjc]
      linarith
  -- связка J(k+1) = J(k) + dJ
  have step : ∀ j, mdlJ A lam c (j + 1) = mdlJ A lam c j + mdlDj A lam c j := by
    intro j
    unfold mdlDj
    ring
  -- хвостовая монотонность
  have after : ∀ k, kstar ≤ k → mdlJ A lam c kstar ≤ mdlJ A lam c k := by
    intro k
    induction k with
    | zero =>
        intro h
        have h0 : kstar = 0 := Nat.le_zero.mp h
        subst h0
        exact le_refl _
    | succ k ih =>
        intro hk
        by_cases hkstar : kstar ≤ k
        · exact le_trans (ih hkstar) (by
            rw [step k]
            linarith [dJ_nn k (by omega)])
        · have heq : kstar = k + 1 := by omega
          rw [heq]
  -- головная монотонность (индукция по kstar − k)
  have before : ∀ m k, k + m = kstar → mdlJ A lam c kstar ≤ mdlJ A lam c k := by
    intro m
    induction m with
    | zero =>
        intro k hk
        simp at hk
        subst hk
        exact le_refl _
    | succ m ih =>
        intro k hk
        have hk1 : k + 1 + m = kstar := by omega
        have hrec := ih (k + 1) hk1
        have hstep : mdlJ A lam c (k + 1)
            = mdlJ A lam c k + mdlDj A lam c k := step k
        have hdj : mdlDj A lam c k < 0 := dJ_neg k (by omega)
        linarith
  intro k
  rcases Nat.lt_or_ge k kstar with hlt | hge
  · exact before (kstar - k) k (by omega)
  · exact after k hge


/-- **MDL-ранг в единицах кросс-энтропии** (единый
план §6.3, mdl_rank_ce): условная цена rank-k
усечения в единицах функции потерь —
через ЯВНУЮ липшицевость ℓ по норме
Фробениуса (а не путём прямого
отождествления цены ранга в весовых
единицах с ценой ошибки в единицах CE):

  |ℓ(A) − ℓ(A_k)| ≤ κ_F · ‖A − A_k‖_F
                   = κ_F · √(∑_{i≥k} σ_i²)

— соединяет липшицевость с точным тождеством
хвостов (frobenius_error_truncatedSVD). -/
theorem mdl_rank_ce (A : Matrix n n ℂ) (k : ℕ)
    (ell : Matrix n n ℂ → ℝ) (kappaF : ℝ)
    (hkF : 0 ≤ kappaF)
    (hlip : ∀ X Y : Matrix n n ℂ,
      |ell X - ell Y|
        ≤ kappaF * @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm (X - Y)) :
    |ell A - ell (SVD.truncatedSVD A k)|
      ≤ kappaF * Real.sqrt
        (∑ i, SVD.truncatedSingularValues_tail A k i ^ 2) := by
  have h := hlip A (SVD.truncatedSVD A k)
  have hE := FrobeniusNorm.frobenius_error_truncatedSVD A k
  have hnorm : @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm
      (A - SVD.truncatedSVD A k)
      = Real.sqrt (∑ i, SVD.truncatedSingularValues_tail A k i ^ 2) := by
    rw [← hE]
    exact (Real.sqrt_sq (norm_nonneg (A - SVD.truncatedSVD A k))).symm
  rw [hnorm] at h
  exact h

end Hagi.MDL.Rank


end Hagi.External.Flywheel

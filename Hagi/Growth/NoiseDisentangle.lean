/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Foundations.Recurrence

/-!
# NoiseDisentangle — разделение шума и полезного разногласия при merge

Разложение `W i = W_shared + u i + n i`, где шум `n i`
попарно ортогонален и равной энергии `σ²`, а полезное
разногласие `u i` — нет.

* `orthogonal_noise_averaging`: энергия усреднённого шума
  равна точно `σ²/N`;
* `disagreement_convergence_floor`: если
  `Dseq (t+1) ≤ κ·Dseq t + σ²/N` (κ < 1), то
  `Dseq t ≤ κ^t·D₀ + (σ²/N)(1 − κ^t)/(1 − κ)`;
* `fiber_merge_denoise`: при merge с сохранением fiber
  (усредняется только shared-часть) ошибка эксперта i
  равна `avgVec n − n i` и её энергия — точно
  `σ²·(1 − 1/N) < σ²`.
-/

open scoped BigOperators
open InnerProductSpace

namespace Hagi.Growth

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Если векторы `n i` попарно ортогональны и
`‖n i‖² = σ²`, то `‖N⁻¹ • Σ n i‖² = σ²/N`. -/
theorem orthogonal_noise_averaging {N : ℕ} [NeZero N]
    (σ : ℝ) (n : Fin N → V)
    (hortho : ∀ i j, i ≠ j → ⟪n i, n j⟫_ℝ = 0)
    (henergy : ∀ i, ‖n i‖ ^ 2 = σ ^ 2) :
    ‖(N : ℝ)⁻¹ • ∑ i, n i‖ ^ 2 = σ ^ 2 / N := by
  have hsumsq : ‖∑ i, n i‖ ^ 2 = ∑ i, ‖n i‖ ^ 2 := by
    have hexp : ‖∑ i, n i‖ ^ 2
        = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ := by
      have h1 : ⟪∑ i, n i, ∑ j, n j⟫_ℝ
          = ∑ i, ⟪∑ j, n j, n i⟫_ℝ :=
        inner_sum (𝕜 := ℝ) Finset.univ n (∑ j, n j : V)
      have h2 : ∀ i : Fin N, ⟪∑ j, n j, n i⟫_ℝ
          = ∑ j, ⟪n j, n i⟫_ℝ := by
        intro i
        calc ⟪∑ j, n j, n i⟫_ℝ
            = ⟪n i, ∑ j, n j⟫_ℝ := real_inner_comm _ _
        _ = ∑ j, ⟪n i, n j⟫_ℝ :=
              inner_sum (𝕜 := ℝ) Finset.univ n (n i)
        _ = ∑ j, ⟪n j, n i⟫_ℝ :=
              Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)
      have h3 : ∀ i : Fin N,
          ∑ j, ⟪n j, n i⟫_ℝ = ∑ j, ⟪n i, n j⟫_ℝ := by
        intro i
        exact Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)
      calc ‖∑ i, n i‖ ^ 2
          = ⟪∑ i, n i, ∑ j, n j⟫_ℝ :=
            (@inner_self_eq_norm_sq ℝ V _ _ _ (∑ i, n i)).symm
      _ = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ := by
            have h4 : ∑ i, ⟪∑ j, n j, n i⟫_ℝ
                = ∑ i, ∑ j, ⟪n i, n j⟫_ℝ :=
              Finset.sum_congr rfl (fun i _ => by
                rw [h2 i, h3 i])
            rw [h1, h4]
    have hkill : ∀ i, ∑ j, ⟪n i, n j⟫_ℝ = ‖n i‖ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · exact real_inner_self_eq_norm_sq (n i)
      · intro j _ hij
        exact hortho i j (fun heq => hij heq.symm)
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    rw [hexp, Finset.sum_congr rfl (fun i _ => hkill i)]
  have hNpos : (0:ℝ) < (N : ℝ) := by
    have h := (inferInstance : NeZero N).out
    exact_mod_cast Nat.pos_of_ne_zero h
  have hnorminv : ‖((N : ℝ))⁻¹‖ ^ 2 = ((N : ℝ)) ⁻¹ ^ 2 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hNpos]
  rw [norm_smul, mul_pow, hnorminv, hsumsq]
  rw [Finset.sum_congr rfl (fun i _ => henergy i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- Если `0 ≤ κ < 1` и `Dseq (t+1) ≤ κ·Dseq t + σ²/N`, то
`Dseq t ≤ κ^t·D₀ + (σ²/N)·(1 − κ^t)/(1 − κ)`. -/
theorem disagreement_convergence_floor (κ σ : ℝ) (N : ℕ)
    (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hσ : 0 ≤ σ)
    (Dseq : ℕ → ℝ) (hD0 : Dseq 0 ≤ D₀)
    (hstep : ∀ t, Dseq (t + 1) ≤ κ * Dseq t + σ ^ 2 / N) :
    ∀ t, Dseq t ≤ κ ^ t * D₀
      + (σ ^ 2 / N * (1 - κ ^ t)) / (1 - κ) :=
  Hagi.Foundations.genGap_decay κ (σ ^ 2 / N) D₀ hκ hκ1
    (by positivity) Dseq hD0 hstep

/-- Усреднение семейства векторов: `avgVec v = N⁻¹ • Σ v i`. -/
noncomputable def avgVec {N : ℕ} (v : Fin N → V) : V :=
  ((N : ℝ))⁻¹ • ∑ i, v i

/-- Для `W i = M + u i + n i` merge с сохранением fiber даёт
`(M + avgVec n + u i) − (M + u i + n i) = avgVec n − n i`, и
при попарно ортогональном шуме равной энергии `σ²`
энергия ошибки равна точно `σ²·(1 − 1/N)`. -/
theorem fiber_merge_denoise {N : ℕ} [NeZero N]
    (σ : ℝ) (n : Fin N → V)
    (hortho : ∀ i j, i ≠ j → ⟪n i, n j⟫_ℝ = 0)
    (henergy : ∀ i, ‖n i‖ ^ 2 = σ ^ 2)
    (M : V) (u : Fin N → V) (i : Fin N) :
    -- ошибка merge — это остаток шума
    (M + avgVec n + u i) - (M + u i + n i) = avgVec n - n i
    -- и его энергия — точно sigma^2 * (1 - 1/N)
    ∧ ‖avgVec n - n i‖ ^ 2 = σ ^ 2 * (1 - 1 / (N : ℝ)) := by
  constructor
  · simp only [avgVec]
    abel
  · -- inner cross term: <n-bar, n i> = sigma^2 / N
    have hcross : ⟪avgVec n, n i⟫_ℝ = σ ^ 2 / (N : ℝ) := by
      simp only [avgVec, inner_smul_left, smul_eq_mul, map_inv,
        RCLike.conj_to_real]
      rw [real_inner_comm (n i) (∑ i, n i), inner_sum]
      rw [Finset.sum_eq_single i]
      · rw [real_inner_self_eq_norm_sq, henergy i]
        field_simp
      · intro j _ hij
        rw [real_inner_comm, hortho j i hij]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    -- energy by expansion
    have hnb : ‖avgVec n‖ ^ 2 = σ ^ 2 / (N : ℝ) :=
      orthogonal_noise_averaging σ n hortho henergy
    have hexp : ‖avgVec n - n i‖ ^ 2
        = ‖avgVec n‖ ^ 2 - 2 * ⟪avgVec n, n i⟫_ℝ + ‖n i‖ ^ 2 :=
      norm_sub_pow_two_real (avgVec n) (n i)
    rw [hexp, hnb, hcross, henergy i]
    field_simp
    ring

end Hagi.Growth

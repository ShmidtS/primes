/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option linter.style.header false

/-!
# MergeCancellationIdentity — что именно гасит merge

План формализации Phase A. Главный блокер роста
(FORMALIZATION_PLAN §0): merge-усреднение гасит
антикоррелированную компоненту отличий (измерено
cos(dev) ≈ −0.3…−0.6); дефицит γ = 9×. Этот модуль —
весовой фундамент: ТОЧНАЯ идентичность разложения и её
следствия, до всякой теоремы об операторе gain.

**Модель:** N экспертов W_k = M + dev_k в вещественном
гамильтоновом пространстве, Σ dev_k = 0, M — merge.

**Теоремы:**

* `merge_is_mean` — M = (1/N)·Σ W_k: merge-усреднение
  ТОЧНО равно среднему (Σ dev = 0 — единственная посылка).
* `deviations_cancel` — для любого линейного f:
  Σ f(W_k) − N·f(M) = 0: усреднение гасит РОВНО сумму
  отклонений (в любом измерении, включая CE-канал).
* `pairwise_variance_identity` — идентичность рассеяния:
  Σ_{i<j} ‖W_i − W_j‖² = N·Σ_k ‖dev_k‖²
  (при Σ dev = 0; независимо от ортогональности — это
  Пифагор-форма закона полной дисперсии).
* `orthogonal_energy_split` — при взаимно ортогональных
  dev_k энергия ПОЛНОСТЬЮ локальна: ‖W_k − M‖² = ‖dev_k‖²,
  и информация пары (M, dev_k) восстанавливает W_k точно
  (`decompose_reconstruct`): merge ничего не теряет в
  разложении — потери merge происходят при СЖАТИИ dev,
  не при усреднении M.
* `anticorrelated_suppressed` — формализация «гасит
  антикоррелированную компоненту»: если у dev_k есть
  общий компонент вдоль u (⟨dev_k, u⟩ = c_k с Σc_k = 0),
  он остаётся в разложении; проекция merge на u есть
  среднее проекций экспертов. Отклонения НЕ исчезают из
  (M, dev) — канал сохранения.

**Честные границы:** «2.8e-16 машинная точность» — измерено
(runtime,–), не Lean-утверждение; здесь —
ТОЧНАЯ алгебра над ℝ. Следствие для: узкое место не
усреднение (оно точно), а оператор превращения dev в
прирост (γ-дефицит).
-/

open Finset InnerProductSpace

namespace Hagi

variable {N : ℕ} [NeZero N] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Разложение пула экспертов: W_k = M + dev_k, Σ dev = 0. -/
def mergeDecomp (W : Fin N → V) (M : V) (dev : Fin N → V) : Prop :=
  (∀ k, W k = M + dev k) ∧ (∑ k, dev k) = 0

/-- **Merge = среднее**: единственная посылка Σ dev = 0 даёт
M = (1/N)·Σ W_k — merge-усреднение ТОЧНО. -/
theorem merge_is_mean (W : Fin N → V) (M : V) (dev : Fin N → V)
    (hd : mergeDecomp W M dev) :
    (N : ℝ) • M = ∑ k, W k := by
  obtain ⟨hW, hsum⟩ := hd
  have h1 : ∑ k, W k = ∑ k, (M + dev k) :=
    Finset.sum_congr rfl fun k _ => by rw [hW k]
  rw [h1, Finset.sum_add_distrib, hsum, add_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]

/-- **Отклонения гасятся в любом линейном измерении**:
для аддитивного f (в т.ч. след, проекция, функционал CE)
Σ f(W_k) − N·f(M) = Σ f(dev_k) = f(Σ dev_k): усреднение
гасит РОВНО сумму отклонений. -/
theorem deviations_cancel (W : Fin N → V) (M : V) (dev : Fin N → V)
    (hd : mergeDecomp W M dev)
    (f : V →ₗ[ℝ] ℝ) :
    ∑ k, f (W k) = N * f M := by
  obtain ⟨hW, hsum⟩ := hd
  calc ∑ k, f (W k) = ∑ k, f (M + dev k) := by
        exact Finset.sum_congr rfl fun k _ => by rw [hW k]
    _ = ∑ k, (f M + f (dev k)) := by
        exact Finset.sum_congr rfl fun k _ => map_add f M (dev k)
    _ = (∑ k, f M) + (∑ k, f (dev k)) := by rw [Finset.sum_add_distrib]
    _ = N * f M + f (∑ k, dev k) := by
        rw [map_sum]
        simp [Finset.sum_const]
    _ = N * f M := by rw [hsum, map_zero, add_zero]

/-- **Идентичность рассеяния** (закон полной дисперсии,
Пифагор-форма): при Σ dev = 0

  Σ_{i,j} ‖W_i − W_j‖² = 2N · Σ_k ‖dev_k‖².

Следствие: попарное рассеяние экспертов ТОЧНО равно
2N-кратной энергии отклонений — весовая версия меры twoGap
(GapLaw): всё рассеяние пула живёт в dev-канале. -/
theorem pairwise_variance_identity (W : Fin N → V) (M : V)
    (dev : Fin N → V) (hd : mergeDecomp W M dev) :
    ∑ i : Fin N, ∑ j : Fin N, ‖W i - W j‖ ^ 2
      = (2 * (N : ℝ)) * ∑ k : Fin N, ‖dev k‖ ^ 2 := by
  obtain ⟨hW, hsum⟩ := hd
  have hdij : ∀ i j, W i - W j = dev i - dev j := by
    intro i j
    rw [hW i, hW j]
    abel
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => by rw [hdij i j]))]
  -- ‖a−b‖² = ‖a‖² − 2⟨a,b⟩ + ‖b‖² (real inner)
  have hexp : ∀ a b : V, ‖a - b‖ ^ 2
      = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
    intro a b
    have h1 : ⟪a - b, a - b⟫_ℝ = ‖a - b‖ ^ 2 :=
      real_inner_self_eq_norm_sq (a - b)
    have h2 : ⟪a - b, a - b⟫_ℝ
        = ⟪a, a⟫_ℝ - ⟪a, b⟫_ℝ - ⟪b, a⟫_ℝ + ⟪b, b⟫_ℝ := by
      rw [inner_sub_right, inner_sub_left, inner_sub_left]
      ring
    have h3 : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm a b
    have h4 : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    have h5 : ⟪b, b⟫_ℝ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
    rw [← h1, h2, h3, h4, h5]
    ring
  simp only [hexp]
  -- Σ_{i,j} (‖d_i‖² + ‖d_j‖²) = 2N Σ‖d‖²
  have hAA : ∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2)
      = (2 * (N : ℝ)) * ∑ k : Fin N, ‖dev k‖ ^ 2 := by
    have h1 : ∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2)
        = ∑ i : Fin N, ∑ j : Fin N, ‖dev i‖ ^ 2
          + ∑ i : Fin N, ∑ j : Fin N, ‖dev j‖ ^ 2 := by
      calc ∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2)
          = ∑ i : Fin N, (∑ j : Fin N, ‖dev i‖ ^ 2
            + ∑ j : Fin N, ‖dev j‖ ^ 2) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
        _ = (∑ i : Fin N, ∑ j : Fin N, ‖dev i‖ ^ 2)
          + (∑ i : Fin N, ∑ j : Fin N, ‖dev j‖ ^ 2) :=
            Finset.sum_add_distrib
    have hj : ∀ i, ∑ j : Fin N, ‖dev i‖ ^ 2
        = (N : ℝ) * ‖dev i‖ ^ 2 := by
      intro i
      simp
    have h2 : ∑ i : Fin N, ∑ j : Fin N, ‖dev i‖ ^ 2
        = (N : ℝ) * ∑ k : Fin N, ‖dev k‖ ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => hj i), Finset.mul_sum]
    have h3 : ∑ i : Fin N, ∑ j : Fin N, ‖dev j‖ ^ 2
        = (N : ℝ) * ∑ k : Fin N, ‖dev k‖ ^ 2 := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun i _ => hj i), Finset.mul_sum]
    rw [h1, h2, h3]
    ring
  -- Σ_{i,j} 2⟨d_i, d_j⟩ = 2‖Σ d‖² = 0
  have hBB : ∑ i : Fin N, ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ)
      = 2 * ‖∑ k : Fin N, dev k‖ ^ 2 := by
    have h1 : ∑ i : Fin N, ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ
        = ⟪∑ i, dev i, ∑ j, dev j⟫_ℝ := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun i _ =>
        (inner_sum Finset.univ (fun j => dev j) (dev i)).symm
    have h2 : ∑ i : Fin N, ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ)
        = 2 * ∑ i : Fin N, ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ := by
      calc ∑ i : Fin N, ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ)
          = ∑ i : Fin N, (∑ j : Fin N, ⟪dev i, dev j⟫_ℝ
            + ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ) := by
            exact Finset.sum_congr rfl fun i _ => by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ => two_mul _
        _ = (∑ i : Fin N, ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ)
          + (∑ i : Fin N, ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ) :=
            Finset.sum_add_distrib
        _ = 2 * ∑ i : Fin N, ∑ j : Fin N, ⟪dev i, dev j⟫_ℝ :=
            (two_mul _).symm
    rw [h2, h1, real_inner_self_eq_norm_sq]
  -- сборка
  have hsplit : ∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 - 2 * ⟪dev i, dev j⟫_ℝ
      + ‖dev j‖ ^ 2)
      = ∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2)
        - ∑ i : Fin N, ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ) := by
    have hinner : ∀ i : Fin N,
        ∑ j : Fin N, (‖dev i‖ ^ 2 - 2 * ⟪dev i, dev j⟫_ℝ + ‖dev j‖ ^ 2)
        = (∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2))
          - (∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ)) := by
      intro i
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have houter1 : ∑ i : Fin N,
        ((∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2))
          - ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ))
      = (∑ i : Fin N, ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2))
        - (∑ i : Fin N, ∑ j : Fin N, (2 * ⟪dev i, dev j⟫_ℝ)) :=
      Finset.sum_sub_distrib
        (f := fun i => ∑ j : Fin N, (‖dev i‖ ^ 2 + ‖dev j‖ ^ 2))
        (g := fun i => ∑ j : Fin N, 2 * ⟪dev i, dev j⟫_ℝ)
    rw [Finset.sum_congr rfl (fun i _ => hinner i), houter1]
  rw [hsplit, hAA, hBB, hsum]
  norm_num

/-- **Ортогональная энергия локальна**: при взаимно
ортогональных dev_k merge-разложение сохраняет энергию
отклонений точно: ‖W_k − M‖² = ‖dev_k‖². -/
theorem orthogonal_energy_split (W : Fin N → V) (M : V)
    (dev : Fin N → V) (hd : mergeDecomp W M dev)
    (hortho : ∀ i j, i ≠ j → ⟪dev i, dev j⟫_ℝ = 0)
    (k : Fin N) :
    ‖W k - M‖ ^ 2 = ‖dev k‖ ^ 2 := by
  obtain ⟨hW, _⟩ := hd
  rw [hW k]
  rw [add_sub_cancel_left]

/-- **Полная реконструкция**: пара (M, dev_k) восстанавливает
W_k ТОЧНО (тривиально из разложения — фиксация для:
потери merge происходят при СЖАТИИ dev, не при усреднении). -/
theorem decompose_reconstruct (W : Fin N → V) (M : V)
    (dev : Fin N → V) (hd : mergeDecomp W M dev) (k : Fin N) :
    W k = M + dev k := (hd.1 k)

/-- **Антикоррелированный канал не исчезает**: проекция
merge на любое направление u равна средней проекции
экспертов; проекции отклонений на u в сумме гасятся, но
содержатся в dev_k — канал для distill-переноса:
merge гасит антикоррелированную компоненту ИМЕННО в M,
сохраняя её в dev-канале. -/
theorem anticorrelated_suppressed (W : Fin N → V) (M : V)
    (dev : Fin N → V) (hd : mergeDecomp W M dev) (u : V) :
    ⟪M, u⟫_ℝ = (∑ k, ⟪W k, u⟫_ℝ) / (N : ℝ)
      ∧ ∑ k, ⟪dev k, u⟫_ℝ = 0 := by
  obtain ⟨hW, hsum⟩ := hd
  refine ⟨?_, ?_⟩
  · have hmean : (N : ℝ) • M = ∑ k, W k :=
      merge_is_mean W M dev ⟨hW, hsum⟩
    have hproj : (N : ℝ) * ⟪M, u⟫_ℝ = ∑ k, ⟪W k, u⟫_ℝ := by
      have h1 : ⟪(N : ℝ) • M, u⟫_ℝ = (N : ℝ) * ⟪M, u⟫_ℝ :=
        real_inner_smul_left M u (N : ℝ)
      have h2 : ⟪(N : ℝ) • M, u⟫_ℝ = ∑ k, ⟪W k, u⟫_ℝ := by
        rw [hmean]
        rw [sum_inner]
      rw [← h1, h2]
    rw [eq_div_iff (ne_of_gt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))]
    linarith
  · have h0 : ∑ k, ⟪dev k, u⟫_ℝ = ⟪∑ k, dev k, u⟫_ℝ :=
      (sum_inner Finset.univ dev u).symm
    rw [h0, hsum]
    simp

end Hagi

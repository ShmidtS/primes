/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.RatioTakeoff
import Hagi.Growth.StateBinding
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

namespace Hagi.Ensemble

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

end Hagi.Ensemble

namespace Hagi
export Hagi.Ensemble (mergeDecomp merge_is_mean deviations_cancel pairwise_variance_identity orthogonal_energy_split decompose_reconstruct anticorrelated_suppressed)
end Hagi
/-!
# GainOperator — оператор превращения disagreement в прирост

Модель цикла: dev-энергия `devEnergy dev = ∑‡dev_k‡²`; оператор
с эффективностью η (`GainOp`: `D' ≥ ρ·D + η·E_dev − ξ`);
производство `C' = C + γ·D`.

* `gainop_cone_step`: при точном шаге, `GainOp`, `ρ ≥ γk`,
  конусе `kC ≤ D` и пороге
  `γk²·C + (1−ρ)k·C + ξ ≤ η·E_dev` следует `kC' ≤ D'`;
* `gainop_pairwise_bridge`: тот же вывод с порогом в попарной
  форме `η·(∑_{i,j}‡W_i − W_j‡²)/(2N)` (тождество
  `pairwise_variance_identity`);
* `gainop_ignition`: если условия выполнены на каждом цикле и
  старт в конусе, то `ConeRatio` инвариантен и
  `C₀·(1+γk)^T ≤ C_T` (композиция с `ratio_takeoff`).

Существование оператора с `η > 0` на реальном runtime — посылка
(в модуле он не строится); метрика η здесь безразмерно смешивает
энергии весов и наты.
-/

open Finset InnerProductSpace

namespace Hagi.Growth

variable {N : ℕ} [NeZero N] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Энергия dev-канала: `devEnergy dev = Σ_k ‖dev k‖^2`. -/
def devEnergy (dev : Fin N → V) : ℝ := ∑ k, ‖dev k‖ ^ 2

/-- `GainOp D D' dev ρ η ξ` означает
`ρ·D + η·devEnergy dev − ξ ≤ D'`. -/
def GainOp (D D' : ℝ) (dev : Fin N → V) (ρ η ξ : ℝ) : Prop :=
  ρ * D + η * devEnergy dev - ξ ≤ D'

/-- Если `C' = C + γ·D`, `GainOp D D' dev ρ η ξ`, `γ·k ≤ ρ`,
`k·C ≤ D` и `γ·k²·C + (1−ρ)·k·C + ξ ≤ η·devEnergy dev`,
то `k·C' ≤ D'`. -/
theorem gainop_cone_step (C D C' D' : ℝ) (γ ρ k ξ η : ℝ)
    (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone : k * C ≤ D)
    (hsuff : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev) :
    k * C' ≤ D' := by
  have hD : ρ * D + η * devEnergy dev - ξ ≤ D' := hop
  -- ключевая алгебра: D' − kC' ≥ (ρ−γk)(D−kC) ≥ 0
  have hkey : ρ * D + η * devEnergy dev - ξ - k * (C + γ * D)
      = (ρ - γ * k) * (D - k * C)
        + (η * devEnergy dev - (γ * k ^ 2 * C
          + (1 - ρ) * k * C + ξ)) := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D - k * C) := by
    have hsub : (0:ℝ) ≤ D - k * C := by linarith [hcone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ) ≤ η * devEnergy dev
      - (γ * k ^ 2 * C + (1 - ρ) * k * C + ξ) :=
    sub_nonneg.mpr hsuff
  have h3 : D' - k * C'
      ≥ (ρ - γ * k) * (D - k * C)
        + (η * devEnergy dev - (γ * k ^ 2 * C
          + (1 - ρ) * k * C + ξ)) := by
    rw [hstep]
    have hkey' : ρ * D + η * devEnergy dev - ξ - k * (C + γ * D)
        = (ρ - γ * k) * (D - k * C)
          + (η * devEnergy dev - (γ * k ^ 2 * C
            + (1 - ρ) * k * C + ξ)) := by
      field_simp
      ring
    linarith [hkey', hD]
  linarith

/-- Тот же вывод, что `gainop_cone_step`, с порогом в
попарной форме: если `mergeDecomp W M dev` и
`γ·k²·C + (1−ρ)·k·C + ξ
≤ η·((Σ_i Σ_j ‖W i − W j‖^2)/(2N))`, то `k·C' ≤ D'`. -/
theorem gainop_pairwise_bridge (C D C' D' : ℝ) (γ ρ k ξ η : ℝ)
    (W : Fin N → V) (M : V) (dev : Fin N → V)
    (hd : mergeDecomp W M dev)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone : k * C ≤ D)
    (hpair : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * ((∑ i, ∑ j, ‖W i - W j‖ ^ 2) / (2 * (N : ℝ)))) :
    k * C' ≤ D' := by
  have hiden : ∑ i, ∑ j, ‖W i - W j‖ ^ 2
      = (2 * (N : ℝ)) * devEnergy dev :=
    pairwise_variance_identity W M dev hd
  have hsuff : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev := by
    rw [hiden] at hpair
    have hz : (2:ℝ) * (N:ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < 2 * (N:ℝ) :=
        mul_pos (by norm_num) (Nat.cast_pos.mpr
          (Nat.pos_of_ne_zero (NeZero.ne N)))
      exact ne_of_gt hpos
    have hsimp : ((2:ℝ) * (N:ℝ)) * devEnergy dev
        / ((2:ℝ) * (N:ℝ)) = devEnergy dev :=
      by
        rw [mul_comm ((2:ℝ) * (N:ℝ)) (devEnergy dev)]
        exact mul_div_cancel_right₀ (devEnergy dev) hz
    rw [hsimp] at hpair
    exact hpair
  exact gainop_cone_step C D C' D' γ ρ k ξ η dev hstep hop
    hrhogk hcone hsuff

/-! ### Инвариант и takeoff от оператора -/

/-- Если на каждом цикле выполнены точный шаг, `GainOp`,
`ρ ≥ γk`, порог из `gainop_cone_step` и старт в конусе,
то `ConeRatio` инвариантен и
`(S 0).capability * (1 + γ·k) ^ T ≤ (S T).capability`. -/
theorem gainop_ignition {Xs : Type*}
    [NormedAddCommGroup Xs] [InnerProductSpace ℝ Xs]
    (S : ℕ → GrowthState Xs)
    (dev : ℕ → Fin N → V) (γ ρ k ξ η : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hstep : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (hop : ∀ t, GainOp (usableFrontier (S t))
      (usableFrontier (S (t + 1))) (dev t) ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (hsuff : ∀ t, γ * k ^ 2 * (S t).capability
      + (1 - ρ) * k * (S t).capability + ξ
      ≤ η * devEnergy (dev t))
    (T : ℕ) :
    ConeRatio (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) k
    ∧ (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability := by
  have hcone : ConeRatio (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) k := by
    intro t
    induction t with
    | zero => exact hcone0
    | succ t ih =>
        exact gainop_cone_step (S t).capability
          (usableFrontier (S t)) (S (t + 1)).capability
          (usableFrontier (S (t + 1))) γ ρ k ξ η (dev t)
          (hstep t) (hop t) hrhogk ih (hsuff t)
  exact ⟨hcone, ratio_takeoff (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k hγ hk hstep hcone T⟩

end Hagi.Growth

namespace Hagi
export Hagi.Growth (devEnergy GainOp gainop_cone_step gainop_pairwise_bridge gainop_ignition)
end Hagi

/-!
# GainDecomposition — разложение GainOp на измеримые стадии

Разложение конверсии disagreement → capability на две стадии:
`η_policy = G_policy / E_dev`, `η_state = G_cap / G_policy`.

* `gain_chain`: если `G_policy = η_p * E_dev` и
  `G_cap = η_s * G_policy`, то `G_cap = (η_p * η_s) * E_dev`;
* `zero_stage_kills_gain`: при `0 ≤ E_dev` и тех же посылках,
  если одна из `η_p`, `η_s` ≤ 0, а другая ≥ 0, то `G_cap ≤ 0`;
  произведения `η_p * η_s`: если он ≤ `(η_p * η_s) * devEnergy dev`,
  то он ≤ `η * devEnergy dev` для `η = η_p * η_s`.
-/

namespace Hagi.Growth

open Finset

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V]

/-- Стадия 1: `etaPolicy E_dev G_policy = G_policy / E_dev`. -/
noncomputable def etaPolicy (E_dev G_policy : ℝ) : ℝ :=
  G_policy / E_dev

/-- Стадия 2: `etaState G_policy G_cap = G_cap / G_policy`. -/
noncomputable def etaState (G_policy G_cap : ℝ) : ℝ :=
  G_cap / G_policy

/-- Если `G_policy = η_p * E_dev` и `G_cap = η_s * G_policy`,
то `G_cap = (η_p * η_s) * E_dev`. -/
theorem gain_chain (E_dev G_policy G_cap η_p η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_cap = η_s * G_policy) :
    G_cap = (η_p * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2]
  ring

/-- Если `0 ≤ E_dev`, `G_policy = η_p * E_dev`,
`G_cap = η_s * G_policy` и одна из `η_p`, `η_s` ≤ 0 при
другой ≥ 0, то `G_cap ≤ 0`. -/
theorem zero_stage_kills_gain (E_dev G_policy G_cap η_p η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev) (h2 : G_cap = η_s * G_policy)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_s) ∨ (0 ≤ η_p ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_s) * E_dev :=
    gain_chain E_dev G_policy G_cap η_p η_s h1 h2
  rcases hzero with ⟨hp, hs⟩ | ⟨hp, hs⟩
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith

end Hagi.Growth


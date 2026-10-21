/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

namespace Hagi.Optimization

open InnerProductSpace

/-!
# DirectionPacking — упаковка направлений (инфраструктура Уэлча)

Первая «геометрия» адаптивной HAGI: сколько почти
ортогональных направлений можно упаковать в d-мерное
пространство. Ядро доказательства границы Уэлча:

* `sum_sq_cauchy` — (∑ f)² ≤ n·∑ f² (Коши–Буняковский через
  inner-норму в EuclideanSpace);
* `Sop` — frame operator S = Σ⟪uᵢ,·⟫·uᵢ; `Sop_inner` /
  `Sop_inner_left` — его матричные элементы;
* `Sop_trace` — tr S = M для M единичных направлений
  (Парсеваль через OrthonormalBasis.sum_inner_mul_inner).

Недостающие шаги полной границы Уэлча
μ² ≥ (M−d)/(d(M−1)): tr S² = Σᵢₖ⟪uᵢ,uₖ⟫² (самосопряжённость)
и сведение М² ≤ d·tr S² к μ-оценке — следующая итерация.
-/

theorem sum_sq_cauchy {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i^2 := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 f : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)
  have h2 : ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ ι),
      (WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)⟫_ℝ = ∑ i, f i := by
    simp [PiLp.inner_apply]
  rw [h2] at h
  rw [abs_le] at h
  have h3 : ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖^2
      = (Fintype.card ι : ℝ) := by
    simp [EuclideanSpace.norm_eq]
  have h4 : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖^2 = ∑ i, f i^2 := by
    simp [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (f i)))]
  have h5 : (∑ i, f i)^2
      ≤ (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖)^2 := by
    have hP : (0:ℝ) ≤ ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hm : (0:ℝ) ≤ (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖) - ∑ i, f i := by linarith
    have hp : (0:ℝ) ≤ (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖) + ∑ i, f i := by linarith
    nlinarith [mul_nonneg hm hp]
  have h6 : (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
      ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖)^2
      = (∑ i, f i^2) * (Fintype.card ι : ℝ) := by
    have hP : (0:ℝ) ≤ ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have ha : (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖) *
        (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖)
        = ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖^2 *
          ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖^2 := by ring_nf
    rw [pow_two, ha, h3, h4]
  calc (∑ i, f i)^2 ≤ (‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : EuclideanSpace ℝ ι)‖)^2 := h5
    _ = (∑ i, f i^2) * (Fintype.card ι : ℝ) := h6
    _ = (Fintype.card ι : ℝ) * ∑ i, f i^2 := by rw [mul_comm (∑ i, f i^2) ((Fintype.card ι : ℝ))]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {d : ℕ} [FiniteDimensional ℝ F] (b : OrthonormalBasis (Fin d) ℝ F)

/-- Frame operator семейства направлений u:
`S x = ∑ ⟪uᵢ, x⟫ • uᵢ` — суммарная проекция. -/
noncomputable def Sop {M : ℕ} (u : Fin M → F) (x : F) : F :=
  ∑ i, ⟪u i, x⟫_ℝ • u i

/-- Матричный элемент frame operator (правая форма). -/
theorem Sop_inner {M : ℕ} (u : Fin M → F) (x y : F) :
    ⟪Sop u x, y⟫_ℝ = ∑ i, ⟪u i, x⟫_ℝ * ⟪u i, y⟫_ℝ := by
  rw [Sop, sum_inner]
  exact Finset.sum_congr rfl (fun i _ => real_inner_smul_left (u i) y ⟪u i, x⟫_ℝ)

/-- Матричный элемент frame operator (левая форма). -/
theorem Sop_inner_left {M : ℕ} (u : Fin M → F) (x y : F) :
    ⟪y, Sop u x⟫_ℝ = ∑ i, ⟪u i, x⟫_ℝ * ⟪y, u i⟫_ℝ := by
  rw [real_inner_comm, Sop_inner]
  exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_comm (u i) y])

/-- Самосопряжённость frame operator: `⟪S x, y⟫ = ⟪x, S y⟫`. -/
theorem Sop_self_adjoint {M : ℕ} (u : Fin M → F) (x y : F) :
    ⟪Sop u x, y⟫_ℝ = ⟪x, Sop u y⟫_ℝ := by
  rw [Sop_inner u x y, Sop_inner_left u y x]
  exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_comm (u i) x]; ring)

/-- **След frame operator**: для M единичных направлений
tr S = M (Парсеваль). -/
theorem Sop_trace {M : ℕ} (u : Fin M → F) (hu : ∀ i, ‖u i‖ = 1) :
    ∑ j, ⟪Sop u (b j), b j⟫_ℝ = (M:ℝ) := by
  have key : ∀ i, ∑ j, ⟪u i, b j⟫_ℝ * ⟪b j, u i⟫_ℝ = ‖u i‖^2 := by
    intro i
    have h1 := OrthonormalBasis.sum_inner_mul_inner b (u i) (u i)
    rw [real_inner_self_eq_norm_sq] at h1
    exact h1
  calc ∑ j, ⟪Sop u (b j), b j⟫_ℝ
      = ∑ j, ∑ i, ⟪u i, b j⟫_ℝ * ⟪u i, b j⟫_ℝ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Sop_inner]
    _ = ∑ i, ∑ j, ⟪u i, b j⟫_ℝ * ⟪u i, b j⟫_ℝ := Finset.sum_comm
    _ = ∑ i, ∑ j, ⟪u i, b j⟫_ℝ * ⟪b j, u i⟫_ℝ :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [real_inner_comm (u i) (b j)]))
    _ = ∑ i, ‖u i‖^2 := Finset.sum_congr rfl (fun i _ => key i)
    _ = (M:ℝ) := by simp [hu]


/-- **Квадрат следа frame operator**: tr S² = Σᵢₖ⟪uᵢ,uₖ⟫²
(через самосопряжённость ⟪S²e,e⟫ = ‖Se‖² и Парсеваль). -/
theorem Sop_trace_sq {M : ℕ} (u : Fin M → F) :
    ∑ j, ⟪Sop u (Sop u (b j)), b j⟫_ℝ = ∑ i, ∑ k, (⟪u i, u k⟫_ℝ)^2 := by
  have hSA : ∀ x y : F, ⟪Sop u x, y⟫_ℝ = ⟪x, Sop u y⟫_ℝ := by
    intro x y
    rw [Sop_inner u x y, Sop_inner_left u y x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm (u i) x]
    ring
  have hstep1 : ∀ j, ⟪Sop u (Sop u (b j)), b j⟫_ℝ = ‖Sop u (b j)‖^2 := by
    intro j
    rw [hSA (Sop u (b j)) (b j), real_inner_self_eq_norm_sq]
  have hstep2 : ∀ j, ‖Sop u (b j)‖^2
      = ∑ i, ∑ k, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ * ⟪u i, u k⟫_ℝ := by
    intro j
    rw [← real_inner_self_eq_norm_sq, Sop_inner u (b j) (Sop u (b j))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Sop_inner_left u (b j) (u i), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring))
  have hpar : ∀ i k, (∑ j, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ) = ⟪u k, u i⟫_ℝ := by
    intro i k
    have h := OrthonormalBasis.sum_inner_mul_inner b (u i) (u k)
    calc (∑ j, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ)
        = ∑ j, ⟪u i, b j⟫_ℝ * ⟪b j, u k⟫_ℝ :=
          Finset.sum_congr rfl (fun j _ => by rw [real_inner_comm (u k) (b j)])
      _ = ⟪u i, u k⟫_ℝ := h
      _ = ⟪u k, u i⟫_ℝ := by rw [real_inner_comm (u i) (u k)]
  calc ∑ j, ⟪Sop u (Sop u (b j)), b j⟫_ℝ
      = ∑ j, ∑ i, ∑ k, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ * ⟪u i, u k⟫_ℝ :=
        Finset.sum_congr rfl (fun j _ => by rw [hstep1 j, hstep2 j])
    _ = ∑ i, ∑ k, ∑ j, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ * ⟪u i, u k⟫_ℝ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ k, (∑ j, ⟪u i, b j⟫_ℝ * ⟪u k, b j⟫_ℝ) * ⟪u i, u k⟫_ℝ := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ k, (⟪u i, u k⟫_ℝ)^2 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)
        ); rw [hpar i k, real_inner_comm (u k) (u i), sq]

/-- **Граница Уэлча**: для M единичных направлений в
d-мерном пространстве с когерентностью

  `μ ≥ |⟪uᵢ, uₖ⟫| (i ≠ k)`

справедливо

  `(M − d)/(M − 1) ≤ d·μ²`.

Доказательство: Коши на диагонали frame operator
((tr S)² ≤ d·tr S², `sum_sq_cauchy` + ⟨Se,e⟩² ≤ ‖Se‖²),
tr S = M (`Sop_trace`), tr S² = Σᵢₖ⟪uᵢ,uₖ⟫² (`Sop_trace_sq`),
разложение Σᵢₖ = M + M(M−1)μ². Геометрическое ограничение на
число почти ортогональных направлений: необходимое условие
d ≥ M/(1 + (M−1)μ²) — размерность по числу различимых
направлений и допустимому смешению (замена эвристики «пик
Ω₇» на измеримую упаковочную границу). -/
theorem welch_bound_core {M : ℕ} (_b : OrthonormalBasis (Fin d) ℝ F)
    (u : Fin M → F) (hu : ∀ i, ‖u i‖ = 1)
    (μ : ℝ) (hμ : ∀ i k, i ≠ k → |⟪u i, u k⟫_ℝ| ≤ μ) (hM : 2 ≤ M)
    (hd : 0 < d) :
    ((M:ℝ) - d) / ((M:ℝ) - 1) ≤ d * μ^2 := by
  have hM1 : (0:ℝ) < (M:ℝ) - 1 := by
    have h2 : (1:ℝ) < (M:ℝ) := by exact_mod_cast show (1:ℕ) < M by omega
    linarith
  -- Коши на диагонали frame operator
  have hf : ∀ j, ⟪Sop u (_b j), _b j⟫_ℝ^2 ≤ ‖Sop u (_b j)‖^2 := by
    intro j
    have hcs := abs_real_inner_le_norm (Sop u (_b j)) (_b j)
    rw [OrthonormalBasis.norm_eq_one _b j, mul_one, abs_le] at hcs
    have hnn : (0:ℝ) ≤ ‖Sop u (_b j)‖ := norm_nonneg _
    nlinarith [hcs.1, hcs.2, hnn]
  have hcauchy := sum_sq_cauchy (fun j : Fin d => ⟪Sop u (_b j), _b j⟫_ℝ)
  simp only [Fintype.card_fin] at hcauchy
  rw [Sop_trace _b u hu] at hcauchy
  -- hcauchy : M² ≤ d · Σ f²; и Σ f² ≤ tr S² = Σᵢₖ⟪⟫²
  have h2 : ∑ j, ⟪Sop u (_b j), _b j⟫_ℝ^2
      ≤ ∑ j, ⟪Sop u (Sop u (_b j)), _b j⟫_ℝ := by
    refine le_trans (Finset.sum_le_sum (fun j _ => hf j)) ?_
    exact Finset.sum_le_sum (fun j _ => by
      rw [Sop_self_adjoint u (Sop u (_b j)) (_b j), real_inner_self_eq_norm_sq])
  rw [Sop_trace_sq _b u] at h2
  -- h2 : Σ f² ≤ Σᵢₖ⟪uᵢ,uₖ⟫²; разложение по диагонали
  have hdiag : ∀ i k, (⟪u i, u k⟫_ℝ)^2
      ≤ (if i = k then (1:ℝ) else μ^2) := by
    intro i k
    by_cases hik : i = k
    · rw [if_pos hik]
      rw [hik, real_inner_self_eq_norm_sq, hu k]
      simp
    · rw [if_neg hik]
      have h2' := hμ i k hik
      have hnn : (0:ℝ) ≤ μ^2 := sq_nonneg μ
      have habs : (0:ℝ) ≤ |⟪u i, u k⟫_ℝ| := abs_nonneg _
      have h9 : (⟪u i, u k⟫_ℝ)^2 = |⟪u i, u k⟫_ℝ| * |⟪u i, u k⟫_ℝ| := by
        rw [pow_two, ← abs_mul_abs_self]
      rw [h9, show (μ:ℝ)^2 = μ * μ from pow_two μ]
      exact mul_self_le_mul_self habs h2'
  have h3 : ∑ i : Fin M, ∑ k : Fin M, (⟪u i, u k⟫_ℝ)^2
      ≤ ∑ i : Fin M, ∑ k : Fin M, (if i = k then (1:ℝ) else μ^2) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hdiag i k))
  -- Σ (if i=k then 1 else μ²) = M + M(M−1)μ²
  have h4 : ∑ i : Fin M, ∑ k : Fin M, (if i = k then (1:ℝ) else μ^2)
      = (M:ℝ) + M * ((M:ℝ) - 1) * μ^2 := by
    have hinner : ∀ i : Fin M, ∑ k : Fin M, (if i = k then (1:ℝ) else μ^2)
        = 1 + ((M:ℝ) - 1) * μ^2 := by
      intro i
      have key : ∀ k : Fin M, (if i = k then (1:ℝ) else μ^2)
          = μ^2 + (if i = k then (1:ℝ) - μ^2 else 0) := by
        intro k
        by_cases h : i = k
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      calc ∑ k : Fin M, (if i = k then (1:ℝ) else μ^2)
          = ∑ k : Fin M, (μ^2 + (if i = k then (1:ℝ) - μ^2 else 0)) :=
            Finset.sum_congr rfl (fun k _ => key k)
        _ = M * μ^2 + ∑ k : Fin M, (if i = k then (1:ℝ) - μ^2 else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
        _ = M * μ^2 + ((1:ℝ) - μ^2) := by
            rw [Finset.sum_ite_eq Finset.univ i (fun _ => (1:ℝ) - μ^2),
              if_pos (Finset.mem_univ i)]
        _ = 1 + ((M:ℝ) - 1) * μ^2 := by ring
    rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  -- финал: M² ≤ d·(M + M(M−1)μ²) ⟹ (M−d)/(M−1) ≤ d·μ²
  have hfin : ((M:ℝ))^2 ≤ (d:ℝ) * ((M:ℝ) + M * ((M:ℝ) - 1) * μ^2) := by
    have hA : ((M:ℝ))^2 ≤ (d:ℝ) * ∑ j, ⟪Sop u (_b j), _b j⟫_ℝ^2 := hcauchy
    have hB : (d:ℝ) * ∑ j, ⟪Sop u (_b j), _b j⟫_ℝ^2
        ≤ (d:ℝ) * ∑ i, ∑ k, (⟪u i, u k⟫_ℝ)^2 := by
      exact mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (d:ℝ))
    have hC : (d:ℝ) * ∑ i, ∑ k, (⟪u i, u k⟫_ℝ)^2
        ≤ (d:ℝ) * ((M:ℝ) + M * ((M:ℝ) - 1) * μ^2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ (d:ℝ))
      exact le_trans h3 (le_of_eq h4)
    exact le_trans hA (le_trans hB hC)
  rw [div_le_iff₀ (by linarith : (0:ℝ) < (M:ℝ) - 1)]
  nlinarith [hfin, hd, hM1]

/-- **Минимальная размерность по Уэлчу**: чтобы упаковать M
различимых направлений с когерентностью μ (допустимым
смешением), необходимо

  `M / (1 + (M−1)·μ²) ≤ d`.

Прямое следствие `welch_bound_core`: размерность
представления выбирается числом реально нужных различимых
направлений и допустимым уровнем их смешения — измеримая
замена эвристики «пик телесного угла при n = 7». -/
theorem welch_min_dimension {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {d : ℕ} [FiniteDimensional ℝ F]
    (_b : OrthonormalBasis (Fin d) ℝ F) {M : ℕ} (u : Fin M → F)
    (hu : ∀ i, ‖u i‖ = 1) (μ : ℝ) (hμ : ∀ i k, i ≠ k → |⟪u i, u k⟫_ℝ| ≤ μ)
    (hM : 2 ≤ M) (hd : 0 < d) (hμ0 : 0 ≤ μ) :
    (M:ℝ) / (1 + ((M:ℝ) - 1) * μ^2) ≤ (d:ℝ) := by
  have hw := welch_bound_core _b u hu μ hμ hM hd
  have hpos : (0:ℝ) < 1 + ((M:ℝ) - 1) * μ^2 := by
    have hM1 : (0:ℝ) < (M:ℝ) - 1 := by
      have : (1:ℝ) < (M:ℝ) := by exact_mod_cast show (1:ℕ) < M by omega
      linarith
    nlinarith [hM1]
  have hM1 : (0:ℝ) < (M:ℝ) - 1 := by
    have : (1:ℝ) < (M:ℝ) := by exact_mod_cast show (1:ℕ) < M by omega
    linarith
  rw [div_le_iff₀ hM1] at hw
  rw [div_le_iff₀ hpos]
  nlinarith [hw]

/-- **Вместимость упаковки заполнена**: M+1 направлений с
когерентностью μ существуют только если
(M+1)/(1+M·μ²) ≤ d. Контрапозиция — триггер контроллера
роста (модуль SubspaceGrowth): если d < (M+1)/(1+M·μ²), новое
направление НЕВОЗМОЖНО добавить без роста размерности или
роста смешения μ — упаковка исчерпана, и projResidual-
остаток нового важного направления обязан быть ненулевым. -/
theorem welch_capacity_full {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {d : ℕ} [FiniteDimensional ℝ F]
    (_b : OrthonormalBasis (Fin d) ℝ F) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hd : 0 < d) (M : ℕ) (hM1 : 1 ≤ M)
    (u : Fin (M+1) → F) (hu : ∀ i, ‖u i‖ = 1)
    (hμ : ∀ i k, i ≠ k → |⟪u i, u k⟫_ℝ| ≤ μ) :
    ((M:ℝ)+1) / (1 + (M:ℝ) * μ^2) ≤ (d:ℝ) := by
  have hM : 2 ≤ M + 1 := by omega
  have hw := welch_min_dimension _b u hu μ hμ hM hd hμ0
  have hconv : (((M:ℕ)+1:ℕ):ℝ) - 1 = (M:ℝ) := by push_cast; ring
  simp only [Nat.cast_succ] at hw
  have : ((M:ℝ) + 1 - 1) = (M:ℝ) := by ring
  rw [this] at hw
  exact hw
end Hagi.Optimization

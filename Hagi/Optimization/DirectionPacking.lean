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

private theorem sum_sq_cauchy {ι : Type*} [Fintype ι] (f : ι → ℝ) :
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

end Hagi.Optimization

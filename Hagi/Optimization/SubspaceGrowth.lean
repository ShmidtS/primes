/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

namespace Hagi.Optimization

open InnerProductSpace

/-!
# SubspaceGrowth — контроллер подпространства и конечность роста

Вторая «геометрия» адаптивной HAGI: рост архитектуры по
остатку проекции. Новое измерение добавляется только когда
важное направление v плохо представимо текущим
ортонормированным базисом u:

* `projResidual u v = v − ∑⟪uᵢ,v⟫·uᵢ` — невязка представления;
* `projResidual_ortho` — остаток ортогонален всем текущим
  направлениям (легитимное новое направление);
* `projResidual_self_inner` — ⟪r,v⟫ = ‖r‖² (невязка несёт
  свою норму);
* `projResidual_le_norm` — δ(v) ≤ ‖v‖: невязка измеряется в
  долях нормы запроса;
* `growth_finite` — внешняя индукция: если метрика покрытия
  C убывает на каждом принятом расширении минимум на δ > 0 и
  неотрицательна, то число расширений конечно
  (k·δ ≤ C₀). Рост архитектуры останавливается за
  C₀/δ шагов — положительное минимальное улучшение, а не
  «когда-нибудь положительное».
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Невязка проекции: часть направления v, не представимая
ортонормированным семейством u. -/
noncomputable def projResidual {k : ℕ} (u : Fin k → F) (v : F) : F :=
  v - ∑ i, ⟪u i, v⟫_ℝ • u i

theorem projResidual_ortho {k : ℕ} (u : Fin k → F) (hu1 : ∀ i, ‖u i‖ = 1)
    (hu2 : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0) (v : F) (j : Fin k) :
    ⟪projResidual u v, u j⟫_ℝ = 0 := by
  rw [projResidual, inner_sub_left, sum_inner]
  rw [Finset.sum_eq_single j]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]
    rw [real_inner_comm v (u j)]
    ring
  · intro i _ hij
    rw [real_inner_smul_left]
    rw [hu2 i j hij]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem projResidual_self_inner {k : ℕ} (u : Fin k → F) (hu1 : ∀ i, ‖u i‖ = 1)
    (hu2 : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0) (v : F) :
    ⟪projResidual u v, v⟫_ℝ = ‖projResidual u v‖^2 := by
  set r := projResidual u v with hrdef
  have hsplit : v - r = ∑ i, ⟪u i, v⟫_ℝ • u i := by
    rw [hrdef, projResidual, sub_sub_cancel]
  have hr : ⟪r, v - r⟫_ℝ = 0 := by
    rw [hsplit, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_smul_right]
    rw [projResidual_ortho u hu1 hu2 v i]
    simp
  have hadd : v = (v - r) + r := by abel
  rw [hadd, inner_add_right, hr]
  rw [real_inner_self_eq_norm_sq]
  ring

theorem projResidual_le_norm {k : ℕ} (u : Fin k → F) (hu1 : ∀ i, ‖u i‖ = 1)
    (hu2 : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0) (v : F) :
    ‖projResidual u v‖ ≤ ‖v‖ := by
  have h := projResidual_self_inner u hu1 hu2 v
  have h2 := abs_of_nonneg (norm_nonneg (projResidual u v))
  rw [show (‖projResidual u v‖^2 : ℝ) = ‖projResidual u v‖ * ‖projResidual u v‖ from by ring] at h
  by_cases hz : ‖projResidual u v‖ = 0
  · rw [hz]; exact norm_nonneg v
  · have hpos : (0:ℝ) < ‖projResidual u v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hcs := abs_real_inner_le_norm (projResidual u v) v
    rw [h] at hcs
    rw [abs_of_nonneg (mul_nonneg hpos.le hpos.le)] at hcs
    nlinarith [hcs, hpos]

/-- **Конечность роста архитектуры**: если метрика покрытия C
неотрицательна и каждое принятое расширение уменьшает её
минимум на δ > 0, то k·δ ≤ C₀ — число расширений конечно
(≤ C₀/δ). Внешняя индукция «трёх геометрий»: рост по новым
независимым направлениям останавливается при конечном
полезном покрытии и гарантированном минимальном улучшении. -/
theorem growth_finite (C : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ k : ℕ, C (k+1) ≤ C k - δ) (hC : ∀ j : ℕ, 0 ≤ C j) (k : ℕ) :
    (k:ℝ) * δ ≤ C 0 := by
  have hkey : ∀ k : ℕ, C k ≤ C 0 - (k:ℝ) * δ := by
    intro k
    induction k with
    | zero => norm_num
    | succ n ih =>
        have h1 := hstep n
        push_cast
        nlinarith [h1, ih, hδ]
  have h2 := hkey k
  have h3 := hC k
  linarith

end Hagi.Optimization

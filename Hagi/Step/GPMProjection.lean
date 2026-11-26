/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# GPM — проекция градиента на дополнение памяти сохраняет прошлые выходы

`_proj_out(x, Ul, Ur)` (optimal_lm.py): `x − Ul (Ulᵀ x)` и `x − (x Ur) Urᵀ` —
Gradient Projection Memory: обновление не меняет компоненту в подпространстве
прошлых задач. `gpm_left/right` — ортонормированные базисы (SVD выходов).

* `projOut` — `g − ∑ᵢ ⟨uᵢ, g⟩ uᵢ` для ортонормированной памяти `U`;
* `projOut_orth` — спроецированный градиент ортогонален каждой строке `U`;
* `gpm_outputs_preserved` — шаг `w − projOut U g` сохраняет `⟨w, uⱼ⟩` точно:
  нулевое забывание выходов на памяти (правая проекция — тот же факт по `dot_comm`).

Граница: память — точный ортонормированный базис; SVD-усечение в коде
приближённое, ошибка не моделируется (см. `ContinualForgetting`).
-/

namespace Hagi.Step.GPM
open Finset
variable {n k : ℕ}

/-- Скалярное произведение строк. -/
def dot (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i
/-- Память GPM: ортонормированные строки-прототипы. -/
def Orthonormal (U : Fin k → (Fin n → ℝ)) : Prop :=
  (∀ i, dot (U i) (U i) = 1) ∧ ∀ i j, i ≠ j → dot (U i) (U j) = 0
/-- Проекция градиента на дополнение памяти (как `_proj_out`). -/
noncomputable def projOut (U : Fin k → (Fin n → ℝ)) (g : Fin n → ℝ) : Fin n → ℝ :=
  fun a => g a - ∑ i, dot (U i) g * U i a
theorem dot_sub_left (x y z : Fin n → ℝ) : dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]
theorem dot_comm (x y : Fin n → ℝ) : dot x y = dot y x := by
  simp [dot, mul_comm]
theorem dot_sum_right (x : Fin n → ℝ) (f : Fin k → ℝ) (u : Fin k → Fin n → ℝ) :
    dot x (∑ i, f i • u i) = ∑ i, f i * dot x (u i) := by
  unfold dot
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => (by ring : x a * (f i * u i a) = f i * (x a * u i a))
/-- Спроецированный градиент ортогонален каждой строке памяти. -/
theorem projOut_orth (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (j : Fin k)
    (g : Fin n → ℝ) : dot (projOut U g) (U j) = 0 := by
  have hP : projOut U g = g - ∑ i, dot (U i) g • U i := by
    funext a; simp [projOut, Finset.sum_apply]
  rw [hP, dot_sub_left, dot_comm g (U j), dot_comm (∑ i, dot (U i) g • U i) (U j), dot_sum_right]
  have hterm : ∀ i : Fin k, dot (U i) g * dot (U j) (U i) = if i = j then dot (U j) g else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp [hU.1]
    · rw [if_neg h, hU.2 j i (Ne.symm h), mul_zero]
  rw [show (∑ i, dot (U i) g * dot (U j) (U i)) = ∑ i, (if i = j then dot (U j) g else 0) from
    Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq' (Finset.univ) j (fun _ => dot (U j) g)]
  simp
/-- Шаг GPM `w' = w − projOut U g` сохраняет выходы строки на памяти. -/
theorem gpm_outputs_preserved (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (j : Fin k)
    (w g : Fin n → ℝ) : dot (w - projOut U g) (U j) = dot w (U j) := by
  rw [dot_sub_left, projOut_orth U hU j g, sub_zero]

end Hagi.Step.GPM

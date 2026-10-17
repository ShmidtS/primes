/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic


set_option linter.style.header false

/-!
# FrobOuter — Frobenius-изометрия внешних произведений (ядро
Eckart–Young, R295)

`frobSq_outer_orthonormal`: Frobenius-квадрат суммы
σ_i·(u_i ⊗ v_i) при ортонормальных семействах u, v равен
точно Σ σ_i² — квадрат суммы раскрывается, кросс-члены
исчезают через (Σ_a u_c u_d)·(Σ_b v_c v_d) = δ_cd·δ_cd.

Это верхняя (достижимость) часть Eckart–Young–Мирского: для
SVD-формы A = Σ σ_i u_i⊗v_i ранговое-k-усечение A_k имеет
‖A − A_k‖_F² = Σ_{i>k} σ_i². Mathlib v4.34.1 не имеет
SVD/singularValues — порт полного Eckart–Young (нижняя
оптимальность, Weyl) многоходовый; здесь доказан точный
фундамент без спектральных посылок: нужны только
ортонормальность семейств.
* `frobSq_outerSum` (обобщение): то же для суммы по любому
  подмножеству индексов s;
* `frobSq_trunc_tail` (точный хвост усечения): ошибка удаления
  s-компоненты из полной суммы — Frobenius-квадрат дополнения,
  ‖A − Σ_{i∈s}σ_i u_i⊗v_i‖²_F = Σ_{i∉s} σ_i² — достижимость
  Eckart–Young для SVD-формы (нижняя оптимальность — FLYWHEEL-
  порт, см. план).
-/

open Finset

namespace Hagi.Core

variable {m r n : Type} [Fintype m] [Fintype r] [Fintype n]
  [DecidableEq m] [DecidableEq r] [DecidableEq n]

/-- Frobenius-квадрат -/
def frobSq (A : Matrix m r ℝ) : ℝ := ∑ a, ∑ b, (A a b) ^ 2

/-- Внешнее произведение u ⊗ v -/
def outer (u : m → ℝ) (v : r → ℝ) : Matrix m r ℝ :=
  Matrix.of fun a b => u a * v b

theorem frobSq_outer_orthonormal
    (u : Fin k → m → ℝ) (v : Fin k → r → ℝ) (σ : Fin k → ℝ)
    (hu : ∀ i j, ∑ a, u i a * u j a = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ b, v i b * v j b = if i = j then 1 else 0) :
    frobSq (∑ i, σ i • outer (u i) (v i))
      = ∑ i, (σ i) ^ 2 := by
  unfold frobSq outer
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul]
  -- квадрат суммы: (Σ c, f c)^2 = Σ c, Σ d, f c * f d
  have hkey : ∀ a b, (∑ c, σ c * (u c a * v c b)) ^ 2
      = ∑ c, ∑ d, (σ c * (u c a * v c b)) * (σ d * (u d a * v d b)) := by
    intro a b
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
    (fun b _ => hkey a b))]
  -- шаг 1: per-b внутренняя тройка (x,c,d) → (c,d,x)
  have h1 : ∀ a : m, ∑ b, ∑ c, ∑ d,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = ∑ c, ∑ d, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b)) := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  -- шаг 2: (a,c,d,b) → (c,d,a,b)
  rw [Finset.sum_comm]  -- (c,a,d,b)
  have h2 : ∀ c : Fin k, ∑ a, ∑ d, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = ∑ d, ∑ a, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b)) := by
    intro c
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun c _ => h2 c)]
  -- факторизация per-(c,d)
  have hfac : ∀ c d : Fin k, ∑ a, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = σ c * σ d * (∑ a, u c a * u d a) * (∑ b, v c b * v d b) := by
    intro c d
    have hb : ∀ a : m, ∑ b, σ c * (u c a * v c b) * (σ d * (u d a * v d b))
        = σ c * σ d * (u c a * u d a) * ∑ b, v c b * v d b := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul,
      ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => hfac c d))]
  -- hu/hv: ортонормальность → if c = d
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => by rw [hu c d, hv c d]))]
  -- Kronecker: (if c = d then 1 else 0)² → ite-форма
  have hkr : ∀ c d : Fin k, σ c * σ d
      * (if c = d then 1 else 0) * (if c = d then 1 else 0)
      = if c = d then σ c * σ c else 0 := by
    intro c d
    by_cases h : c = d
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => hkr c d))]
  -- Σ_d (if c = d then σc² else 0) = σc²
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_ite_eq Finset.univ c
    (fun d => σ c * σ c))]
  simp [sq]

/-- Хвостовая сумма внешних произведений: индексы из s. -/
def outerSum (s : Finset n) (σ : n → ℝ)
    (u : n → m → ℝ) (v : n → r → ℝ) : Matrix m r ℝ :=
  ∑ i ∈ s, σ i • outer (u i) (v i)

theorem frobSq_outerSum (s : Finset n) (σ : n → ℝ)
    (u : n → m → ℝ) (v : n → r → ℝ)
    (hu : ∀ i j, ∑ a, u i a * u j a = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ b, v i b * v j b = if i = j then 1 else 0) :
    frobSq (outerSum s σ u v) = ∑ i ∈ s, (σ i) ^ 2 := by

  unfold outerSum frobSq outer
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul]
  -- квадрат суммы: (Σ c, f c)^2 = Σ c, Σ d, f c * f d
  have hkey : ∀ a b, (∑ c ∈ s, σ c * (u c a * v c b)) ^ 2
      = ∑ c ∈ s, ∑ d ∈ s, (σ c * (u c a * v c b)) * (σ d * (u d a * v d b)) := by
    intro a b
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
    (fun b _ => hkey a b))]
  -- шаг 1: per-b внутренняя тройка (x,c,d) → (c,d,x)
  have h1 : ∀ a : m, ∑ b, ∑ c ∈ s, ∑ d ∈ s,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = ∑ c ∈ s, ∑ d ∈ s, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b)) := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  -- шаг 2: (a,c,d,b) → (c,d,a,b)
  rw [Finset.sum_comm]  -- (c,a,d,b)
  have h2 : ∀ c : n, ∑ a, ∑ d ∈ s, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = ∑ d ∈ s, ∑ a, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b)) := by
    intro c
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun c _ => h2 c)]
  -- факторизация per-(c,d)
  have hfac : ∀ c d : n, ∑ a, ∑ b,
      σ c * (u c a * v c b) * (σ d * (u d a * v d b))
      = σ c * σ d * (∑ a, u c a * u d a) * (∑ b, v c b * v d b) := by
    intro c d
    have hb : ∀ a : m, ∑ b, σ c * (u c a * v c b) * (σ d * (u d a * v d b))
        = σ c * σ d * (u c a * u d a) * ∑ b, v c b * v d b := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul,
      ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => hfac c d))]
  -- hu/hv: ортонормальность → if c = d
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => by rw [hu c d, hv c d]))]
  -- Kronecker: (if c = d then 1 else 0)² → ite-форма
  have hkr : ∀ c d : n, σ c * σ d
      * (if c = d then 1 else 0) * (if c = d then 1 else 0)
      = if c = d then σ c * σ c else 0 := by
    intro c d
    by_cases h : c = d
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun d _ => hkr c d))]
  -- Σ_d (if c = d then σc² else 0) = σc²
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_ite_eq s c
    (fun d => σ c * σ c))]
  simp [sq]


/-- **Точный хвост ошибки усечения** (достижимость
Eckart–Young): для A = Σ_i σ_i·(u_i⊗v_i) и любого подмножества
индексов s ошибка удаления s-компоненты — это Frobenius-квадрат
дополнения: ‖A − Σ_{i∈s} σ_i u_i⊗v_i‖²_F = Σ_{i∉s} σ_i².
Ранговая k-усечённая версия — инстанциация при
s = {i < k} на упорядоченном типе. -/
theorem frobSq_trunc_tail (s : Finset n) (σ : n → ℝ)
    (u : n → m → ℝ) (v : n → r → ℝ)
    (hu : ∀ i j, ∑ a, u i a * u j a = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ b, v i b * v j b = if i = j then 1 else 0) :
    frobSq ((∑ i, σ i • outer (u i) (v i))
      - outerSum s σ u v)
      = ∑ i ∈ sᶜ, (σ i) ^ 2 := by
  have hsplit : (∑ i, σ i • outer (u i) (v i))
      = outerSum s σ u v + outerSum (sᶜ) σ u v := by
    unfold outerSum
    rw [← Finset.sum_sdiff (Finset.subset_univ s)]
    exact add_comm _ _
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact frobSq_outerSum sᶜ σ u v hu hv

end Hagi.Core

namespace Hagi
export Hagi.Core (frobSq outer outerSum frobSq_outer_orthonormal frobSq_outerSum frobSq_trunc_tail)
end Hagi

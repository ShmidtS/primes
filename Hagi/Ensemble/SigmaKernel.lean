/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R129-ревизия + R131: Σ-ядро интерференции и GN-мост

Эпистемологическая ревизия 2026-10-05 (внешний документ):

## R129 (уровень 1, Machine-Checked): PSD-ядро
Квадратичный член функциональной интерференции слияния —
квадратичная форма v ⬝ᵥ (Σ.mulVec v) ковариации активаций.
При факторизации Σ = Aᵀ·A (PSD-представление, посылка —
само существование фактора; спектральная теорема вне
объёма):

* `quad_form_factorization` — v ⬝ᵥ (Σ.mulVec v) =
  ‖A.mulVec v‖² (точная идентичность);
* `quad_form_zero_iff` — интерференция = 0 ⟺ A.mulVec v = 0
  (строка лежит в ядре фактора);
* `kernel_interference_zero` — Δ·Σ = 0 (ядро) ⟹
  квадратичная интерференция нулевая.

## R131 (уровень 1 + уровень 2-режим): GN-мост
В режиме Гаусса-Ньютона (лосс-градиент g = (1/m)·Xᵀ·r —
ПОСЫЛКА-режим, уровень 2) любое направление из ker(X)
(GPM-проекция) допустимо для SafeQP при любом остатке r:

* `gn_grad_inner_ker` — d ∈ ker(X) ⟹ ⟨g, d⟩ = 0;
* `gpm_implies_safeqp_gn` — ⟨g, d⟩ = 0 ≥ −ε ∀ε ≥ 0
  (GPM — ДОСТАТОЧНОЕ условие допустимости; обратное при
  ε > 0 ложно — SafeQP слабее, честно зафиксировано).

Честные границы: факторизация Σ = AᵀA и GN-форма градиента
— посылки (h_emp_/h_model_-слой); тейлоровский барьер
M/6·‖Δ‖³ при липшицевом гессиане — уровень 2, НЕ доказано
(требует интегрального остатка Тейлора).
-/

open Matrix

namespace Hagi

variable {n k : Type*} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

/-! ## R129: PSD-ядро интерференции -/

/-- Факторизованная квадратичная форма интерференции:
v ⬝ᵥ (Σ.mulVec v) = ‖A.mulVec v‖² при Σ = Aᵀ·A. -/
theorem quad_form_factorization (A : Matrix k n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((Aᵀ * A).mulVec v) = (A.mulVec v) ⬝ᵥ (A.mulVec v) := by
  have hkey : (Aᵀ * A).mulVec v = Aᵀ.mulVec (A.mulVec v) := by
    simp [Matrix.mulVec, Matrix.mul_assoc]
  rw [hkey, dotProduct_comm v (Aᵀ.mulVec (A.mulVec v)),
    ← Matrix.vecMul_transpose Aᵀ (A.mulVec v),
    Matrix.dotProduct_mulVec,
    show ((Aᵀ)ᵀ) = A from Matrix.transpose_transpose A]

/-- **Ядро фактора ⟺ нулевая интерференция**: сумма
квадратов = 0 ⟺ каждый квадрат = 0. -/
theorem quad_form_zero_iff (A : Matrix k n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((Aᵀ * A).mulVec v) = 0 ↔ A.mulVec v = 0 := by
  rw [quad_form_factorization]
  constructor
  · intro h
    funext i
    have hsum : ∑ i', (A.mulVec v) i' * (A.mulVec v) i' = 0 := h
    have hterm := Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg _) |>.mp hsum i (Finset.mem_univ i)
    exact eq_zero_of_mul_self_eq_zero hterm
  · intro h
    rw [h, dotProduct_zero]

/-- **Ядро Σ ⟹ нулевая квадратичная интерференция**
(машиносчитанная часть R129-ревизии). -/
theorem kernel_interference_zero (A : Matrix k n ℝ) (v : n → ℝ)
    (hker : (Aᵀ * A).mulVec v = 0) :
    v ⬝ᵥ ((Aᵀ * A).mulVec v) = 0 := by
  rw [hker, dotProduct_zero]

/-! ## R131: мост Гаусса-Ньютона (GPM ⟹ SafeQP) -/

/-- Внутреннее произведение GN-градиента с направлением из
ker(X): g = Xᵀ·r (масштаб 1/m опущен — константа) ⟹
⟨g, d⟩ = ⟨r, X·d⟩ = 0. -/
theorem gn_grad_inner_ker (X : Matrix k n ℝ) (r : k → ℝ)
    (d : n → ℝ) (hker : X.mulVec d = 0) :
    (Xᵀ.mulVec r) ⬝ᵥ d = 0 := by
  rw [dotProduct_comm]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose, hker]
  simp

/-- **GPM ⟹ SafeQP-допустимость в GN-режиме**: направление
из ker(X) удовлетворяет ограничению SafeQP
⟨g, d⟩ ≥ −ε при ЛЮБОМ остатке r и любом ε ≥ 0.
(Достаточность; обратная импликация при ε > 0 ложна —
SafeQP-конус строго шире ядра.) -/
theorem gpm_implies_safeqp_gn (X : Matrix k n ℝ) (r : k → ℝ)
    (d : n → ℝ) (hker : X.mulVec d = 0) (eps : ℝ) (heps : 0 ≤ eps) :
    -eps ≤ (Xᵀ.mulVec r) ⬝ᵥ d := by
  rw [gn_grad_inner_ker X r d hker]
  linarith

end Hagi

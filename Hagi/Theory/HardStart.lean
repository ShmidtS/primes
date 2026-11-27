/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# HardStart — перевес трудных стартов в state-carry BPTT

optimal_lm.py (HARD_START > 0, state_carry): при `wrap` старт потока
выбирается из `H` кандидатов с весом `w_j = 1/(1 + c_j)`, `c_j` — частота
3-байтового контекста в bypass_t3 (редкий/неизвестный контекст — тяжелее).
Это распределение данных обучения, а не оценка.

* `hardWeight c j = 1/(1 + c j)`;
* `hardStart_two_cand` — на частотах `(0, 3)`: `q = (4/5, 1/5)`;
* `hardStart_rare_heavier` — редкий контекст получает вес `4/5 > 1/2`;
* `hardStart_eval_biased` — `E_q[ℓ] − E_u[ℓ] = 3/10·(ℓ₀ − ℓ₁)`: CE, измеренный
  на обучающих потоках, смещён; валидация — только по равномерным окнам ValWindows.lean.
-/

namespace Hagi.Theory.HardStart

/-- HARD_START (`optimal_lm.py`): старт потока выбирается из кандидатов с
весом `w_j = 1/(1+c_j)` (`c_j` — частота 3-байтового контекста; редкий
контекст тяжелее), `q_j = w_j/Σw`. -/
noncomputable def hardWeight (c : Fin 2 → ℝ) : Fin 2 → ℝ := fun j => 1 / (1 + c j)
/-- Взвешенное среднее потерь по `q` отличается от равномерного: на двух
кандидатах с частотами `(0, 3)` и потерями `(ℓ₀, ℓ₁)` — `q = (4/5, 1/5)`. -/
theorem hardStart_two_cand (ℓ : Fin 2 → ℝ) :
    let c : Fin 2 → ℝ := ![0, 3]
    let w := hardWeight c
    let q := fun j => w j / ∑ i, w i
    (∑ j, q j * ℓ j) = (4/5) * ℓ 0 + (1/5) * ℓ 1 := by
  intro c w q
  simp [hardWeight, w, c, Fin.sum_univ_two, q]
  ring
/-- Смещение: среднее по `q` завышает CE, если редкий контекст труднее
(`ℓ₁ ≥ ℓ₀` не достаточно — вес редкого меньше!). С weight `1/(1+c)` редкий
контекст (c = 0) получает БОЛЬШИЙ вес: `q₀ = 4/5 > 1/2`. -/
theorem hardStart_rare_heavier :
    let c : Fin 2 → ℝ := ![0, 3]
    let w := hardWeight c
    (fun j => w j / ∑ i, w i) 0 = 4/5 := by
  intro c w
  simp [hardWeight, w, c, Fin.sum_univ_two]
  ring
/-- Смещение оценки CE на hard-start потоках: `E_q[ℓ] − E_u[ℓ] = (q₀ − 1/2)(ℓ₀ − ℓ₁)`
— при `q₀ = 4/5` это `3/10·(ℓ₀ − ℓ₁)`. Валидация обязана идти по равномерным
окнам (`ValWindows`), а не по обучающим потокам. -/
theorem hardStart_eval_biased (ℓ : Fin 2 → ℝ) :
    let c : Fin 2 → ℝ := ![0, 3]
    let w := hardWeight c
    let q := fun j => w j / ∑ i, w i
    (∑ j, q j * ℓ j) - (1/2) * (ℓ 0 + ℓ 1) = (3/10) * (ℓ 0 - ℓ 1) := by
  intro c w q
  simp [hardWeight, w, c, Fin.sum_univ_two, q]
  ring

end Hagi.Theory.HardStart

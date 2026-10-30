import Mathlib

/-!
# Lion: sign-обновление (источник №47)

Источник №47: Chen et al., "Symbolic Discovery of
Optimization Algorithms" (arXiv 2302.06675, Lion).
Обновление x ← x − η·sign(m): направление — только ЗНАКИ
момента, величина отбрасывается: размер шага по ℓ₂
контролируется ТОЛЬКО η (не зависит от амплитуды
градиентов — robustness к выбросам шкалы).

Формализованное ядро (строгое):
- `signStep`: шаг η·sign(m);
- `sign_sq_le_one`: sign(i)² ≤ 1 (значение из {−1,0,1});
- `lion_step_norm_bound`: ‖шаг‖₂ ≤ η·√d — норма шага
  ограничена константой размерности: LION НИКОГДА не
  делает большого шага, даже при взрывном градиенте
  (контраст с AdaGrad-затуханием: фиксированная шкала).
-/

namespace Hagi.Optimization.Lion

open Finset

variable {d : ℕ}

/-- Знак скаляра. -/
noncomputable def sgn (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- Sign-шаг Lion. -/
noncomputable def signStep (eta : ℝ) (m : Fin d → ℝ) : Fin d → ℝ :=
  fun i => eta * sgn (m i)

theorem sign_sq_le_one (x : ℝ) : (sgn x) ^ 2 ≤ 1 := by
  unfold sgn
  split
  · norm_num
  · split
    · norm_num
    · norm_num

/-- НОРМА ШАГА LION ОГРАНИЧЕНА: ∑ (η·sgn m i)² ≤ η²·d —
шаг никогда не превышает η·√d, даже при взрывном m. -/
theorem lion_step_norm_bound (eta : ℝ) (m : Fin d → ℝ) :
    ∑ i, (signStep eta m i) ^ 2 ≤ eta ^ 2 * (d : ℝ) := by
  have h1 : ∀ i ∈ Finset.univ, (signStep eta m i) ^ 2
      ≤ eta ^ 2 * 1 := by
    intro i _
    unfold signStep
    have hs := sign_sq_le_one (m i)
    have hmul : (eta * sgn (m i)) ^ 2 = eta ^ 2 * (sgn (m i)) ^ 2 := by
      ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg eta)
  have h2 := Finset.sum_le_sum (f := fun i => (signStep eta m i) ^ 2)
    (g := fun _ => eta ^ 2 * 1) h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h2
  simp [mul_one] at h2
  nlinarith [h2]

end Hagi.Optimization.Lion

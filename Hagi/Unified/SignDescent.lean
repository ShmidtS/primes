import Hagi.Unified.DescentCore
import Hagi.Step.SignSGD

/-!
# Мост SignSGD → DescentCore

Знаковая компрессия градиента интегрируется в контракт
спуска: немасштабированный sign-шаг НЕ выровнен в смысле
`aligned` (норма знакового вектора — число ненулевых
координат — может превышать ℓ₁-норму градиента).
Масштабированный шаг s·sign(g) при s = ‖g‖₁/n выровнен:
связь signSGD с нормализованным спуском. Как следствие —
гарантированное чистое убывание через `descent_drop` для
сжатого шага.
-/

namespace Hagi.Unified.SignDescent

open Hagi.Unified.DescentCore Hagi.Step.SignSGD

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Масштаб знакового шага: средняя абсолютная величина
градиента. -/
noncomputable def signScale (g : k → ℝ) : ℝ :=
  (∑ i, |g i|) / (Fintype.card k)

/-- Знак координаты, умноженный на координату, — модуль
координаты. -/
theorem sgn1_mul_self (x : ℝ) : sgn1 x * x = |x| := by
  unfold sgn1
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos h, abs_of_neg h]
    ring
  · rw [if_neg (by linarith), if_pos h, h]
    simp
  · rw [if_neg (by linarith), if_neg (by linarith : ¬ x = 0),
      abs_of_pos h]
    ring

/-- Квадрат знаковой координаты — индикатор ненулевой. -/
theorem sgn1_sq (x : ℝ) : (sgn1 x)^2 = if x = 0 then (0:ℝ) else 1 := by
  unfold sgn1
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos h, if_neg (by linarith)]
    norm_num
  · rw [if_neg (by linarith), if_pos h]
    norm_num
  · rw [if_neg (by linarith), if_neg (by linarith : ¬ x = 0)]
    norm_num

/-- Число ненулевых координат не превосходит мощность
типа. -/
theorem count_nonzero_le (g : k → ℝ) :
    (∑ i, if g i = 0 then (0:ℝ) else 1) ≤ (Fintype.card k : ℝ) := by
  have h1 : ∀ i ∈ Finset.univ,
      ((if g i = 0 then (0:ℝ) else 1) : ℝ) ≤ (1:ℝ) := by
    intro i _
    split <;> norm_num
  have h : (∑ i ∈ Finset.univ, ((if g i = 0 then (0:ℝ) else 1) : ℝ))
      ≤ (∑ i ∈ Finset.univ, (1:ℝ)) := Finset.sum_le_sum h1
  simp only [Finset.sum_const, if_true] at h
  norm_num at h
  exact h

/-- ГЛАВНАЯ ТЕОРЕМА: масштабированный sign-шаг выровнен. -/
theorem sign_scaled_aligned (J : Objective k) (x : k → ℝ) :
    aligned J x (fun i => signScale (J.grad x) * sgn1 (J.grad x i)) := by
  set g := J.grad x with hgdef
  set s := signScale g with hsdef
  have hpt2 : ∀ i : k, (s * sgn1 (g i))^2
      = s^2 * (if g i = 0 then (0:ℝ) else 1) := by
    intro i
    rw [mul_pow, sgn1_sq]
  have hpt3 : ∀ i : k, g i * (s * sgn1 (g i)) = s * |g i| := by
    intro i
    rw [← sgn1_mul_self (g i)]
    ring
  have hn2 : nrm2 (fun i => s * sgn1 (g i))
      = s^2 * (∑ i, if g i = 0 then (0:ℝ) else 1) := by
    unfold nrm2
    rw [Finset.sum_congr rfl (fun i _ => hpt2 i), ← Finset.mul_sum]
  have hin : inprod g (fun i => s * sgn1 (g i))
      = s * (∑ i, |g i|) := by
    unfold inprod
    rw [Finset.sum_congr rfl (fun i _ => hpt3 i), ← Finset.mul_sum]
  unfold aligned
  rw [hn2, hin, hsdef, signScale]
  have hcnt := count_nonzero_le g
  have hnn : ((Fintype.card k : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hstep1 : (((∑ i, |g i|) / (Fintype.card k : ℝ))^2
        * (∑ i, if g i = 0 then (0:ℝ) else 1))
      ≤ ((∑ i, |g i|) / (Fintype.card k : ℝ))^2
        * ((Fintype.card k : ℝ)) :=
    mul_le_mul_of_nonneg_left hcnt (sq_nonneg _)
  have hstep2 : ((∑ i, |g i|) / (Fintype.card k : ℝ))^2
      * ((Fintype.card k : ℝ))
      = ((∑ i, |g i|) / (Fintype.card k : ℝ)) * (∑ i, |g i|) := by
    field_simp
  linarith [hstep1, hstep2]

/-- СЛЕДСТВИЕ: сжатый sign-шаг даёт гарантированное чистое
убывание (связь signSGD с контрактом спуска). -/
theorem sign_descent (J : Objective k) (x : k → ℝ)
    (eta : ℝ) (heta : 0 < eta) (hetaL : eta ≤ 1 / J.L) :
    J.f (x - fun i => eta * (signScale (J.grad x) * sgn1 (J.grad x i)))
      ≤ J.f x
        - eta * (1 - J.L * eta / 2)
            * nrm2 (fun i => signScale (J.grad x) * sgn1 (J.grad x i)) :=
  descent_drop J x
    (fun i => signScale (J.grad x) * sgn1 (J.grad x i))
    (sign_scaled_aligned J x) eta heta hetaL

end Hagi.Unified.SignDescent

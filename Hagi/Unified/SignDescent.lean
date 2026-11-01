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

/-- GENERIC-МОСТ: выровненность масштабированного sign-шага
произвольного направления относительно градиента — при
условии согласованности направления с градиентом (ядро
интеграции Lion: момент согласован с градиентом). -/
theorem scaled_sign_aligned_of_coherence
    (J : Objective k) (x m : k → ℝ)
    (hcoh : (∑ i, |m i|) / (Fintype.card k)
      * (∑ i, if m i = 0 then (0:ℝ) else 1)
        ≤ ∑ i, J.grad x i * sgn1 (m i)) :
    aligned J x
      (fun i => signScale m * sgn1 (m i)) := by
  set s := signScale m with hsdef
  have hpt2 : ∀ i : k, (s * sgn1 (m i))^2
      = s^2 * (if m i = 0 then (0:ℝ) else 1) := by
    intro i
    rw [mul_pow, sgn1_sq]
  have hpt3 : ∀ i : k, J.grad x i * (s * sgn1 (m i))
      = s * (J.grad x i * sgn1 (m i)) := by
    intro i
    ring
  have hn2 : nrm2 (fun i => s * sgn1 (m i))
      = s^2 * (∑ i, if m i = 0 then (0:ℝ) else 1) := by
    unfold nrm2
    rw [Finset.sum_congr rfl (fun i _ => hpt2 i), ← Finset.mul_sum]
  have hin : inprod (J.grad x) (fun i => s * sgn1 (m i))
      = s * (∑ i, J.grad x i * sgn1 (m i)) := by
    unfold inprod
    rw [Finset.sum_congr rfl (fun i _ => hpt3 i), ← Finset.mul_sum]
  unfold aligned
  rw [hn2, hin, hsdef, signScale]
  have hnn : (0:ℝ) < (Fintype.card k : ℝ) := by positivity
  have habs : (0:ℝ) ≤ ∑ i, |m i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set A := (∑ i, |m i|) with hA
  set N := ((Fintype.card k : ℝ)) with hN
  set S := (∑ i, J.grad x i * sgn1 (m i)) with hS
  set M := (∑ i, if m i = 0 then (0:ℝ) else 1) with hM
  have hcoh2 : (A * M) / N ≤ S := by
    rw [div_mul_eq_mul_div] at hcoh
    exact hcoh
  have hcoh' : A * M ≤ S * N := by
    rw [div_le_iff₀ hnn] at hcoh2
    exact hcoh2
  have hAA : A * (A * M) ≤ A * (S * N) :=
    mul_le_mul_of_nonneg_left hcoh' habs
  have hlast := mul_le_mul_of_nonneg_right hAA (le_of_lt hnn)
  calc ((A / N)^2) * M = A * (A * M) / N^2 := by
        field_simp
    _ ≤ A * (S * N) / N^2 := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < N^2)
          (by positivity : (0:ℝ) < N^2)]
        nlinarith [mul_le_mul_of_nonneg_right hAA
          (le_of_lt (by positivity : (0:ℝ) < N^2))]
    _ = (A / N) * S := by
        field_simp

/-- ЗНАК ОПТИМАЛЕН на ℓ∞-кубе: для любого направления v
с покоординатными |v i| ≤ 1 линейный функционал
⟨g, v⟩ ≤ ⟨g, sign(g)⟩ = ‖g‖₁ — ядро спектральной
оптимальности Muon (ортогонализация максимизирует
выравнивание; диагональное ядро — знаковое). -/
theorem sign_is_pointwise_max (g v : k → ℝ)
    (hv : ∀ i, |v i| ≤ 1) :
    (∑ i, g i * v i) ≤ ∑ i, |g i| := by
  have hpt : ∀ i : k, g i * v i ≤ |g i| := by
    intro i
    rcases lt_trichotomy (g i) 0 with h | h | h
    · have hv' : v i ≤ 1 := le_trans (abs_le.mp (hv i)).2 (le_refl _)
      have hnn : |g i| = -g i := abs_of_neg h
      nlinarith [mul_le_mul_of_nonneg_right hv' (le_of_lt (by linarith : (0:ℝ) < -g i)),
        abs_le.mp (hv i)]
    · have hgv : g i * v i = 0 := by simp [h]
      rw [hgv, h]
      norm_num
    · have hv' : -1 ≤ v i := (abs_le.mp (hv i)).1
      have hpos : |g i| = g i := abs_of_pos h
      nlinarith [mul_le_mul_of_nonneg_left hv' (le_of_lt h),
        abs_le.mp (hv i)]
  exact Finset.sum_le_sum (fun i _ => hpt i)

/-- LION-МОСТ: sign-шаг по моменту m согласован с градиентом
⟹ масштабированный Lion-шаг даёт чистое убывание. -/
theorem lion_descent (J : Objective k) (x m : k → ℝ)
    (hcoh : (∑ i, |m i|) / (Fintype.card k)
      * (∑ i, if m i = 0 then (0:ℝ) else 1)
        ≤ ∑ i, J.grad x i * sgn1 (m i))
    (eta : ℝ) (heta : 0 < eta) (hetaL : eta ≤ 1 / J.L) :
    J.f (x - fun i => eta * (signScale m * sgn1 (m i)))
      ≤ J.f x
        - eta * (1 - J.L * eta / 2)
            * nrm2 (fun i => signScale m * sgn1 (m i)) :=
  descent_drop J x
    (fun i => signScale m * sgn1 (m i))
    (scaled_sign_aligned_of_coherence J x m hcoh) eta heta hetaL

end Hagi.Unified.SignDescent

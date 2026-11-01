import Hagi.Unified.EFResidual
import Hagi.Unified.SignEFQuad

/-!
# Пороговый компрессор: остаток — малая часть

Пороговое сжатие передаёт только большие координаты;
остаток (несланданное) — в точности малые координаты и
потому НЕ ПРЕВЫШАЕТ нормы входа. Контраст со знаковым
компрессором, у которого остаток растёт с носителя.
-/

namespace Hagi.Unified.ThrComp

open Hagi.Unified.DescentCore Hagi.Unified.DescentCoreQuad
open Hagi.Unified.QuadGDRate Hagi.Unified.SignEFQuad

variable {k : Type*} [Fintype k]

/-- Пороговый компрессор: большие координаты — точно,
малые — нуль. -/
noncomputable def thrComp (τ : ℝ) (v : k → ℝ) : k → ℝ :=
  fun i => if τ ≤ |v i| then v i else 0

/-- Большие координаты передаются точно. -/
theorem thrComp_keeps (τ : ℝ) (v : k → ℝ) (i : k)
    (h : τ ≤ |v i|) : thrComp τ v i = v i := by
  unfold thrComp
  rw [if_pos h]

/-- Остаток — в точности малые координаты. -/
theorem thrComp_residual (τ : ℝ) (v : k → ℝ) :
    v - thrComp τ v = fun i => if |v i| < τ then v i else 0 := by
  funext i
  show v i - thrComp τ v i = if |v i| < τ then v i else 0
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h, if_neg (by linarith [h])]
    simp
  · rw [if_neg h, if_pos (by linarith [h])]
    ring

/-- ГЛАВНАЯ: остаток порогового сжатия не превосходит
нормы входа — малая часть целого, без гипотез. -/
theorem thrComp_residual_le (τ : ℝ) (v : k → ℝ) :
    nrm2 (v - thrComp τ v) ≤ nrm2 v := by
  unfold nrm2
  simp only [Pi.sub_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h]
    simp
    positivity
  · rw [if_neg h]
    simp

/-- Следствие: EF-остаток порогового компрессора
контролируется нормой сообщения — резидуал не может
превысить того, что пришло. -/
theorem ef_thr_residual_control (τ : ℝ) (d e : k → ℝ) :
    nrm2 (d + e - thrComp τ (d + e)) ≤ nrm2 (d + e) :=
  thrComp_residual_le τ (d + e)

/-- АБСОЛЮТНЫЙ БАРЬЕР: остаток не превосходит
количества координат на квадрат порога — независимо от
истории. -/
theorem thrComp_barrier (τ : ℝ) (v : k → ℝ) :
    nrm2 (v - thrComp τ v)
      ≤ (Fintype.card k : ℝ) * τ ^ 2 := by
  have h : ∀ i, (v i - thrComp τ v i)^2 ≤ τ ^ 2 := by
    intro i
    unfold thrComp
    by_cases hc : τ ≤ |v i|
    · rw [if_pos hc]
      simp
      positivity
    · rw [if_neg hc]
      have hlt : |v i| < τ := not_le.mp hc
      have hnn : (0:ℝ) ≤ |v i| := abs_nonneg _
      have hle : (v i)^2 ≤ τ ^ 2 := by
        rw [← sq_abs]
        nlinarith
      simpa using hle
  unfold nrm2
  simp only [Pi.sub_apply]
  calc ∑ i, (v i - thrComp τ v i)^2 ≤ ∑ i, τ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card k : ℝ) * τ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Норма масштабированного вектора. -/
theorem nrm2_smul (c : ℝ) (v : k → ℝ) :
    nrm2 (c • v) = c ^ 2 * nrm2 v := by
  unfold nrm2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Коши–Буняковский в квадратичной форме. -/
theorem inprod_abs_le (u v : k → ℝ) :
    |inprod u v| ≤ Real.sqrt (nrm2 u * nrm2 v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  unfold inprod at hcs
  show |∑ i, u i * v i|
    ≤ Real.sqrt ((∑ i, (u i)^2) * (∑ i, (v i)^2))
  have hkey : |∑ i, u i * v i| ^ 2
      ≤ (∑ i, (u i)^2) * (∑ i, (v i)^2) := by
    rw [sq_abs]
    exact hcs
  calc |∑ i, u i * v i|
      = Real.sqrt (|∑ i, u i * v i| ^ 2) :=
        (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt ((∑ i, (u i)^2) * (∑ i, (v i)^2)) :=
        Real.sqrt_le_sqrt hkey

/-- ИТОГОВАЯ ПРАКТИЧЕСКАЯ ТЕОРЕМА: пороговое EF-обучение —
линейная скорость плюс АБСОЛЮТНЫЙ тау-барьер. Ни одной
гипотезы о резидуале: он ограничен количеством координат
на квадрат порога по построению компрессора. -/
theorem thr_ef_quality (a : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2)
    (x0 : k → ℝ) (τ : ℝ) (e : ℕ → k → ℝ)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - thrComp τ (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • thrComp τ
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (he0 : e 0 = 0) (n : ℕ) :
    quadE a (xC n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0
        + eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
            * ((Fintype.card k : ℝ) * τ ^ 2))
        + (eta ^ 2 / 2) * ((Fintype.card k : ℝ) * τ ^ 2) := by
  have hmain := Hagi.Unified.SignEFQuad.quad_ef_quality_rate a
    eta heta heta2 x0 e (thrComp τ) hEF xC hxC hx0 n
  rw [he0, sub_zero] at hmain
  have hbar : nrm2 (e n)
      ≤ (Fintype.card k : ℝ) * τ ^ 2 := by
    match n with
    | 0 =>
      have hn0 : nrm2 (e 0) = 0 := by
        rw [he0]
        simp [nrm2]
      rw [hn0]
      exact mul_nonneg (by positivity) (sq_nonneg τ)
    | m + 1 =>
      have hstep := hEF m
      have h := thrComp_barrier τ
        (quadGrad a (quadGD a eta x0 m) + e m)
      rw [hstep]
      exact h
  have hsm := nrm2_smul eta (e n)
  have hin : inprod (quadGrad a (quadGD a eta x0 n))
      (eta • e n) ≤ eta * Real.sqrt (nrm2 (quadGrad a
        (quadGD a eta x0 n)) * ((Fintype.card k : ℝ) * τ ^ 2)) := by
    have hcs := inprod_abs_le (quadGrad a (quadGD a eta x0 n))
      (e n)
    have hη : (0:ℝ) ≤ eta := heta.le
    have hip : inprod (quadGrad a (quadGD a eta x0 n)) (eta • e n)
        = eta * inprod (quadGrad a (quadGD a eta x0 n)) (e n) := by
      unfold inprod
      have hterm : ∀ i, (quadGrad a (quadGD a eta x0 n)) i
            * (eta • e n) i
          = eta * ((quadGrad a (quadGD a eta x0 n)) i * e n i) := by
        intro i
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    have hg : (0:ℝ) ≤ nrm2 (quadGrad a (quadGD a eta x0 n)) := by
      unfold nrm2
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqr : Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * nrm2 (e n))
        ≤ Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * ((Fintype.card k : ℝ) * τ ^ 2)) :=
      Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hbar hg)
    rw [hip]
    calc eta * inprod (quadGrad a (quadGD a eta x0 n)) (e n)
        ≤ eta * |inprod (quadGrad a (quadGD a eta x0 n)) (e n)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hη
      _ ≤ eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * nrm2 (e n)) :=
          mul_le_mul_of_nonneg_left hcs hη
      _ ≤ eta * Real.sqrt (nrm2 (quadGrad a (quadGD a eta x0 n))
          * ((Fintype.card k : ℝ) * τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsqr hη
  have hfin : eta ^ 2 * nrm2 (e n)
      ≤ eta ^ 2 * ((Fintype.card k : ℝ) * τ ^ 2) :=
    mul_le_mul_of_nonneg_left hbar (sq_nonneg eta)
  linarith [hmain, hin, hsm, hfin]

end Hagi.Unified.ThrComp
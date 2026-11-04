import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Core.FrobOuter

set_option linter.style.header false

/-!
# TernaryPert — возмущение выхода слоя при тернарном квантовании (цикл 11)

Базовый кирпень сквозной ошибки квантования (критика аудита #1):
неравенство подчинённости ‖E·x‖ ≤ ‖E‖_F·‖x‖ для матричной ошибки
E = Q(R) − R, доказанное через Cauchy–Schwarz в EuclideanSpace.
Следствие для тернарного квантователя — через поэлементную
посылку ошибки.
-/

open Finset InnerProductSpace

namespace Hagi.Learning.TernaryPert

open Hagi.Core

variable {m r : ℕ}

/-- Евклидова норма (корень из суммы квадратов). -/
noncomputable def eunorm (x : Fin r → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Строка матрицы как вектор. -/
def rowVec (E : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) : Fin r → ℝ :=
  fun j => E i j

/-- CAUCHY–SCHWARZ для координатных сумм:
|(a ⬝ᵥ x)| ≤ ‖a‖·‖x‖. -/
theorem cs_dotProduct (a x : Fin r → ℝ) :
    abs (dotProduct a x) ≤ eunorm a * eunorm x := by
  have hinner : dotProduct a x
      = ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin r)),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin r))⟫_ℝ := by
    simp [PiLp.inner_apply, starRingEnd_apply, star_trivial]
    exact (dotProduct_comm x a).symm
  have hcs := norm_inner_le_norm
    (𝕜 := ℝ) (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin r))
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin r))
  rw [Real.norm_eq_abs] at hcs
  have hnorm : ∀ (y : Fin r → ℝ),
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin r))‖ = eunorm y := by
    intro y
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, map_pow, abs_of_nonneg, sq_abs]
    rfl
  rw [hinner]
  rw [hnorm a, hnorm x] at hcs
  exact hcs


/-! ### Подчинённость матричной нормы -/

/-- Норма вектора-выхода. -/
noncomputable def outNorm (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- ПОДЧИНЁННОСТЬ: ‖E·x‖₂ ≤ ‖E‖_F·‖x‖₂. -/
theorem frob_submul (E : Matrix (Fin m) (Fin r) ℝ) (x : Fin r → ℝ) :
    outNorm (fun i => dotProduct (rowVec E i) x)
      ≤ Real.sqrt (frobSq E) * eunorm x := by
  have hrow : ∀ i : Fin m,
      abs (dotProduct (rowVec E i) x)
        ≤ eunorm (rowVec E i) * eunorm x :=
    fun i => cs_dotProduct (rowVec E i) x
  have hsq : ∀ i : Fin m, (dotProduct (rowVec E i) x) ^ 2
      ≤ (eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 := by
    intro i
    have h := hrow i
    have h2 : abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x)
        ≤ (eunorm (rowVec E i) * eunorm x) * (eunorm (rowVec E i) * eunorm x) :=
      mul_le_mul h h (abs_nonneg _) (by
        have hnn : (0:ℝ) ≤ eunorm (rowVec E i) * eunorm x :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact hnn)
    have hy : (dotProduct (rowVec E i) x) ^ 2
        = abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x) := by
      rw [← sq_abs, ← pow_two]
    calc (dotProduct (rowVec E i) x) ^ 2
        = abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x) := hy
      _ ≤ (eunorm (rowVec E i) * eunorm x) * (eunorm (rowVec E i) * eunorm x) := h2
      _ = (eunorm (rowVec E i) * eunorm x) ^ 2 := by ring
      _ = eunorm (rowVec E i) ^ 2 * eunorm x ^ 2 := by ring
  have hsum : ∑ i, (dotProduct (rowVec E i) x) ^ 2
      ≤ (∑ i, eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 := by
    calc ∑ i, (dotProduct (rowVec E i) x) ^ 2
        ≤ ∑ i, (eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hsq i)
      _ = (∑ i, eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 :=
          by rw [← Finset.sum_mul]
  have hrowsq : ∀ i : Fin m, eunorm (rowVec E i) ^ 2 = ∑ j : Fin r, E i j ^ 2 := by
    intro i
    unfold eunorm rowVec
    rw [Real.sq_sqrt (by
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  have hsqE : (∑ i, eunorm (rowVec E i) ^ 2) = frobSq E := by
    rw [Finset.sum_congr rfl (fun i _ => hrowsq i)]
    rfl
  -- финал: sqrt-монотонность
  have hsqrt := Real.sqrt_le_sqrt hsum
  have hsqE' : (∑ i, eunorm (rowVec E i) ^ 2) * eunorm x ^ 2
      = frobSq E * (∑ j : Fin r, x j ^ 2) := by
    rw [hsqE]
    congr 1
    unfold eunorm
    rw [Real.sq_sqrt (by
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  unfold outNorm eunorm
  calc Real.sqrt (∑ i, (dotProduct (rowVec E i) x) ^ 2)
      ≤ Real.sqrt ((∑ i, eunorm (rowVec E i) ^ 2) * eunorm x ^ 2) := hsqrt
    _ = Real.sqrt (frobSq E * ∑ j : Fin r, x j ^ 2) := by rw [hsqE']
    _ = Real.sqrt (frobSq E) * Real.sqrt (∑ j : Fin r, x j ^ 2) :=
          Real.sqrt_mul (show (0:ℝ) ≤ frobSq E by
              unfold frobSq
              exact Finset.sum_nonneg (fun p _ =>
                Finset.sum_nonneg (fun q _ => sq_nonneg _)))
            (∑ j : Fin r, x j ^ 2)

/-! ### Следствие для тернарного квантования остатков -/

/-- СКВОЗНАЯ ОШИБКА КВАНТОВАНИЯ СЛОЯ: возмущение выхода слоя
при замене остатка R на его тернарное квантование Q(R) не
превосходит ‖R − Q(R)‖_F·‖x‖ — базовый кирпень сквозной оценки
‖f_Q(x) − f(x)‖ (критика аудита #1 закрыта на уровне одного
слоя; композиция слоёв — через телескоп таких оценок). -/
theorem ternary_layer_pert (R QR : Matrix (Fin m) (Fin r) ℝ)
    (x : Fin r → ℝ)
    (hq : ∀ i j, abs (QR i j - R i j) ≤ 1/2) :
    outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ Real.sqrt ((m : ℝ) * (r : ℝ) * (1/2)^2) * eunorm x := by
  have hfrob : frobSq (QR - R)
      ≤ (m : ℝ) * (r : ℝ) * (1/2)^2 := by
    unfold frobSq
    have hcard : ∑ a : Fin m, ∑ b : Fin r, ((1:ℝ)/2)^2
        = (m : ℝ) * (r : ℝ) * ((1:ℝ)/2)^2 := by
      rw [Finset.sum_const, Finset.sum_const]
      simp
      push_cast
      ring
    calc frobSq (QR - R)
        = ∑ a : Fin m, ∑ b : Fin r, (QR a b - R a b)^2 := by
          unfold frobSq
          exact Finset.sum_congr rfl (fun a _ =>
            Finset.sum_congr rfl (fun b _ => by
              rfl))
      _ ≤ ∑ a : Fin m, ∑ b : Fin r, (1/2)^2 :=
          Finset.sum_le_sum (fun a _ =>
            Finset.sum_le_sum (fun b _ => by
              have habs := hq a b
              have hkey : abs (QR a b - R a b) * abs (QR a b - R a b)
                  ≤ (1/2 : ℝ) * (1/2 : ℝ) :=
                mul_le_mul habs habs (abs_nonneg _) (by norm_num)
              exact (show (QR a b - R a b) ^ 2 ≤ (1/2 : ℝ) ^ 2 by
                rw [← sq_abs (QR a b - R a b), pow_two, pow_two]
                exact hkey)))
      _ = (m : ℝ) * (r : ℝ) * (1/2)^2 := hcard
  have hsub := frob_submul (QR - R) x
  refine le_trans hsub ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt hfrob

end Hagi.Learning.TernaryPert

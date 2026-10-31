import Mathlib

/-!
# ModelSoup / EMA — усреднение весов (источник №73:
# "Model Soups: Averaging Weights of Multiple Fine-Tuned
# Models", arXiv 2203.05482; EMA/Polyak-усреднение)

Суп из K моделей = выпуклая комбинация параметров.
Формализуем честные гарантии:

1. `soup_mem`: суп лежит в[min, max] параметров-ингредиентов
   (выпуклая оболочка) — суп не может выйти за границы
   ни одной из моделей.
2. `soup_loss_le_avg` (Jensen): если функция потерь ВЫПУКЛА
   по параметру, потеря супа ≤ средневзвешенной потери
   ингредиентов — выпуклым лоссам усреднение параметров
   бесплатно (мотивация Model Soups).
3. EMA-рекурсия: β ∈ (0,1), EMA_t = β·EMA_{t-1} + (1−β)·x_t;
   `ema_invariant`: EMA остаётся в [lo, hi] на любом
   горизонте (сглаживание без выхода за диапазон данных).
-/

namespace Hagi.Model.ModelSoup

open Finset

variable {K : Type*} [Fintype K] [Nonempty K]

/-- Суп: выпуклая комбинация параметров. -/
def soup (w : K → ℝ) (x : K → ℝ) : ℝ := ∑ i, w i * x i

/-- СУП В ГРАНИЦАХ: при неотрицательных весах с суммой 1 и
ингредиентах в [c, d] суп лежит в [c, d] (выпуклая
оболочка: усреднение не изобретает новых значений). -/
theorem soup_mem (w x : K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (c d : ℝ)
    (hx : ∀ i, c ≤ x i ∧ x i ≤ d) :
    c ≤ soup w x ∧ soup w x ≤ d := by
  have hlo : (∑ i, w i * c) ≤ ∑ i, w i * x i :=
    Finset.sum_le_sum fun i _ => by
      have := hx i
      exact mul_le_mul_of_nonneg_left this.1 (hw i)
  have hhi : (∑ i, w i * x i) ≤ ∑ i, w i * d :=
    Finset.sum_le_sum fun i _ => by
      have hxi := (hx i).2
      exact mul_le_mul_of_nonneg_left hxi (hw i)
  have hc : (∑ i, w i * c) = c * (∑ i, w i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hd : (∑ i, w i * d) = d * (∑ i, w i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, mul_one] at hc hd
  constructor <;> unfold soup <;> linarith

/-- JENSEN ДЛЯ СУПА: выпуклый лосс от супа ≤ супа лоссов
(средневзвешенного) — параметрическое усреднение не
увеличивает выпуклый лосс относительно среднего. -/
theorem soup_loss_le_avg (w : K → ℝ) (x : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (f : ℝ → ℝ) {s : Set ℝ} (hconv : ConvexOn ℝ s f)
    (hx : ∀ i, x i ∈ s) :
    f (soup w x) ≤ ∑ i, w i * f (x i) :=
  hconv.map_sum_le (t := Finset.univ) (fun i _ => hw i) hsum (fun i _ => hx i)

/-- EMA-рекурсия (Polyak/ModelSoup-скользящее среднее). -/
noncomputable def ema (β : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | t + 1 => β * ema β x t + (1 - β) * x (t + 1)

/-- EMA-ИНВАРИАНТ: если все наблюдения в [lo, hi] и
β ∈ [0,1], то EMA остаётся в [lo, hi] на любом горизонте —
сглаживание не выходит за диапазон данных. -/
theorem ema_invariant (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (x : ℕ → ℝ) (lo hi : ℝ) (hx : ∀ t, lo ≤ x t ∧ x t ≤ hi) :
    ∀ t, lo ≤ ema β x t ∧ ema β x t ≤ hi := by
  intro t
  induction t with
  | zero => exact hx 0
  | succ t ih =>
      have h1b : 0 ≤ 1 - β := by linarith
      constructor
      · unfold ema
        have hx1 := (hx (t + 1)).1
        have hA : β * lo + (1 - β) * lo
            ≤ β * ema β x t + (1 - β) * x (t + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left ih.1 hβ)
            (mul_le_mul_of_nonneg_left hx1 h1b)
        have hB : β * lo + (1 - β) * lo = lo := by ring
        linarith
      · unfold ema
        have hx1 := (hx (t + 1)).2
        have hA : β * ema β x t + (1 - β) * x (t + 1)
            ≤ β * hi + (1 - β) * hi :=
          add_le_add (mul_le_mul_of_nonneg_left ih.2 hβ)
            (mul_le_mul_of_nonneg_left hx1 h1b)
        have hB : β * hi + (1 - β) * hi = hi := by ring
        linarith

end Hagi.Model.ModelSoup

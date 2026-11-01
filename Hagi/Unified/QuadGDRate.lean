import Hagi.Unified.PLQuad
import Hagi.Unified.PLBudget

/-!
# Явная PL-скорость градиентного спуска

Полная инстанциация PL-цепочки для реального
градиентного спуска на квадратичной машине: итераты
`quadGD`, ТОЧНОЕ равенство убывания за шаг и явный
фактор сжатия (1 − 2η(1 − η/2)) без гипотез о
drop-грани — всё выводится.
-/

namespace Hagi.Unified.QuadGDRate

open Hagi.Unified.PLQuad
open Hagi.Unified.PLLoop
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- Итераты градиентного спуска на квадратичной
машине: x_{t+1} = x_t − η∇E(x_t). -/
def quadGD (a : k → ℝ) (eta : ℝ) (x0 : k → ℝ) :
    ℕ → k → ℝ
  | 0 => x0
  | t + 1 => fun i =>
      quadGD a eta x0 t i - eta * quadGrad a (quadGD a eta x0 t) i

/-- ТОЧНОЕ равенство убывания шага градиентного
спуска: E(x − η∇E(x)) = E(x) − η(1 − η/2)·‖∇E(x)‖. -/
theorem quad_gd_step_eq (a x : k → ℝ) (eta : ℝ) :
    quadE a (fun i => x i - eta * quadGrad a x i)
      = quadE a x - eta * (1 - eta / 2) * nrm2 (quadGrad a x) := by
  have hd : (fun i => x i - eta * quadGrad a x i)
      = x + (fun i => -eta * quadGrad a x i) := by
    funext i
    simp
    ring
  have hdesc := quad_descent_eq a x (fun i => -eta * quadGrad a x i)
  have hin : inprod (quadGrad a x) (fun i => -eta * quadGrad a x i)
      = -eta * nrm2 (quadGrad a x) := by
    unfold inprod nrm2
    show ∑ i, quadGrad a x i * (-eta * quadGrad a x i)
      = -eta * ∑ i, (quadGrad a x i)^2
    have hterm : ∀ i, quadGrad a x i * (-eta * quadGrad a x i)
        = -eta * (quadGrad a x i)^2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  have hnrm : nrm2 (fun i => -eta * quadGrad a x i)
      = eta ^ 2 * nrm2 (quadGrad a x) := by
    unfold nrm2
    show ∑ i, (-eta * quadGrad a x i)^2
      = eta ^ 2 * ∑ i, (quadGrad a x i)^2
    have hterm : ∀ i, (-eta * quadGrad a x i)^2
        = eta ^ 2 * (quadGrad a x i)^2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  rw [hd, hdesc, hin, hnrm]
  ring

/-- ГЛАВНАЯ ТЕОРЕМА: явная линейная скорость градиентного
спуска на квадратичной машине — при η ∈ (0, 1/2] энергия
сжимается фактором (1 − 2η(1 − η/2)) за шаг, без единой
гипотезы о drop-грани. -/
theorem quad_gd_pl_rate (a x0 : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 1 / 2) (n : ℕ) :
    quadE a (quadGD a eta x0 n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0 := by
  set κ := eta * (1 - eta / 2) with hκdef
  have hκ : 0 ≤ κ := by
    rw [hκdef]
    exact mul_nonneg heta.le (by
      have : (0:ℝ) ≤ 1 - eta / 2 := by nlinarith
      linarith)
  have hκ2 : 2 * κ < 1 := by
    have hne : (1:ℝ) - eta ≠ 0 := by
      intro h
      have h1 : (1:ℝ) < eta := by linarith
      linarith
    have hsq : (1 - eta) ^ 2 > 0 := by
      have hring : (1 - eta) ^ 2 = (1 - eta) * (1 - eta) := by
        ring
      rw [hring]
      exact mul_self_pos.mpr hne
    have hexp : 2 * (eta * (1 - eta / 2)) = 1 - (1 - eta) ^ 2 := by
      ring
    rw [hκdef]
    linarith
  set drops : ℕ → ℝ := fun t =>
    eta * (1 - eta / 2) * nrm2 (quadGrad a (quadGD a eta x0 t))
  have hstep : ∀ t : ℕ,
      quadE a (quadGD a eta x0 (t + 1))
        = quadE a (quadGD a eta x0 t) - drops t := by
    intro t
    unfold drops
    have := quad_gd_step_eq a (quadGD a eta x0 t) eta
    simpa [quadGD] using this
  have hmain := quad_pl_rate a (quadGD a eta x0) drops n κ hκ hκ2
    (fun t _ => le_of_eq rfl)
    (fun t _ => by rw [hstep t])
  rw [hκdef, show quadGD a eta x0 0 = x0 from rfl] at hmain
  rw [show (1:ℝ) - 2 * (eta * (1 - eta / 2))
      = 1 - 2 * eta * (1 - eta / 2) from by ring] at hmain
  exact hmain

/-- ОДНОШАГОВАЯ СХОДИМОСТЬ: на квадратичной машине
оптимальный шаг eta = 1 достигает оптимума за ОДИН шаг —
итерат равен якорю, энергия нуль. Минимально возможное
вычисление. -/
theorem quad_gd_one_step (a x : k → ℝ) :
    quadGD a 1 x 1 = a ∧ quadE a (quadGD a 1 x 1) = 0 := by
  have h1 : quadGD a 1 x 1 = a := by
    funext i
    show x i - 1 * (x i - a i) = a i
    ring
  rw [h1]
  exact ⟨rfl, quad_e_star a⟩

/-- Скорость на открытом диапазоне: eta < 1 строго. -/
theorem quad_gd_pl_rate_open (a x0 : k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta < 1) (n : ℕ) :
    quadE a (quadGD a eta x0 n)
      ≤ (1 - 2 * eta * (1 - eta / 2)) ^ n * quadE a x0 := by
  have hκ : (0:ℝ) ≤ eta * (1 - eta / 2) :=
    mul_nonneg heta.le (by
      have : (0:ℝ) ≤ 1 - eta / 2 := by nlinarith
      linarith)
  have hκ2 : 2 * (eta * (1 - eta / 2)) < 1 := by
    have hne : (1:ℝ) - eta ≠ 0 := by
      intro h
      linarith
    have hring : (1 - eta) * (1 - eta)
        = 1 - 2 * (eta * (1 - eta / 2)) := by ring
    have hpos : (0:ℝ) < (1 - eta) * (1 - eta) :=
      mul_self_pos.mpr hne
    rw [hring] at hpos
    linarith
  set drops : ℕ → ℝ := fun t =>
    eta * (1 - eta / 2) * nrm2 (quadGrad a (quadGD a eta x0 t))
  have hstep : ∀ t : ℕ,
      quadE a (quadGD a eta x0 (t + 1))
        = quadE a (quadGD a eta x0 t) - drops t := by
    intro t
    unfold drops
    have := quad_gd_step_eq a (quadGD a eta x0 t) eta
    simpa [quadGD] using this
  have hmain := quad_pl_rate a (quadGD a eta x0) drops n
    (eta * (1 - eta / 2)) hκ hκ2
    (fun t _ => le_of_eq rfl)
    (fun t _ => by rw [hstep t])
  rw [show quadGD a eta x0 0 = x0 from rfl] at hmain
  rw [show (1:ℝ) - 2 * (eta * (1 - eta / 2))
      = 1 - 2 * eta * (1 - eta / 2) from by ring] at hmain
  exact hmain

end Hagi.Unified.QuadGDRate

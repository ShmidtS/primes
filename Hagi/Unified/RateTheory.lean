/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Unified.CertifiedLoop
import Hagi.Unified.DescentCoreQuad
import Hagi.Unified.LoopInstances

/-!
# Теория скоростей (объединённая)

PL-линейная скорость (PLLoop), точная PL на квадратичной
машине (PLQuad), сложностной горизонт и бюджет (PLBudget),
явная скорость градиентного спуска и одношаговый оптимум
(QuadGDRate). Слит из четырёх модулей; имена деклараций
сохранены.
-/

/-!
# Линейная сходимость certified-цикла при PL-условии

Без условия Поляка–Лоясевича certified-цикл гарантирует
лишь остановку в точке «нет сертифицируемого улучшения».
При PL-условии и равномерной нижней грани спуска по
квадрату градиента цепочка шагов даёт ЛИНЕЙНУЮ скорость:
остаточная энергия сжимается геометрически с фактором
(1 − 2κμ).
-/

namespace Hagi.Unified.PLLoop

variable {S : Type*}

/-- ГЛАВНАЯ ТЕОРЕМА: PL-скорость сертифицированной цепочки.
Каждый шаг убивает долю κ квадрата градиента, целевой
функционал удовлетворяет PL-неравенству с параметром μ —
остаток убывает линейно. -/
theorem pl_linear
    (obj : S → ℝ) (Estar κ μ : ℝ)
    (f : ℕ → S) (drops gsqr : ℕ → ℝ) (n : ℕ)
    (hκ : 0 ≤ κ) (hμ : 0 < μ) (hκμ : 2 * κ * μ < 1)
    (hE : ∀ t ≤ n, Estar ≤ obj (f t))
    (hPL : ∀ t ≤ n, 2 * μ * (obj (f t) - Estar) ≤ gsqr t)
    (hdrop : ∀ t < n, κ * gsqr t ≤ drops t)
    (hcert : ∀ t < n,
      obj (f (t + 1)) ≤ obj (f t) - drops t) :
    obj (f n) - Estar
      ≤ (1 - 2 * κ * μ) ^ n * (obj (f 0) - Estar) := by
  have hfactor : (0:ℝ) ≤ 1 - 2 * κ * μ := by
    nlinarith
  revert hE hPL hdrop hcert
  induction n with
  | zero =>
    intro hE hPL hdrop hcert
    rw [pow_zero, one_mul]
  | succ n ih =>
    intro hE hPL hdrop hcert
    have ih' := ih
      (fun t ht => hE t (by omega))
      (fun t ht => hPL t (by omega))
      (fun t ht => hdrop t (by omega))
      (fun t ht => hcert t (by omega))
    have hstep := hcert n (by omega)
    have hPLn := hPL n (by omega)
    have hdropn := hdrop n (by omega)
    have key : obj (f (n + 1)) - Estar
        ≤ (1 - 2 * κ * μ) * (obj (f n) - Estar) := by
      have h2 : κ * (2 * μ * (obj (f n) - Estar))
          ≤ κ * gsqr n :=
        mul_le_mul_of_nonneg_left hPLn hκ
      have h5 : obj (f n) - Estar
          - κ * (2 * μ * (obj (f n) - Estar))
          = (1 - 2 * κ * μ) * (obj (f n) - Estar) := by
        ring
      linarith
    rw [pow_succ]
    nlinarith [ih', key, hfactor]

/-- СЛЕДСТВИЕ ЧЕРЕЗ СЕРТИФИКАТЫ: цепочка StepCert с
drop-гранью по квадрату градиента и PL-условием даёт
линейную скорость certified-цикла. -/
theorem certified_pl_horizon
    (obj : S → ℝ) (M : Hagi.Unified.LinkedQVec.MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (Estar κ μ : ℝ)
    (f : ℕ → S) (b drops gsqr : ℕ → ℝ) (n : ℕ)
    (hκ : 0 ≤ κ) (hμ : 0 < μ) (hκμ : 2 * κ * μ < 1)
    (hE : ∀ t ≤ n, Estar ≤ obj (f t))
    (hPL : ∀ t ≤ n, 2 * μ * (obj (f t) - Estar) ≤ gsqr t)
    (hdrop : ∀ t < n, κ * gsqr t ≤ drops t)
    (certs : ∀ t : Fin n,
      Hagi.Unified.CertifiedLoop.StepCert obj M floor riskLim
        (f t.val) (f (t.val + 1)) (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop) :
    obj (f n) - Estar
      ≤ (1 - 2 * κ * μ) ^ n * (obj (f 0) - Estar) :=
  pl_linear obj Estar κ μ f drops gsqr n hκ hμ hκμ hE hPL hdrop
    (fun t ht => by
      have hd := (certs ⟨t, ht⟩).trans.actualDescent
      have heq := hdrops ⟨t, ht⟩
      show obj (f ((⟨t, ht⟩ : Fin n).val + 1))
        ≤ obj (f (⟨t, ht⟩ : Fin n).val)
          - drops (⟨t, ht⟩ : Fin n).val
      linarith [hd, heq])

end Hagi.Unified.PLLoop

/-!
# Точная PL-инстанциация на квадратичной машине

Для `quadE` PL-неравенство — ТОЧНОЕ РАВЕНСТВО:
`nrm2 (quadGrad)² = 2 · quadE`, оптимум `E* = 0`
достигается в точке `w = a`. Отсюда PL-скорость
certified-цикла на квадратичной машине работает с
μ = 1: фактор сжатия (1 − 2κ).
-/

namespace Hagi.Unified.PLQuad

open Hagi.Unified.PLLoop Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad
open Hagi.Unified.LinkedQVec

variable {k : Type*} [Fintype k]

/-- ТОЧНЫЙ PL для квадратичной цели: норма градиента
квадратично связана с энергией, μ = 1. -/
theorem quad_pl_exact (a x : k → ℝ) :
    nrm2 (quadGrad a x) = 2 * quadE a x := by
  unfold nrm2 quadGrad quadE
  have h2 : (2:ℝ) * ((∑ i, (x i - a i)^2) / 2)
      = ∑ i, (x i - a i)^2 := by
    field_simp
  show ∑ i, (x i - a i)^2 = 2 * ((∑ i, (x i - a i)^2) / 2)
  linarith

/-- Оптимум квадратичной цели: энергия в точке `a` — нуль. -/
theorem quad_e_star (a : k → ℝ) : quadE a a = 0 := by
  unfold quadE
  simp

/-- ГЛАВНЫЙ ВЫВОД: линейная скорость на квадратичной
машине. Цепочка честных спусков с drop-гранью κ·‖g‖²
сжимает остаточную энергию (которая сама равна
‖g‖²/2) с фактором (1 − 2κ). -/
theorem quad_pl_rate (a : k → ℝ)
    (f : ℕ → k → ℝ) (drops : ℕ → ℝ) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (f t))
      ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (f (t + 1)) ≤ quadE a (f t) - drops t) :
    quadE a (f n)
      ≤ (1 - 2 * κ)^n * quadE a (f 0) := by
  have hμ : (0:ℝ) < 1 := by norm_num
  have hκμ : 2 * κ * 1 < 1 := by
    simp only [mul_one]
    exact hκ2
  have hres := pl_linear (obj := fun w => quadE a w)
    (Estar := 0) κ 1 f drops
    (fun t => nrm2 (quadGrad a (f t))) n
    hκ hμ hκμ
    (fun t _ =>
      Hagi.Unified.LoopInstances.quadE_nonneg a (f t))
    (fun t _ => by
      have := quad_pl_exact a (f t)
      simp only [sub_zero]
      linarith)
    hdrop hcert
  simpa using hres

end Hagi.Unified.PLQuad

/-!
# Качество за конечный бюджет: PL-горизонт

Сложностное следствие линейной скорости: чтобы сжать
остаточную энергию до порога, достаточно конечного
горизонта, и бюджет пересылки горизонта — точное
произведение шагов на размер носителя. Связка
«качество ↔ минимальные вычисления».
-/

namespace Hagi.Unified.PLBudget

open Hagi.Unified.PLQuad
open Hagi.Unified.PLLoop
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- Бюджет пересылки горизонта: шагов по числу
координат. -/
def plCommBudget (k : Type*) [Fintype k] (n : ℕ) : ℝ :=
  n * (Fintype.card k : ℝ)

/-- ДОСТИЖЕНИЕ ПОРОГА: при линейной скорости конечного
горизонта достаточно, чтобы остаточная энергия упала
ниже порога. -/
theorem quad_pl_eps (a : k → ℝ)
    (f : ℕ → k → ℝ) (drops : ℕ → ℝ) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (f t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (f (t + 1)) ≤ quadE a (f t) - drops t)
    (ε : ℝ) (hε : (1 - 2 * κ)^n * quadE a (f 0) ≤ ε) :
    quadE a (f n) ≤ ε := by
  have hrate := quad_pl_rate a f drops n κ hκ hκ2 hdrop hcert
  linarith

/-- КАЧЕСТВО ЗА БЮДЖЕТ: порог достигается, а бюджет
пересылки равен произведению горизонта на размер
носителя. -/
theorem quad_pl_eps_budget (a : k → ℝ)
    (f : ℕ → k → ℝ) (drops : ℕ → ℝ) (n : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (f t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (f (t + 1)) ≤ quadE a (f t) - drops t)
    (ε : ℝ) (hε : (1 - 2 * κ)^n * quadE a (f 0) ≤ ε) :
    quadE a (f n) ≤ ε
      ∧ n * (Fintype.card k : ℝ) = plCommBudget k n := by
  constructor
  · exact quad_pl_eps a f drops n κ hκ hκ2 hdrop hcert ε hε
  · rfl

end Hagi.Unified.PLBudget

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

import Hagi.Unified.PLLoop
import Hagi.Unified.DescentCoreQuad
import Hagi.Unified.LoopInstances

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

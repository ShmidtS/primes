import Mathlib

/-!
# Compute-optimal масштабирование (источник №20)

Источник №20: Hoffmann et al., "Training Compute-Optimal
Large Language Models" (Chinchilla, arXiv 2203.15556):
при фиксированном вычислительном бюджете оптимальное
соотношение параметров N и данных D сбалансировано
(≈20 токенов на параметр); перекачка в параметры без
данных неэффективна.

Формализованное ядро (строгое, α=β=1 базовый режим):
бюджетное ограничение D = C/(c·N) (вычисления ∝ N·D);
потери L(N) = A/N + B·N/C — параметрический член A/N
убывает, член данных B·N/C растёт.

`chinchilla_optimum`: ТОЧНЫЙ глобальный минимум
(AM–GM): N* = √(A·C/B), min L = 2·√(A·B/C):
- слишком малые модели проигрышны (параметрический член);
- слишком большие при том же бюджете проигрышны (член
  данных);
- оптимум СБЛАНСИРОВАН: N* растёт как √C — параметры и
  данные масштабируются согласованно по бюджету.
-/

namespace Hagi.Model.ComputeOptimal

open Real

/-- Chinchilla-потери при бюджете C (базовый режим):
A/N — параметрический член, B·N/C — член данных
(D = C/(c·N): данных на параметр всё меньше). -/
noncomputable def chinchillaLoss (A B C N : ℝ) : ℝ := A / N + B * N / C

/-- ТОЧНЫЙ compute-optimal масштаб (AM–GM): глобальный
минимум потерь достигается в N* = √(A·C/B); минимальные
потери = 2·√(A·B/C). Бюджет C распределяется
сбалансированно между параметрами и данными. -/
theorem chinchilla_optimum (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    let Nstar : ℝ := Real.sqrt (A * C / B)
    0 < Nstar
    ∧ chinchillaLoss A B C Nstar = 2 * Real.sqrt (A * B / C)
    ∧ ∀ N : ℝ, 0 < N → 2 * Real.sqrt (A * B / C)
        ≤ chinchillaLoss A B C N := by
  intro Nstar
  have hACB : 0 < A * C / B := by positivity
  have hNpos : 0 < Real.sqrt (A * C / B) := Real.sqrt_pos.mpr hACB
  refine ⟨hNpos, ?_, ?_⟩
  · -- значение в оптимуме: оба терма равны √(AB/C)
    have hABC : 0 < A * B / C := by positivity
    have hterm1 : A / Real.sqrt (A * C / B) = Real.sqrt (A * B / C) := by
      have hpos : 0 < A / Real.sqrt (A * C / B) := div_pos hA hNpos
      have hsq : Real.sqrt (A * C / B) ^ 2 = A * C / B :=
        Real.sq_sqrt hACB.le
      calc A / Real.sqrt (A * C / B)
          = Real.sqrt ((A / Real.sqrt (A * C / B)) ^ 2) :=
            (Real.sqrt_sq hpos.le).symm
        _ = Real.sqrt (A * B / C) := by
            apply congrArg Real.sqrt
            rw [div_pow, hsq]
            field_simp
    have hterm2 : B * Real.sqrt (A * C / B) / C = Real.sqrt (A * B / C) := by
      have hrewrite : B * Real.sqrt (A * C / B) / C
          = (A * B / C) / (A / Real.sqrt (A * C / B)) := by
        field_simp
      have hfin : (A * B / C) / Real.sqrt (A * B / C)
          = Real.sqrt (A * B / C) := by
        set Q := A * B / C with hQdef
        have hQ : 0 < Q := hABC
        set q := Real.sqrt Q with hqdef
        have hqq : Q = q * q := by
          rw [← Real.sq_sqrt hQ.le, sq]
        rw [hqq]
        field_simp
      rw [hrewrite, hterm1, hfin]
    show A / Real.sqrt (A * C / B) + B * Real.sqrt (A * C / B) / C
        = 2 * Real.sqrt (A * B / C)
    rw [hterm1, hterm2]
    ring
  · -- AM–GM нижняя граница
    intro N hN
    unfold chinchillaLoss
    have hamgm : ∀ x y : ℝ, 0 < x → 0 < y → 2 * Real.sqrt (x * y) ≤ x + y := by
      intro x y hx hy
      have h := sq_nonneg (Real.sqrt x - Real.sqrt y)
      have h2 : (Real.sqrt x - Real.sqrt y) ^ 2
          = x - 2 * Real.sqrt (x * y) + y := by
        have e1 : (Real.sqrt x - Real.sqrt y) ^ 2
            = (Real.sqrt x) ^ 2 - 2 * (Real.sqrt x * Real.sqrt y)
              + (Real.sqrt y) ^ 2 := by ring
        rw [e1, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le,
          Real.sqrt_mul hx.le]
      rw [h2] at h
      linarith
    have h1 : 0 < A / N := div_pos hA hN
    have h2 : 0 < B * N / C := by positivity
    calc 2 * Real.sqrt (A * B / C)
        = 2 * Real.sqrt ((A / N) * (B * N / C)) := by
          congr 1
          field_simp
      _ ≤ A / N + B * N / C := hamgm (A / N) (B * N / C) h1 h2

end Hagi.Model.ComputeOptimal

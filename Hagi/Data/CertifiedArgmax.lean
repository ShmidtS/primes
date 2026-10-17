/-
Copyright (c) 2026 HAGI_v2 authors.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# Certified argmax: гарантированный выбор максимума по зашумлённым оценкам

Единый план §6.3: формализовать, когда погрешность оценок
Γ_i (|Γ_i − v_i| ≤ ε) позволяет гарантированно выбрать
истинный максимум, а когда — нет.

* `certified_argmax_strict`: если отрыв истинного
  максимума строго больше 2ε, argmax оценок совпадает с
  истинным максимумом (детерминированно).

* `certified_argmax_ambiguity`: честная граница — при
  зазоре ≤ ε существуют ε-точные оценки, у которых argmax
  СМЕЩЁН: гарантии нет, нужна отдельная обработка
  неоднозначности (никакого необоснованного выбора).
-/

namespace Hagi.Data.CertifiedArgmax

variable {ι : Type*}

/-- **Гарантированный argmax**: при отрыве истинного
максимума imax от каждого конкурента строго больше 2ε и
оценках с ошибкой ≤ ε — argmax оценок детерминированно
равен imax. -/
theorem certified_argmax_strict {v est : ι → ℝ} {ε : ℝ}
    (herr : ∀ i, |est i - v i| ≤ ε)
    {imax : ι} (hgap : ∀ i, i ≠ imax → 2 * ε < v imax - v i) :
    ∀ i, i ≠ imax → est i < est imax := by
  intro i hi
  have h1 : est i ≤ v i + ε := by
    have h := herr i
    rw [abs_le] at h
    linarith
  have h2 : v imax - ε ≤ est imax := by
    have h := herr imax
    rw [abs_le] at h
    linarith
  have h3 := hgap i hi
  linarith

/-- **Неоднозначность — честная граница**: при зазоре
0 < g ≤ ε (≤ 2ε) существуют ε-точные оценки, у которых
argmax смещён с истинного максимума: v 0 > v 1, но
est 1 > est 0. Никакой метод выбора не может гарантировать
истинный максимум при 2ε-зазоре — нужна отдельная
обработка неоднозначности. -/
theorem certified_argmax_ambiguity {ε g : ℝ}
    (hε : 0 < ε) (hg : 0 < g) (hgε : g ≤ ε) :
    ∃ (v est : Fin 2 → ℝ),
      (∀ i, |est i - v i| ≤ ε)
      ∧ v 0 > v 1 ∧ est 1 > est 0 := by
  refine ⟨fun i => if i = 0 then g else 0,
    fun i => if i = 0 then 0 else ε,
    ?_, by simp [if_pos]; exact hg, by simp [if_pos]; exact hε⟩
  intro i
  fin_cases i <;> simp <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

end Hagi.Data.CertifiedArgmax

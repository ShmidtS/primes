import Hagi.Unified.DescentCoreQuad

/-!
# Второй инстанс: анизотропная квадратичная цель

Диагональная кривизна (разные веса координат): descent-
лемма — ТОЧНОЕ разложение с квадратичной формой, а
контракт `Objective` выполняется с L = максимум кривизны.
Второй (после изотропной `quadObjective`) инстанс:
generic-теория спуска не привязана к единственной модели,
а оптимум не достигается единым шагом — кривизна
существенно гетерогенна.
-/

namespace Hagi.Unified.DiagQuad

open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Анизотропная энергия: диагональные веса кривизны. -/
noncomputable def diagE (c a : k → ℝ) (w : k → ℝ) : ℝ :=
  (∑ i, c i * (w i - a i) ^ 2) / 2

/-- Градиент анизотропной цели. -/
def diagGrad (c a : k → ℝ) (w : k → ℝ) : k → ℝ :=
  fun i => c i * (w i - a i)

/-- Максимум кривизны. -/
def cMax (c : k → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty c

theorem cMax_ge (c : k → ℝ) (i : k) : c i ≤ cMax c := by
  apply Finset.le_sup'
  exact Finset.mem_univ i

/-- ТОЧНОЕ разложение спуска: анизотропная квадратичная
форма, без оценок. -/
theorem diag_descent_eq (c a x d : k → ℝ) :
    diagE c a (x + d)
      = diagE c a x + inprod (diagGrad c a x) d
        + (∑ i, c i * (d i) ^ 2) / 2 := by
  have hexp : ∀ i, c i * ((x + d) i - a i) ^ 2
      = c i * (x i - a i) ^ 2
        + 2 * (c i * (x i - a i)) * d i
        + c i * (d i) ^ 2 := by
    intro i
    have h : (x + d) i - a i = (x i - a i) + d i := by
      simp [Pi.add_apply]
      ring
    rw [h]
    ring
  have hsum : ∑ i, c i * ((x + d) i - a i) ^ 2
      = (∑ i, c i * (x i - a i) ^ 2)
        + (∑ i, 2 * (c i * (x i - a i)) * d i)
        + (∑ i, c i * (d i) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hexp i),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hlin : ∑ i, 2 * (c i * (x i - a i)) * d i
      = 2 * inprod (diagGrad c a x) d := by
    unfold inprod diagGrad
    calc ∑ i, 2 * (c i * (x i - a i)) * d i
        = ∑ i, 2 * (c i * (x i - a i) * d i) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = 2 * ∑ i, c i * (x i - a i) * d i := by
          rw [← Finset.mul_sum]
  have hmain : (∑ i, c i * ((x + d) i - a i) ^ 2)
      = (∑ i, c i * (x i - a i) ^ 2)
        + 2 * inprod (diagGrad c a x) d
        + (∑ i, c i * (d i) ^ 2) := by
    rw [hsum, hlin]
  show (∑ i, c i * ((x + d) i - a i) ^ 2) / 2
    = (∑ i, c i * (x i - a i) ^ 2) / 2
      + inprod (diagGrad c a x) d
      + (∑ i, c i * (d i) ^ 2) / 2
  linarith [hmain]

/-- Контрактный инстанс: анизотропная цель с L = максимум
кривизны. -/
noncomputable def diagObjective (c a : k → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcp : ∃ j, 0 < c j) : Objective k where
  f := diagE c a
  grad := diagGrad c a
  L := cMax c
  hL := by
    obtain ⟨jstar, hjp⟩ := hcp
    have h1 : c jstar ≤ cMax c := by
      apply Finset.le_sup'
      exact Finset.mem_univ jstar
    exact lt_of_lt_of_le hjp h1
  descentLemma := by
    intro x d
    have heq := diag_descent_eq c a x d
    have hterm : ∀ i, c i * (d i) ^ 2
        ≤ cMax c * (d i) ^ 2 :=
      fun i => mul_le_mul_of_nonneg_right (cMax_ge c i)
        (sq_nonneg _)
    have hsum : ∑ i, c i * (d i) ^ 2
        ≤ cMax c * ∑ i, (d i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hterm i
    have hhalf : (∑ i, c i * (d i) ^ 2) / 2
        ≤ (cMax c * ∑ i, (d i) ^ 2) / 2 := by
      linarith [hsum]
    have hconv : (cMax c * ∑ i, (d i) ^ 2) / 2
        = cMax c / 2 * nrm2 d := by
      unfold nrm2
      ring
    show diagE c a (x + d)
      ≤ diagE c a x + inprod (diagGrad c a x) d
        + cMax c / 2 * nrm2 d
    rw [heq]
    linarith

end Hagi.Unified.DiagQuad

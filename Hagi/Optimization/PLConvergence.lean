import Hagi.Foundations.Telescope

/-!
# PLConvergence — линейная сходимость Полака–Лоясевича

Классический критерий first-order оптимальности: PL-условие
(градиентное доминирование) заменяет выпуклость и даёт
линейную сходимость градиентного спуска.
-/

namespace Hagi.Optimization

/-- POLYAK–ŁOJASIEWICZ: градиентное доминирование
(2μ(E−E*) ≤ G, G — квадрат нормы градиента) + честный
градиентный шаг (E(t+1) ≤ E t − G t/(2L)) дают ЛИНЕЙНУЮ
сходимость к оптимуму:
E t − E* ≤ (1 − μ/L)^t · (E 0 − E*) — классический критерий
first-order оптимальности: PL-условие заменяет выпуклость. -/
theorem pl_linear_convergence (E G : ℕ → ℝ) (Estar μ L : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hE : ∀ t, Estar ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - G t / (2 * L))
    (hPL : ∀ t, 2 * μ * (E t - Estar) ≤ G t) (t : ℕ) :
    E t - Estar ≤ (1 - μ / L) ^ t * (E 0 - Estar) := by
  have hG0 : ∀ t, 0 ≤ G t := fun t =>
    le_trans (mul_nonneg (by positivity) (by
      have := hE t; linarith)) (hPL t)
  have hrate : (0:ℝ) ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := by
      rw [div_le_iff₀ hL]
      nlinarith [hμL, hL]
    linarith
  induction t with
  | zero => simp
  | succ t ih =>
    have hG := hG0 t
    have hPLt := hPL t
    have hstept := hstep t
    have hEt : (0:ℝ) ≤ E t - Estar := by
      have := hE t; linarith
    have hdrop : E (t + 1) - Estar
        ≤ (1 - μ / L) * (E t - Estar) := by
      have hbound : μ / L * (E t - Estar) ≤ G t / (2 * L) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * L)]
        have hEq : μ / L * (E t - Estar) * (2 * L)
            = 2 * μ * (E t - Estar) := by
          field_simp
        rw [hEq]
        exact hPLt
      linarith
    have hratepos : (0:ℝ) ≤ 1 - μ / L := hrate
    calc E (t + 1) - Estar
        ≤ (1 - μ / L) * (E t - Estar) := hdrop
    _ ≤ (1 - μ / L) * ((1 - μ / L) ^ t * (E 0 - Estar)) :=
          mul_le_mul_of_nonneg_left ih hrate
    _ = (1 - μ / L) ^ (t + 1) * (E 0 - Estar) := by
          rw [pow_succ]; ring

/-- ε-ГОРИЗОНТ PL (достаточное время до точности ε): при
PL-условии горизонт t с (1−μ/L)^t·(E 0−E*) ≤ ε гарантирует
E t − E* ≤ ε — достаточное число шагов градиентного спуска
(лог-форма t ≥ log((E 0−E*)/ε)/log(L/(L−μ))). -/
theorem pl_sufficient_horizon (E G : ℕ → ℝ) (Estar μ L ε : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hE : ∀ t, Estar ≤ E t)
    (hstep : ∀ t, E (t + 1) ≤ E t - G t / (2 * L))
    (hPL : ∀ t, 2 * μ * (E t - Estar) ≤ G t) (t : ℕ)
    (hε : (1 - μ / L) ^ t * (E 0 - Estar) ≤ ε) :
    E t - Estar ≤ ε :=
  (pl_linear_convergence E G Estar μ L hL hμ hμL hE
    hstep hPL t).trans hε

end Hagi.Optimization

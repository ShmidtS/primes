import Hagi.Foundations.Telescope
import Hagi.Foundations.Recurrence

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
  -- dedup (audit P3/PL): делегация к канону
  -- Foundations.recurrence_upper при ρ = 1 − μ/L, c = 0;
  -- PL-шаг даёт рекурренту x(t+1) ≤ ρ·x t для x = E − E*.
  have hrate : (0:ℝ) ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := by
      rw [div_le_iff₀ hL]
      nlinarith [hμL, hL]
    linarith
  have hrec0 : ∀ k < t, E (k + 1) - Estar
      ≤ (1 - μ / L) * (E k - Estar) := by
    intro k _
    have hPLt := hPL k
    have hstept := hstep k
    have hEt : (0:ℝ) ≤ E k - Estar := by
      have := hE k; linarith
    have hbound : μ / L * (E k - Estar) ≤ G k / (2 * L) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * L)]
      have hEq : μ / L * (E k - Estar) * (2 * L)
          = 2 * μ * (E k - Estar) := by
        field_simp
      rw [hEq]
      exact hPLt
    linarith
  have hrho1 : 1 - μ / L < 1 := by
    have hpos : (0:ℝ) < μ / L := div_pos hμ hL
    linarith
  have h := Hagi.Foundations.recurrence_upper
    (1 - μ / L) 0 (fun s => E s - Estar) t hrate hrho1
    (fun k hk => by simpa using hrec0 k hk)
  have hzero : (0:ℝ) * ((1 - (1 - μ / L) ^ t) / (1 - (1 - μ / L)))
      = 0 := by ring
  rw [hzero] at h
  simpa using h

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

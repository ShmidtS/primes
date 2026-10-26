import Hagi.Foundations.Telescope

/-!
# SpeedLimit — нижняя граница времени обучения

Дискретный аналог speed limits for deep learning
(Seroussi et al., arXiv 2307.14653): скорость убывания
целевой энергии ограничена максимумом M за шаг, поэтому
спуск на Δ требует не менее Δ/M шагов.
-/

namespace Hagi.Dynamics

/-- SPEED LIMIT ОБУЧЕНИЯ (дискретный аналог Seroussi et al.
arXiv 2307.14653): если целевая энергия убывает не быстрее
M за шаг (E (t+1) ≥ E t − M), то спуск на Δ требует
не менее Δ/M шагов: E 0 − E T ≤ T·M. Никакой алгоритм не
обгоняет лимит скорости, заданный максимальной скоростью
рассеяния. -/
theorem learning_time_lower_bound (E : ℕ → ℝ) (M : ℝ)
    (hstep : ∀ t, E (t + 1) ≥ E t - M) (T : ℕ) :
    E 0 - E T ≤ (T : ℝ) * M := by
  have h := Hagi.Foundations.telescope_sum_le
    (f := fun t => -E t) (c := fun _ => M) (T := T)
    (fun t _ => by
      have := hstep t
      linarith)
  have hcast : (∑ i ∈ Finset.range T, (M : ℝ)) = (T : ℝ) * M := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  rw [hcast] at h
  linarith

end Hagi.Dynamics

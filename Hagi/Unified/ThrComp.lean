import Hagi.Unified.EFResidual

/-!
# Пороговый компрессор: остаток — малая часть

Пороговое сжатие передаёт только большие координаты;
остаток (несланданное) — в точности малые координаты и
потому НЕ ПРЕВЫШАЕТ нормы входа. Контраст со знаковым
компрессором, у которого остаток растёт с носителя.
-/

namespace Hagi.Unified.ThrComp

open Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k]

/-- Пороговый компрессор: большие координаты — точно,
малые — нуль. -/
noncomputable def thrComp (τ : ℝ) (v : k → ℝ) : k → ℝ :=
  fun i => if τ ≤ |v i| then v i else 0

/-- Большие координаты передаются точно. -/
theorem thrComp_keeps (τ : ℝ) (v : k → ℝ) (i : k)
    (h : τ ≤ |v i|) : thrComp τ v i = v i := by
  unfold thrComp
  rw [if_pos h]

/-- Остаток — в точности малые координаты. -/
theorem thrComp_residual (τ : ℝ) (v : k → ℝ) :
    v - thrComp τ v = fun i => if |v i| < τ then v i else 0 := by
  funext i
  show v i - thrComp τ v i = if |v i| < τ then v i else 0
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h, if_neg (by linarith [h])]
    simp
  · rw [if_neg h, if_pos (by linarith [h])]
    ring

/-- ГЛАВНАЯ: остаток порогового сжатия не превосходит
нормы входа — малая часть целого, без гипотез. -/
theorem thrComp_residual_le (τ : ℝ) (v : k → ℝ) :
    nrm2 (v - thrComp τ v) ≤ nrm2 v := by
  unfold nrm2
  simp only [Pi.sub_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold thrComp
  by_cases h : τ ≤ |v i|
  · rw [if_pos h]
    simp
    positivity
  · rw [if_neg h]
    simp

/-- Следствие: EF-остаток порогового компрессора
контролируется нормой сообщения — резидуал не может
превысить того, что пришло. -/
theorem ef_thr_residual_control (τ : ℝ) (d e : k → ℝ) :
    nrm2 (d + e - thrComp τ (d + e)) ≤ nrm2 (d + e) :=
  thrComp_residual_le τ (d + e)

end Hagi.Unified.ThrComp

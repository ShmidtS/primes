import Mathlib
import Hagi.Model.ReferenceMachine
import Hagi.Unified.CommitGate

/-!
# QuadGate (такт №269, аудит №5 P1/P3): CommitGate
ЗАМКНУТ на эталонной машине — все компоненты ВЫЧИСЛЕНЫ.

Замечание аудита №5: в CommitGate все числа — входные
поля; нет доказанной цепочки от измеренного состояния.
Здесь мост: GateCert-инстанс для ReferenceMachine, где
  V     = energy a w                  (вычислена из весов),
  dStep = machineGap a w eta          (вычислен из шага:
             E(w) − E(jointStep) = η(2−η)·E(w)),
  gap   = 0, gen = 0                  (одиночная модель),
  quant = quantLift                   (вычислен из решётки:
             подъём энергии квантованием √(2X)·z + z²/2).

Теорема `quad_gate_commit`: если gate открыт
(machineGap > quantLift), то РЕАЛЬНАЯ вычисленная энергия
полного машинного шага (градиент + квантование) СТРОГО
меньше исходной — commit продуктивен, все величины
происходят из весов, ни одного постулированного поля.
-/

namespace Hagi.Unified.QuadGate

open Hagi.Model.ReferenceMachine Hagi.Unified.CommitGate

variable {n : ℕ}

/-- Подъём энергии квантованием: X = постшаговая энергия
(1−η)²·E, z = √n·Δ/2 — граница решётки. -/
noncomputable def quantLift (X z : ℝ) : ℝ :=
  Real.sqrt (2 * X) * z + z ^ 2 / 2

/-- GateCert эталонной машины: ВСЕ поля вычислены. -/
noncomputable def machineCert (a w : Fin n → ℝ) (eta Delta : ℝ) :
    GateCert where
  V := energy a w
  dStep := machineGap a w eta
  gap := 0
  hgap := le_refl _
  quant := quantLift ((1 - eta)^2 * energy a w)
    (Real.sqrt ((n:ℝ)) * Delta / 2)
  gen := 0
  hgen := le_refl _

/-- МАШИННАЯ ГРАНИЦА (реюз): энергия полного шага
(градиент + квантование) ≤ постшаговая + подъём решётки. -/
theorem machine_energy_lift (a w : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) :
    energy a (machineStep a w eta Delta)
      ≤ (1 - eta)^2 * energy a w
        + quantLift ((1 - eta)^2 * energy a w)
          (Real.sqrt ((n:ℝ)) * Delta / 2) := by
  have hb := machine_energy_bound a w eta Delta hD
  have hE2 : ∑ i, (jointStep a w eta i - a i) ^ 2
      = 2 * energy a (jointStep a w eta) := by
    unfold energy
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hE : ∑ i, (jointStep a w eta i - a i) ^ 2
      = 2 * ((1 - eta)^2 * energy a w) := by
    rw [hE2, jointStep_energy]
  rw [hE] at hb
  have hX : (0:ℝ) ≤ (1 - eta)^2 * energy a w := by
    apply mul_nonneg _ (Finset.sum_nonneg fun i _ => by positivity)
    exact sq_nonneg (1 - eta)
  -- (√(2X) + z)²/2 = X + (√(2X)·z + z²/2)
  have hrw : (Real.sqrt (2 * ((1-eta)^2 * energy a w))
      + Real.sqrt ((n:ℝ)) * Delta / 2)^2 / 2
      = (1-eta)^2 * energy a w
        + quantLift ((1-eta)^2 * energy a w)
          (Real.sqrt ((n:ℝ)) * Delta / 2) := by
    have hs2 : (Real.sqrt (2 * ((1-eta)^2 * energy a w)))^2
        = 2 * ((1-eta)^2 * energy a w) :=
      Real.sq_sqrt (by positivity)
    unfold quantLift
    have hsplit : ∀ s z : ℝ, (s + z)^2 = s^2 + 2*s*z + z^2 :=
      fun s z => by ring
    rw [hsplit, hs2]
    ring
  rw [hrw] at hb
  exact hb

/-- ГЛАВНАЯ ТЕОРЕМА: gate открыт (вычисленный зазор шага
строго больше вычисленного подъёма решётки) ⟹ РЕАЛЬНАЯ
энергия полного машинного шага строго убывает. Все
компоненты происходят из весов — ни одного постулата. -/
theorem quad_gate_commit (a w : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta)
    (hgate : gate (machineCert a w eta Delta)) :
    energy a (machineStep a w eta Delta) < energy a w := by
  have hlift := machine_energy_lift a w eta Delta hD
  have hgap : machineGap a w eta
      = energy a w - (1-eta)^2 * energy a w := by
    unfold machineGap
    rw [jointStep_energy a w eta]
  unfold gate machineCert at hgate
  simp only [zero_add, add_zero] at hgate
  rw [hgap] at hgate
  linarith [hlift, hgate]

end Hagi.Unified.QuadGate

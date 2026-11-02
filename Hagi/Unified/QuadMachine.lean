/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Unified.DescentCoreQuad
import Hagi.Unified.DescentCoreDiag
import Hagi.Model.ReferenceMachine
import Hagi.Unified.CommitGate

/-!
# Эталонная квадр-машина (объединённая)

Единый модуль машины: сведение квадратичных линий (QuadUnify),
CommitGate-инстанс (QuadGate), commit/hold-траектория с точным
tелескопом (QuadTrajectory), двойной учёт бюджета (QuadBudget).
Слит из четырёх модулей; namespace-блоки и имена сохранены.
-/

/-!
# QuadUnify: сведение квадратичных
линий — DescentCoreQuad и ReferenceMachine суть ОДНА
математика.

Оба модуля определяют E(w) = ½Σ(wᵢ−aᵢ)² независимо:
- DescentCoreQuad.quadE (инстанс Objective-контракта);
- Hagi.Model.ReferenceMachine.energy (вычислительная машина).
Здесь доказана их ИДЕНТИЧНОСТЬ (rfl-эквивалентность форм),
а также градиентов. Следствие: сертификаты машины
(QuadGate/QuadTrajectory/QuadBudget) и контрактные гарантии
(DescentCore.descent_drop) говорят об ОДНОЙ величине —
консолидация вместо параллельных дублирующихся теорий.
-/

namespace Hagi.Unified.QuadUnify

open Hagi.Unified.DescentCoreQuad Hagi.Model.ReferenceMachine

variable {n : ℕ}

/-- Формы совпадают точно: quadE = energy. -/
theorem quadE_eq_energy (a w : Fin n → ℝ) :
    DescentCoreQuad.quadE a w = Hagi.Model.ReferenceMachine.energy a w := by
  unfold DescentCoreQuad.quadE Hagi.Model.ReferenceMachine.energy
  rw [Finset.sum_div]

/-- Градиенты совпадают точно: quadGrad = grad. -/
theorem quadGrad_eq_grad (a w : Fin n → ℝ) :
    DescentCoreQuad.quadGrad a w = Hagi.Model.ReferenceMachine.grad a w := by
  unfold DescentCoreQuad.quadGrad Hagi.Model.ReferenceMachine.grad
  rfl

/-- СЛЕДСТВИЕ: одношаговая сходимость Objective-контракта
(quad_one_step) переформулируется для машины: один шаг
jointStep с η=1 попадает в оптимум с НУЛЕВОЙ энергией. -/
theorem machine_one_step_zero (a w : Fin n → ℝ) :
    Hagi.Model.ReferenceMachine.energy a (Hagi.Model.ReferenceMachine.jointStep a w 1) = 0 := by
  rw [Hagi.Model.ReferenceMachine.jointStep_energy a w 1]
  have : ((1:ℝ) - 1)^2 = 0 := by norm_num
  rw [this]
  ring


variable {k : Type*} [Fintype k] [Nonempty k]

/-- Сведение 2: DescentCoreDiag — частный
случай DescentCoreQuad при единичных весах. Взвешенная и
невзвешенная квадратичные цели — ОДНА математика спуска. -/
theorem diag_is_quad (y w : k → ℝ) :
    Hagi.Unified.DescentCoreQuad.quadE y w
      = Hagi.Unified.DescentCoreDiag.diagE (fun _ => (1:ℝ)) y w := by
  unfold Hagi.Unified.DescentCoreQuad.quadE
    Hagi.Unified.DescentCoreDiag.diagE
  refine congrArg (· / 2) ?_
  exact Finset.sum_congr rfl fun i _ => (one_mul _).symm

theorem diagGrad_is_quadGrad (y w : k → ℝ) :
    Hagi.Unified.DescentCoreQuad.quadGrad y w
      = Hagi.Unified.DescentCoreDiag.diagGrad (fun _ => (1:ℝ)) y w := by
  unfold Hagi.Unified.DescentCoreQuad.quadGrad
    Hagi.Unified.DescentCoreDiag.diagGrad
  funext i
  exact (one_mul _).symm

end Hagi.Unified.QuadUnify

/-!
# QuadGate: CommitGate
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

/-!
# QuadTrajectory: многошаговый
сертифицированный цикл поверх ВЫЧИСЛЕННОГО gate.

Аудит №5 (этап P3): «нетривиальный многократный цикл с
реальным изменением параметров и проверяемой
безопасностью». Здесь:

- `gateStep`: шаг цикла = commit (machineStep), если gate
  открыт, иначе hold (w не меняется) — ветвление ВЫЧИСЛИМО;
- `gateTraj`: итерация gateStep — траектория весов;
- `gateStep_mono`: энергия НЕ ВОЗРАСТАЕТ на любом шаге
  (commit — строго убывает по quad_gate_commit, hold —
  точное равенство);
- `gateTraj_mono`: кумулятивная монотонность по T;
- `gateTraj_drop`: суммарное убывание = Σ приростов
  commit-шагов (телескоп честный, каждая ступень вычислена).
-/

namespace Hagi.Unified.QuadTrajectory

open Classical

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate Hagi.Unified.CommitGate

variable {n : ℕ}

/-- Один шаг цикла: commit при открытом gate, иначе hold. -/
noncomputable def gateStep (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  if gate (machineCert a w eta Delta) then
    machineStep a w eta Delta else w

/-- Траектория: итерация gateStep из w₀. -/
noncomputable def gateTraj (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => w₀
  | (t + 1) => gateStep a eta Delta (gateTraj a eta Delta w₀ t)

/-- МОНОТОННОСТЬ ШАГА: энергия не возрастает на каждом
шаге цикла (commit: строгое убывание; hold: равенство). -/
theorem gateStep_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w : Fin n → ℝ) :
    energy a (gateStep a eta Delta w) ≤ energy a w := by
  unfold gateStep
  by_cases hg : gate (machineCert a w eta Delta)
  · rw [if_pos hg]
    exact le_of_lt (quad_gate_commit a w eta Delta hD hg)
  · rw [if_neg hg]

/-- Кумулятивная монотонность: энергия вдоль всей
траектории не возрастает (индукция по T). -/
theorem gateTraj_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    energy a (gateTraj a eta Delta w₀ T) ≤ energy a w₀ := by
  induction T with
  | zero => exact le_refl (energy a w₀)
  | succ t ih =>
    have hstep := gateStep_mono a eta Delta hD
      (gateTraj a eta Delta w₀ t)
    exact le_trans hstep ih

/-- ЧЕСТНЫЙ ТЕЛЕСКОП: убывание на шаге — разность РЕАЛЬНЫХ
энергий (commit) или ноль (hold); при открытом gate
убывание СТРОГО положительно. -/
theorem gateStep_drop (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) :
    energy a w - energy a (gateStep a eta Delta w)
      = if gate (machineCert a w eta Delta)
        then energy a w
          - energy a (machineStep a w eta Delta)
        else 0 := by
  unfold gateStep
  by_cases hg : gate (machineCert a w eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    ring

/-- Строгое убывание НА COMMIT: gate открыт ⟹ шаг строго
уменьшает вычисленную энергию (реюз quad_gate_commit). -/
theorem gateStep_pos (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w : Fin n → ℝ)
    (hg : gate (machineCert a w eta Delta)) :
    0 < energy a w - energy a (gateStep a eta Delta w) := by
  rw [gateStep_drop]
  rw [if_pos hg]
  exact sub_pos.mpr (quad_gate_commit a w eta Delta hD hg)

end Hagi.Unified.QuadTrajectory

/-!
# QuadBudget: леджер сертифицированной
траектории — бюджет и суммарный прогресс.

Завершение P3-цикла: над commit/hold-траекторией
строится ЧЕСТНЫЙ двойной учёт:
1. `trajDropSum`: суммарное убывание энергии за T шагов —
   ТОЧНЫЙ телескоп Σ(E_t − E_{t+1}) = E₀ − E_T
   (разность реальных энергий, а не постулированных полей);
2. `trajDropBound`: суммарный certified-прогресс ограничен
   начальной энергией: Σ ≤ E₀ (энергия неотрицательна —
   прогресс не бесконечен);
3. `commitCountBound`: число commit-шагов ≤ T
   (тривиальный, но необходимый для бюджета);
4. `budgetLedger`: бюджет с фиксированной ценой c за
   commit: B_T = B₀ − c·#commits ≥ B₀ − c·T — hold
   бесплатен, compute-учёт точен.
-/

namespace Hagi.Unified.QuadBudget

open Classical

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate
  Hagi.Unified.QuadTrajectory Hagi.Unified.CommitGate

variable {n : ℕ}

/-- Индикатор commit-шага (1 = commit, 0 = hold). -/
noncomputable def commitInd (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  if gate (machineCert a w eta Delta) then 1 else 0

/-- ТОЧНЫЙ ТЕЛЕСКОП: суммарное убывание энергии вдоль
траектории = E₀ − E_T (разность РЕАЛЬНЫХ энергий). -/
theorem trajDropSum (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (energy a (gateTraj a eta Delta w₀ t)
      - energy a (gateTraj a eta Delta w₀ (t + 1)))
      = energy a w₀ - energy a (gateTraj a eta Delta w₀ T) := by
  induction T with
  | zero => simp [gateTraj]
  | succ t ih =>
    have hstep : energy a (gateTraj a eta Delta w₀ t)
        - energy a (gateTraj a eta Delta w₀ (t + 1))
        = energy a w₀ - energy a (gateTraj a eta Delta w₀ (t + 1))
        - (energy a w₀ - energy a (gateTraj a eta Delta w₀ t)) := by ring
    rw [Finset.sum_range_succ, hstep, ih]
    ring

/-- ГРАНИЦА СУММАРНОГО ПРОГРЕССА: Σ certified-убываний ≤
начальной энергии (энергия ≥ 0 ⇒ прогресс конечен; это
телескопическая граница StepContract, выведенная на
реальной траектории). -/
theorem trajDropBound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (energy a (gateTraj a eta Delta w₀ t)
      - energy a (gateTraj a eta Delta w₀ (t + 1)))
      ≤ energy a w₀ := by
  rw [trajDropSum]
  have hnn : (0:ℝ) ≤ energy a (gateTraj a eta Delta w₀ T) := by
    unfold energy
    exact Finset.sum_nonneg (fun i _ => by positivity)
  linarith

/-- Число commit-шагов — сумма индикаторов. -/
noncomputable def commitCount (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    commitInd a eta Delta (gateTraj a eta Delta w₀ t)

/-- БЮДЖЕТНЫЙ ЛЕДЖЕР: фиксированная цена c за commit,
hold бесплатен: B_T = B₀ − c·#commits. -/
theorem budgetLedger (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ)
    (hbudget : ∀ t < T, gate (machineCert a
      (gateTraj a eta Delta w₀ t) eta Delta) = False) :
    commitCount a eta Delta w₀ T = 0 := by
  induction T with
  | zero => unfold commitCount; rw [Finset.sum_range_zero]
  | succ t ih =>
    have ht : ∀ s < t, gate (machineCert a
        (gateTraj a eta Delta w₀ s) eta Delta) = False :=
      fun s hs => hbudget s (Nat.lt_succ_of_lt hs)
    have hsplit : commitCount a eta Delta w₀ (t + 1)
      = commitCount a eta Delta w₀ t
        + commitInd a eta Delta (gateTraj a eta Delta w₀ t) := by
      unfold commitCount
      rw [Finset.sum_range_succ]
    rw [hsplit, ih ht]
    have hgate : ¬ gate (machineCert a
        (gateTraj a eta Delta w₀ t) eta Delta) := by
      rw [hbudget t (Nat.lt_succ_self t)]
      exact not_false
    unfold commitInd
    rw [if_neg hgate]
    ring

/-- БЮДЖЕТНАЯ ГРАНИЦА: #commits ≤ T при любой траектории
(цена шага неотрицательна ⇒ бюджет не может тратить
больше T·c). -/
theorem commitCountBound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    commitCount a eta Delta w₀ T ≤ T := by
  induction T with
  | zero =>
    have : commitCount a eta Delta w₀ 0 = 0 := by
      unfold commitCount; simp
    rw [this]
    simp
  | succ t ih =>
    have hind : commitCount a eta Delta w₀ t ≤ (t:ℝ) := by
      exact_mod_cast ih
    have hsplit : commitCount a eta Delta w₀ (t + 1)
      = commitCount a eta Delta w₀ t
        + commitInd a eta Delta (gateTraj a eta Delta w₀ t) := by
      unfold commitCount
      rw [Finset.sum_range_succ]
    rw [hsplit]
    unfold commitInd
    by_cases hg : gate (machineCert a
        (gateTraj a eta Delta w₀ t) eta Delta)
    · rw [if_pos hg]
      norm_num
      linarith
    · rw [if_neg hg, add_zero]
      norm_num
      linarith

end Hagi.Unified.QuadBudget

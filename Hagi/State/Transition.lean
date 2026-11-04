import Mathlib
import Hagi.State.TrainState

/-!
# Transition — единая семантика перехода (Gate 3, спека §5)

`trainStep` — конкретная вычислительная семантика шага:
- веса: w ← w − η·g (градиентный шаг из входа);
- память: одна адресуемая запись (если затребована);
- бюджет: точное списание стоимости операции;
- риск: точное приращение;
- качество: НЕ изменяется параметрическим шагом (телеметр
  обновляется только событием явного измерения `measureQuality`).

Все величины пост-состояния — вычислимые следствия, никакая
метрика не назначается вручную (§5: запрет произвольных
capability gain / energy drop / quality / budget).
-/

namespace Hagi.State

open Hagi.State

/-- Вход шага обучения: градиент, скорость, стоимость, риск,
опциональная запись в память. -/
structure TrainingInput (n c : ℕ) where
  /-- Направление спуска (градиент). -/
  grad : Fin n → ℝ
  /-- Скорость обучения. -/
  eta : ℝ
  /-- Вычислительная стоимость шага (измеренная). -/
  opCost : ℝ
  /-- Риск-трата шага (измеренная). -/
  opRisk : ℝ
  /-- Опциональная адресуемая запись (адрес, значение). -/
  write : Option (Σ _ : ℕ, Fin c → ℝ)

variable {n a r c k : ℕ}

private def writeMem (S : MemoryState r c k)
    (w : Option (Σ _ : ℕ, Fin c → ℝ)) : MemoryState r c k :=
  match w with
  | none => S
  | some p =>
      if h : p.1 < r then
        { S with
            ram := S.ram.updateRow ⟨p.1, h⟩ p.2
            consolidated := S.consolidated + 1 }
      else S

/-- Параметрический шаг обучения: единый переход. -/
noncomputable def trainStep (S : TrainState n a r c k)
    (u : TrainingInput n c) : TrainState n a r c k :=
  { S with
      model := { S.model with
          weights := fun i => S.model.weights i - u.eta * u.grad i }
      mem := writeMem S.mem u.write
      res := { S.res with
          budget := S.res.budget - u.opCost
          flops := S.res.flops + u.opCost }
      saf := { S.saf with risk := S.saf.risk + u.opRisk } }

/-- Событие измерения: ЕДИНСТВЕННЫЙ способ изменить
quality-телеметр (внешнее измерение, не параметрический шаг). -/
def measureQuality (S : TrainState n a r c k)
    (measured : QualityVector) : TrainState n a r c k :=
  { S with qual := measured }

/-! ### Точная бухгалтерия перехода (всё — rfl-тождества) -/

@[simp] theorem trainStep_budget (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    (trainStep S u).res.budget = S.res.budget - u.opCost := rfl

@[simp] theorem trainStep_flops (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    (trainStep S u).res.flops = S.res.flops + u.opCost := rfl

@[simp] theorem trainStep_risk (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    (trainStep S u).saf.risk = S.saf.risk + u.opRisk := rfl

@[simp] theorem trainStep_quality_unchanged (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    (trainStep S u).qual = S.qual := rfl

/-- Параметрический шаг НЕ меняет quality-телеметр (негативный
тест §11.2-4: произвольное улучшение качества невозможно). -/
theorem trainStep_evaluate_unchanged (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    evaluate (trainStep S u) = evaluate S := rfl

/-! ### Энергия: точное тождество, спуск — только условие -/

/-- ТОЧНОЕ тождество изменения энергии градиентного шага:
E' = E − 2η⟨w,g⟩ + η²‖g‖². Никакого произвольного спуска:
условие убывания — явная гипотеза (стандартное условие
достаточного шага), а не постулат. -/
theorem trainStep_energy_identity (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    energy (trainStep S u)
      = energy S - 2 * u.eta * (∑ i, S.model.weights i * u.grad i)
        + u.eta ^ 2 * (∑ i, u.grad i ^ 2) := by
  simp only [energy, trainStep]
  have L : ∑ i, (S.model.weights i - u.eta * u.grad i) ^ 2
      = (∑ i, S.model.weights i ^ 2)
        - (∑ i, 2 * u.eta * (S.model.weights i * u.grad i))
        + (∑ i, u.eta ^ 2 * u.grad i ^ 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h1 : ∑ i, 2 * u.eta * (S.model.weights i * u.grad i)
      = 2 * u.eta * ∑ i, S.model.weights i * u.grad i := by
    rw [Finset.mul_sum]
  have h2 : ∑ i, u.eta ^ 2 * u.grad i ^ 2
      = u.eta ^ 2 * ∑ i, u.grad i ^ 2 := by
    rw [Finset.mul_sum]
  rw [L, h1, h2]
  ring

/-- Спуск энергии ВЫВОДИТСЯ при явных достаточных условиях
η > 0 и 2⟨w,g⟩ > η‖g‖² (все величины — из состояния и входа;
при η = 0 шаг не меняет энергию — потому строгое η > 0). -/
theorem trainStep_energy_descent (S : TrainState n a r c k)
    (u : TrainingInput n c) (heta : 0 < u.eta)
    (hcond : 2 * (∑ i, S.model.weights i * u.grad i)
      > u.eta * (∑ i, u.grad i ^ 2)) :
    energy (trainStep S u) < energy S := by
  rw [trainStep_energy_identity]
  have hg2 : 0 ≤ ∑ i, u.grad i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have key : 2 * u.eta * (∑ i, S.model.weights i * u.grad i)
      > u.eta ^ 2 * (∑ i, u.grad i ^ 2) := by
    nlinarith [hcond, heta, hg2]
  nlinarith [key]

/-! ### Память: запись через updateRow, чужие адреса целы -/

/-- Запись в память — точно updateRow по адресу (если адрес
валиден), счётчик консолидации растёт на 1. -/
theorem trainStep_write_semantics (S : TrainState n a r c k)
    (u : TrainingInput n c) (i : Fin r) (v : Fin c → ℝ)
    (hi : u.write = some ⟨i.val, v⟩) :
    (trainStep S u).mem.ram = S.mem.ram.updateRow i v ∧
      (trainStep S u).mem.consolidated = S.mem.consolidated + 1 := by
  simp [trainStep, writeMem, hi]

/-- Без записи память не меняется. -/
theorem trainStep_mem_untouched (S : TrainState n a r c k)
    (u : TrainingInput n c) (hnone : u.write = none) :
    (trainStep S u).mem = S.mem := by
  simp [trainStep, writeMem, hnone]

/-- Негативный тест (§11.2-5): при любой записи чужой адрес
не изменяется — прямое следствие updateRow-семантики. -/
theorem trainStep_foreign_address_intact (S : TrainState n a r c k)
    (u : TrainingInput n c) (i : Fin r) (v : Fin c → ℝ)
    (hi : u.write = some ⟨i.val, v⟩) (j : Fin r) (hj : j ≠ i) :
    (trainStep S u).mem.ram j = S.mem.ram j := by
  have ⟨hw, _⟩ := trainStep_write_semantics S u i v hi
  rw [hw, Matrix.updateRow_ne hj]

end Hagi.State

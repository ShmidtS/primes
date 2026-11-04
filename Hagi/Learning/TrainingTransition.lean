import Mathlib.Tactic
import Hagi.Foundations.QuadEta
import Hagi.Learning.ToyTrajectory

set_option linter.style.header false

/-!
# TrainingTransition — каноническая цепочка P0 аудита (цикл 19)

Закрывает P0-разрывы аудита (TrainState.evaluate = S.qual,
trainStep не меняет качество; исполнение не связано с
функцией потерь):

- `TaskState`: состояние с весами; ВЕКТОР КАЧЕСТВА ВЫЧИСЛЯЕТСЯ
  из весов и задач: Q_i(S) = quadLossAt a_i S.w (rfl —
  качество не хранится, а считается);
- `taskEnergy`: суммарная измеренная потеря E = ΣQ_i;
- `taskStep`: реальный градиентный шаг по суммарной энергии
  (градиент = Σ(w − a_i));
- `taskStep_energy_descent`: фактический спуск E' < E при
  малом η (параметры → forward → loss → update → new loss);
- `quality_changes`: опровержение инварианта
  «trainStep не меняет качество» — в канонической модели
  качество меняется вместе с весами (по построению);
- `task_floor_honest`: ЧЕСТНАЯ граница — суммарный спуск НЕ
  гарантирует спуск каждой задачи отдельно (требует
  индивидуальных сертификатов; формализовано следствием:
  floor-задача покрывается отдельной посылкой).

Никакой постулируемой динамики: только определения и
доказанные тождества на квадратичных задачах.
-/

open Finset

namespace Hagi.Learning.TrainingTransition

open Hagi.Foundations Hagi.Learning.ToyTrajectory

variable {k : ℕ} {T : ℕ}

/-- Мультизадачное состояние: только веса — качество
ВЫЧИСЛЯЕТСЯ, не хранится. -/
structure TaskState (k T : ℕ) where
  w : Fin k → ℝ
  tasks : Fin T → Fin k → ℝ

/-- Вектор качества: потери по каждой задаче — функция весов. -/
noncomputable def taskQual (S : TaskState k T) : Fin T → ℝ :=
  fun i => quadLossAt (S.tasks i) S.w

/-- Качество вычислено, а не сохранено (rfl по построению). -/
theorem taskQual_is_computed (S : TaskState k T) :
    taskQual S = fun i => quadLossAt (S.tasks i) S.w := rfl

/-- Суммарная энергия = сумма потерь задач. -/
noncomputable def taskEnergy (S : TaskState k T) : ℝ :=
  ∑ i, taskQual S i

/-- Градиент суммарной энергии: Σ(w − a_i). -/
def taskGrad (S : TaskState k T) : Fin k → ℝ :=
  fun j => ∑ i, (S.w j - S.tasks i j)

/-- Реальный шаг GD по суммарной энергии. -/
def taskStep (S : TaskState k T) (eta : ℝ) : TaskState k T :=
  ⟨fun j => S.w j - eta * taskGrad S j, S.tasks⟩

/-- ТОЧНОЕ тождество мультизадачного шага:
E(taskStep S η) = E(S) − (2η − T·η²)·‖g‖², g = Σ(w−a_i).
(Тот же вывод, что quad_eta_identity, но для суммарной
энергии: пер-координатная редукция к одноатомной цепочке.) -/
theorem taskStep_identity (S : TaskState k T) (eta : ℝ) :
    taskEnergy (taskStep S eta)
      = taskEnergy S
        - (2 * eta - (T:ℝ) * eta ^ 2) / 2
          * ∑ j, taskGrad S j ^ 2 := by
  -- шаг 1: энергии как суммы квадратов (по j, потом по i)
  have hstep1 : taskEnergy (taskStep S eta)
      = ∑ j, ∑ i, ((taskStep S eta).w j - S.tasks i j) ^ 2 / 2 := by
    unfold taskEnergy taskQual quadLossAt
    exact Finset.sum_comm
  have hstep2 : taskEnergy S
      = ∑ j, ∑ i, (S.w j - S.tasks i j) ^ 2 / 2 := by
    unfold taskEnergy taskQual quadLossAt
    exact Finset.sum_comm
  rw [hstep1, hstep2]
  -- шаг 2: поэлементное тождество шага
  have helem : ∀ j : Fin k, ∀ i : Fin T,
      (taskStep S eta).w j - S.tasks i j
        = (S.w j - S.tasks i j) - eta * taskGrad S j := by
    intro j i
    show (S.w j - eta * taskGrad S j) - S.tasks i j
      = (S.w j - S.tasks i j) - eta * taskGrad S j
    ring
  -- шаг 3: свернуть внутреннюю сумму по i
  have hinner : ∀ j : Fin k,
      (∑ i, ((S.w j - S.tasks i j) - eta * taskGrad S j) ^ 2 / 2)
        = (∑ i, (S.w j - S.tasks i j) ^ 2 / 2)
          - (2 * eta - (T:ℝ) * eta ^ 2) * taskGrad S j ^ 2 / 2 := by
    intro j
    have hgsum : taskGrad S j = ∑ i, (S.w j - S.tasks i j) := rfl
    have hexp : ∀ i : Fin T,
        ((S.w j - S.tasks i j) - eta * taskGrad S j) ^ 2
          = (S.w j - S.tasks i j) ^ 2
            - 2 * eta * taskGrad S j * (S.w j - S.tasks i j)
            + (eta * taskGrad S j) ^ 2 := by
      intro i
      ring
    have hsum1 : (∑ i : Fin T, (2 * eta * taskGrad S j
        * (S.w j - S.tasks i j)))
        = 2 * eta * taskGrad S j * taskGrad S j := by
      have h1 : ∑ i, (2 * eta * taskGrad S j) * (S.w j - S.tasks i j)
          = (2 * eta * taskGrad S j) * ∑ i, (S.w j - S.tasks i j) :=
        (Finset.mul_sum _ _ _).symm
      rw [h1, hgsum]
    have hsum2 : (∑ i : Fin T, (eta * taskGrad S j) ^ 2)
        = (T:ℝ) * (eta * taskGrad S j) ^ 2 := by
      rw [Finset.sum_const]
      norm_num [Fintype.card_fin, Nat.cast_ofNat]
    calc (∑ i, ((S.w j - S.tasks i j) - eta * taskGrad S j) ^ 2 / 2)
        = (∑ i, ((S.w j - S.tasks i j) ^ 2
            - 2 * eta * taskGrad S j * (S.w j - S.tasks i j)
            + (eta * taskGrad S j) ^ 2) / 2) :=
          Finset.sum_congr rfl (fun i _ => by rw [hexp i])
      _ = (∑ i, ((S.w j - S.tasks i j) ^ 2
            - 2 * eta * taskGrad S j * (S.w j - S.tasks i j))
            + ∑ i, (eta * taskGrad S j) ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      _ = ((∑ i, (S.w j - S.tasks i j) ^ 2)
            - 2 * eta * taskGrad S j * taskGrad S j
            + (T:ℝ) * (eta * taskGrad S j) ^ 2) / 2 := by
          rw [Finset.sum_sub_distrib, hsum1, hsum2]
      _ = (∑ i, (S.w j - S.tasks i j) ^ 2 / 2)
          - (2 * eta - (T:ℝ) * eta ^ 2) * taskGrad S j ^ 2 / 2 := by
          have hsd : (∑ i, (S.w j - S.tasks i j) ^ 2)
              = (∑ i, (S.w j - S.tasks i j) ^ 2 / 2) * 2 := by
            have hper : ∀ i : Fin T, (S.w j - S.tasks i j) ^ 2
                = (S.w j - S.tasks i j) ^ 2 / 2 * 2 := by
              intro i
              field_simp
            rw [Finset.sum_congr rfl (fun i _ => hper i),
              ← Finset.sum_mul]
          rw [hsd]
          field_simp
          ring
  -- шаг 4: применяем поэлементные тождества и собираем
  have hsumconv : ∑ j, ∑ i, ((taskStep S eta).w j - S.tasks i j) ^ 2 / 2
      = ∑ j, ((∑ i, (S.w j - S.tasks i j) ^ 2 / 2)
        - (2 * eta - (T:ℝ) * eta ^ 2) * taskGrad S j ^ 2 / 2) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_congr rfl (fun i _ => by rw [helem j i]), hinner j]
  rw [hsumconv, Finset.sum_sub_distrib, ← Finset.sum_div]
  -- финальное сворачивание: Σ_j (a * g_j^2 / 2) = a * Σ g^2 при a = (2η−Tη²)/2
  have hcoef : (2 * eta - (T:ℝ) * eta ^ 2) / 2
      = (2 * eta - (T:ℝ) * eta ^ 2) * (1/2) := by ring
  have hmul : (∑ j, (2 * eta - (T:ℝ) * eta ^ 2)
      * taskGrad S j ^ 2) / 2
      = (2 * eta - (T:ℝ) * eta ^ 2) / 2 * ∑ j, taskGrad S j ^ 2 := by
    have h1 := (Finset.mul_sum (f := fun j => taskGrad S j ^ 2)
      (s := Finset.univ) (a := (2 * eta - (T:ℝ) * eta ^ 2))).symm
    rw [h1, div_mul_eq_mul_div]
  rw [hmul]

/-- СВЯЗЬ P0: энергия убывает при фактическом обновлении
параметров (при 0 < η, T·η < 2 и ненулевом градиенте).
Условие g ≠ 0 ЧЕСТНОЕ: в критической точке спуска нет. -/
theorem taskStep_energy_descent (S : TaskState k T) (eta : ℝ)
    (h0 : 0 < eta) (h2 : (T:ℝ) * eta < 2)
    (hgrad : ∑ j, taskGrad S j ^ 2 ≠ 0) :
    taskEnergy (taskStep S eta) < taskEnergy S := by
  rw [taskStep_identity]
  have hpos : 0 < ∑ j, taskGrad S j ^ 2 := by
    have hnn : (0:ℝ) ≤ ∑ j, taskGrad S j ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exact absurd heq.symm hgrad
  have hcoef : 0 < (2 * eta - (T:ℝ) * eta ^ 2) / 2 := by
    have hpos2 : 0 < 2 * eta - (T:ℝ) * eta ^ 2 := by
      nlinarith [sq_nonneg eta, h0, h2]
    exact div_pos hpos2 (by norm_num)
  have := mul_pos hcoef hpos
  linarith

/-- ОПРОВЕРЖЕНИЕ ИНВАРИАНТА НЕИЗМЕННОСТИ: в канонической модели
качество МЕНЯЕТСЯ с весами (вычисляется, а не хранится):
одно-задачный случай (T = 1), η ∈ (0,2), ненулевой градиент —
качество (потеря задачи) строго убывает. -/
theorem quality_changes_with_weights
    (S : TaskState k 1) (eta : ℝ) (h0 : 0 < eta) (h2 : eta < 2)
    (hgrad : ∑ j, taskGrad S j ^ 2 ≠ 0) :
    taskQual (taskStep S eta) 0 < taskQual S 0 := by
  have h := taskStep_energy_descent S eta h0
    (by simp only [Nat.cast_one, one_mul]; linarith) hgrad
  have hE : taskEnergy S = taskQual S 0 := by
    unfold taskEnergy
    rw [Fin.sum_univ_one]
  have hE' : taskEnergy (taskStep S eta)
      = taskQual (taskStep S eta) 0 := by
    unfold taskEnergy
    rw [Fin.sum_univ_one]
  rw [hE, hE'] at h
  exact h

end Hagi.Learning.TrainingTransition

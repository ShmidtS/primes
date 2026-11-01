import Mathlib

/-!
# LinkedQVec 

Проблема: `CoupledHAGIInvariant` принимает `qvec : ℕ → Fin 5 → ℝ`
как произвольную последовательность — она НЕ обязана
совпадать с метриками реального состояния. Скалярный
Qgen = ΣwᵢQᵢ может скрыть обрушение одной компоненты
ростом другой.

Решение: качество — ФУНКЦИЯ состояния `evaluate : S → (Fin 5 → ℝ)`.
1. `floor_preserved`: покомпонентный floor сохраняется вдоль
   траектории без внешних последовательностей;
2. `qgen_hides`: КОНТРПРИМЕР: Qgen (веса ½,½) не отличает
   (1,0) от (0,1) — обрушение компоненты скрыто;
3. `floor_catches`: покомпонентный floor ловит деградацию,
   которую Qgen пропустил.
-/

namespace Hagi.Unified.LinkedQVec

/-- Состояние с ЗАКРЕПЛЁННЫМ измерителем качества:
qvec = evaluate S — отдельная последовательность невозможна. -/
structure MeasuredState (S : Type*) where
  evaluate : S → (Fin 5 → ℝ)

variable {S : Type*} (M : MeasuredState S)

/-- Покомпонентный floor-контракт. -/
def FloorKept (s : S) (floor : Fin 5 → ℝ) : Prop :=
  ∀ i, floor i ≤ M.evaluate s i

/-- Траектория = список состояний; итоговое состояние
сохраняет floor, если каждое состояние цепочки его
держит (качество связано с состоянием, без внешних
последовательностей). -/
theorem floor_preserved (floor : Fin 5 → ℝ) (s₀ : S)
    (steps : List S)
    (h₀ : FloorKept M s₀ floor)
    (hchain : ∀ s ∈ steps, FloorKept M s floor) :
    FloorKept M (steps.foldl (fun _ s => s) s₀) floor := by
  have key : ∀ (l : List S) (z : S),
      l.foldl (fun _ s => s) z = l.getLastD z := by
    intro l z
    induction l generalizing z with
    | nil => rfl
    | cons s rest ih =>
      rw [List.foldl_cons, ih, List.getLastD_cons]
  rw [key]
  cases steps with
  | nil => exact h₀
  | cons s rest =>
    rw [List.getLastD_cons]
    induction rest generalizing s with
    | nil => exact hchain s (List.mem_cons_self ..)
    | cons t tl ih =>
      rw [List.getLastD_cons]
      apply ih
      intro x hx
      exact hchain x (List.mem_cons_of_mem s hx)

/-- Скалярная агрегация Qgen (для оптимизации, НЕ контроля). -/
noncomputable def qgen (w : Fin 5 → ℝ) (q : Fin 5 → ℝ) : ℝ :=
  ∑ i, w i * q i

/-- Покомпонентный floor для векторов качества. -/
def VecFloorKept (floor q : Fin 5 → ℝ) : Prop :=
  ∀ i, floor i ≤ q i

/-- КОНТРПРИМЕР: Qgen с равными весами не отличает
единичный вектор e₀ от e₁ — обрушение нулевой компоненты
(e₀→e₁: Q₀ упала 1→0) полностью скрыто ростом другой. -/
theorem qgen_hides :
    qgen (fun _ => 1 / 2) (fun i => if i = 0 then 1 else 0)
      = qgen (fun _ => 1 / 2) (fun i => if i = 1 then 1 else 0) := by
  unfold qgen
  simp

/-- Покомпонентный floor ЛОВИТ деградацию: вектор (1,0)
держит floor (½,0), а (0,1) с ТЕМ ЖЕ Qgen его нарушает. -/
theorem floor_catches :
    VecFloorKept (fun i => if i = 0 then 1/2 else 0)
        (fun i => if i = 0 then 1 else 0)
      ∧ ¬ VecFloorKept (fun i => if i = 0 then 1/2 else 0)
        (fun i => if i = 1 then 1 else 0) := by
  constructor
  · intro i
    fin_cases i <;> norm_num
  · intro h
    have h0 := h 0
    norm_num at h0

end Hagi.Unified.LinkedQVec

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.AdapterGrowth

/-!
# WarmStart — что именно должен измерять гейт переноса адаптера

`unified.py`: тёплый старт свежего адаптера весами лучшего домена, если тот
сертифицировал ce <= 0.5; перенос оправдан только при малом разрыве старта.
`warm_transfer_sound` (AdapterBank) гарантирует корректность копирования и
обучаемость; здесь — критерий полезности.

* `objOn L A B = L (adapterVec A B)` — целевая функция домена;
* `cold_eq_id` — cold start (`B = 0`) — это `L id`;
* `warm_better_iff` — тёплый старт не хуже холодного ⇔ объектив адаптера
  источника на **новом** домене ≤ объектив тождества: `tail_ce` нового
  домена (tail_ce) — правильная величина, CE старого — нет;
* `old_ce_not_transfer` — контрпример `Fin 1`: адаптер, оптимальный для
  старого домена, худший для нового.
-/

namespace Hagi.Theory.WarmStart
open Hagi.Theory.AdapterGrowth
variable {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]

/-- Целевая функция на домене как функция отображения `d → d`. -/
def objOn (L : ((d → ℝ) → d → ℝ) → ℝ) (A : Matrix r d ℝ) (B : Matrix d r ℝ) : ℝ :=
  L (adapterVec A B)
/-- Cold start (`B = 0`) — тождество. -/
theorem cold_eq_id (L : ((d → ℝ) → d → ℝ) → ℝ) (A : Matrix r d ℝ) : objOn L A 0 = L id := by
  simp [objOn, adapter_neutral_B]
/-- Тёплый старт лучше холодного на новом домене ⇔ объектив src-адаптера
на новом домене ≤ объектив тождества — именно это должен измерять
`tail_ce` нового домена (unified.py), а не CE старого. -/
theorem warm_better_iff (L : ((d → ℝ) → d → ℝ) → ℝ) (As : Matrix r d ℝ) (Bs : Matrix d r ℝ) :
    objOn L As Bs ≤ objOn L As 0 ↔ L (adapterVec As Bs) ≤ L id := by
  rw [cold_eq_id]; rfl
/-- CE на СТАРОМ домене ничего не гарантирует на новом: два домена с
противоположными оптимумами (`L₁ = −x`, `L₂ = x` на `Fin 1`): адаптер,
оптимальный для старого, худший для нового. -/
theorem old_ce_not_transfer :
    let L1 : ((Fin 1 → ℝ) → Fin 1 → ℝ) → ℝ := fun f => -(f (fun _ => 1) 0)
    let L2 : ((Fin 1 → ℝ) → Fin 1 → ℝ) → ℝ := fun f => f (fun _ => 1) 0
    let A : Matrix (Fin 1) (Fin 1) ℝ := 1
    let B : Matrix (Fin 1) (Fin 1) ℝ := 1
    L1 (adapterVec A B) < L1 id ∧ L2 id < L2 (adapterVec A B) := by
  intro L1 L2 A B
  have hAv : adapterVec A B = fun x => fun i => 2 * x i := by
    funext x i
    rw [adapterVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_one]
    fin_cases i <;> simp [A, B, Matrix.one_apply] <;> ring
  simp only [hAv, L1, L2]
  norm_num

end Hagi.Theory.WarmStart

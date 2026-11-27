/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# GPM — проекция градиента на дополнение памяти сохраняет прошлые выходы

`_proj_out(x, Ul, Ur)` (optimal_lm.py): `x − Ul (Ulᵀ x)` и `x − (x Ur) Urᵀ` —
Gradient Projection Memory: обновление не меняет компоненту в подпространстве
прошлых задач. `gpm_left/right` — ортонормированные базисы (SVD выходов).

* `projOut` — `g − ∑ᵢ ⟨uᵢ, g⟩ uᵢ` для ортонормированной памяти `U`;
* `projOut_orth` — спроецированный градиент ортогонален каждой строке `U`;
* `gpm_outputs_preserved` — шаг `w − projOut U g` сохраняет `⟨w, uⱼ⟩` точно:
  нулевое забывание выходов на памяти (правая проекция — тот же факт по `dot_comm`).

Граница: память — точный ортонормированный базис; SVD-усечение в коде
приближённое, ошибка не моделируется (см. `ContinualForgetting`).

`truncation_loses_old`: направление, не вошедшее в итоговую память, теряет
защиту. В коде этого не происходит благодаря правилу приёма
`k_new = min k (max_k − cur_r)` (`gpm_admission_keeps_old`: `cur_r + k_new ≤
max_k`) и тому, что QR матрицы с ортонормированным префиксом возвращает его
на месте (гипотеза о QR), поэтому `take max_k` старые столбцы сохраняет
(`take_keeps_prefix`). Сохранение прошлых выходов гарантировано для строк
итоговой памяти.

Цена защиты (983576b: базисы на 90% энергии блокировали обучение, CE
0.754 → 0.598, GPM выключен по умолчанию): `pythagoras_one`,
`projOut_sub`, `projOut_smul`, `projOut_idem`, `projOut_of_orth` — линейность,
идемпотентность и инвариантность `⊥ U`;
`decayed`, `decay_keeps_protected`, `decay_unprotected` — защищённый весовой
спад (projected_weight_decay, trunk_ops.py): `W' = W − dC − c·projOut W`;
при `dC ⊥ U` старые выходы сохраняются точно, спад действует только на
незащищённую компоненту (`projOut W' = (1 − c)·projOut W − dC`);
`projOut_norm_le`, `projOut_norm_lt` — проекция градиента не увеличивает
норму и строго укорачивает шаг, если градиент нового домена имеет компоненту
в памяти. Нулевое забывание на памяти покупается скоростью обучения нового.
-/

namespace Hagi.Step.GPM
open Finset
variable {n k : ℕ}

/-- Скалярное произведение строк. -/
def dot (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i
/-- Память GPM: ортонормированные строки-прототипы. -/
def Orthonormal (U : Fin k → (Fin n → ℝ)) : Prop :=
  (∀ i, dot (U i) (U i) = 1) ∧ ∀ i j, i ≠ j → dot (U i) (U j) = 0
/-- Проекция градиента на дополнение памяти (как _proj_out). -/
noncomputable def projOut (U : Fin k → (Fin n → ℝ)) (g : Fin n → ℝ) : Fin n → ℝ :=
  fun a => g a - ∑ i, dot (U i) g * U i a
theorem dot_sub_left (x y z : Fin n → ℝ) : dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]
theorem dot_comm (x y : Fin n → ℝ) : dot x y = dot y x := by
  simp [dot, mul_comm]
theorem dot_sum_right (x : Fin n → ℝ) (f : Fin k → ℝ) (u : Fin k → Fin n → ℝ) :
    dot x (∑ i, f i • u i) = ∑ i, f i * dot x (u i) := by
  unfold dot
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => (by ring : x a * (f i * u i a) = f i * (x a * u i a))
/-- Спроецированный градиент ортогонален каждой строке памяти. -/
theorem projOut_orth (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (j : Fin k)
    (g : Fin n → ℝ) : dot (projOut U g) (U j) = 0 := by
  have hP : projOut U g = g - ∑ i, dot (U i) g • U i := by
    funext a; simp [projOut, Finset.sum_apply]
  rw [hP, dot_sub_left, dot_comm g (U j), dot_comm (∑ i, dot (U i) g • U i) (U j), dot_sum_right]
  have hterm : ∀ i : Fin k, dot (U i) g * dot (U j) (U i) = if i = j then dot (U j) g else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp [hU.1]
    · rw [if_neg h, hU.2 j i (Ne.symm h), mul_zero]
  rw [show (∑ i, dot (U i) g * dot (U j) (U i)) = ∑ i, (if i = j then dot (U j) g else 0) from
    Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq' (Finset.univ) j (fun _ => dot (U j) g)]
  simp
/-- Шаг GPM `w' = w − projOut U g` сохраняет выходы строки на памяти. -/
theorem gpm_outputs_preserved (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (j : Fin k)
    (w g : Fin n → ℝ) : dot (w - projOut U g) (U j) = dot w (U j) := by
  rw [dot_sub_left, projOut_orth U hU j g, sub_zero]

/-- Базисные векторы в `Fin 2 → ℝ`. -/
def e1 : Fin 2 → ℝ := ![1, 0]
def e2 : Fin 2 → ℝ := ![0, 1]
def U1 : Fin 1 → (Fin 2 → ℝ) := fun _ => e1
theorem U1_orthonormal : Orthonormal U1 := by
  refine ⟨fun i => ?_, fun i j _ => ?_⟩
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [U1, e1, dot, Fin.sum_univ_two]
  · exact absurd (Subsingleton.elim i j) (by assumption)
/-- Truncation of the merged GPM basis can drop an old direction `e₂`:
the projected step then has a nonzero component on `e₂` — the old output
`<w, e₂>` is no longer preserved (`gpm_outputs_preserved` only covers
rows of the truncated memory). -/
theorem truncation_loses_old : dot (projOut U1 e2) e2 ≠ 0 := by
  unfold projOut dot
  simp [U1, e1, e2, Fin.sum_univ_two]

/-- The admission rule of update_gpm_bases: `k_new = min k (max_k − cur_r)`
keeps `cur_r + k_new ≤ max_k`. -/
theorem gpm_admission_keeps_old (k cur_r max_k : ℕ) (hcur : cur_r ≤ max_k) :
    cur_r + min k (max_k - cur_r) ≤ max_k := by omega
/-- Truncating the merged list to `max_k ≥ cur_r` keeps all `cur_r` old
entries: if QR returns the old orthonormal columns in the first `cur_r`
positions, they survive `take max_k`. -/
theorem take_keeps_prefix (l : List ℝ) (cur_r max_k : ℕ) (hcur : cur_r ≤ max_k)
    (hlen : cur_r ≤ l.length) {i : ℕ} (hi : i < cur_r) :
    (l.take max_k)[i]? = l[i]? := by
  rw [List.getElem?_eq_getElem (by rw [List.length_take]; exact lt_min_iff.2 ⟨by omega, by omega⟩),
    List.getElem?_eq_getElem (by omega), List.getElem_take]
variable {n : ℕ}
/-- Один защищённый вектор `u` (ортонормированный): `projOut u g = g − ⟨u,g⟩u`. -/
theorem projOut_one (u g : Fin n → ℝ) :
    projOut (fun _ : Fin 1 => u) g = fun a => g a - dot u g * u a := by
  unfold projOut
  funext a
  simp [Fin.sum_univ_one]
/-- Пифагор: `‖g‖² = ‖P g‖² + ⟨u,g⟩²`. -/
theorem pythagoras_one (u g : Fin n → ℝ) (hu : dot u u = 1) :
    dot g g = dot (projOut (fun _ : Fin 1 => u) g) (projOut (fun _ : Fin 1 => u) g) + dot u g ^ 2 := by
  have hP : projOut (fun _ : Fin 1 => u) g = fun a => g a - dot u g * u a := projOut_one u g
  simp only [hP]
  unfold dot
  have hu' : ∑ i, u i * u i = 1 := hu
  have hsplit : ∀ i, g i * g i = (g i - (∑ x, u x * g x) * u i) * (g i - (∑ x, u x * g x) * u i)
      + (2 * (∑ x, u x * g x) * g i * u i - (∑ x, u x * g x) ^ 2 * (u i * u i)) := by
    intro i
    set s := ∑ x, u x * g x with hs
    ring
  have hsplit' : ∑ i, g i * g i = ∑ i, ((g i - (∑ x, u x * g x) * u i) * (g i - (∑ x, u x * g x) * u i)
      + (2 * (∑ x, u x * g x) * g i * u i - (∑ x, u x * g x) ^ 2 * (u i * u i))) :=
    Finset.sum_congr rfl (fun i _ => hsplit i)
  rw [Finset.sum_add_distrib] at hsplit'
  have hs : ∑ i, g i * u i = ∑ x, u x * g x := Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h1 : ∑ i, 2 * (∑ x, u x * g x) * g i * u i = 2 * (∑ x, u x * g x) ^ 2 := by
    have : ∀ i, 2 * (∑ x, u x * g x) * g i * u i = (2 * (∑ x, u x * g x)) * (g i * u i) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum, hs]
    ring
  have h2 : ∑ i, (∑ x, u x * g x) ^ 2 * (u i * u i) = (∑ x, u x * g x) ^ 2 := by
    have : ∀ i, (∑ x, u x * g x) ^ 2 * (u i * u i) = ((∑ x, u x * g x) ^ 2) * (u i * u i) := fun i => rfl
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum, hu']
    ring
  have hsum : ∑ i, (2 * (∑ x, u x * g x) * g i * u i - (∑ x, u x * g x) ^ 2 * (u i * u i))
      = (∑ x, u x * g x) ^ 2 := by
    rw [Finset.sum_sub_distrib, h1, h2]; ring
  rw [hsum] at hsplit'
  exact hsplit'
/-- Проекция не увеличивает длину. -/
theorem projOut_norm_le (u g : Fin n → ℝ) (hu : dot u u = 1) :
    dot (projOut (fun _ : Fin 1 => u) g) (projOut (fun _ : Fin 1 => u) g) ≤ dot g g := by
  have := pythagoras_one u g hu
  nlinarith [sq_nonneg (dot u g)]
/-- Компонента градиента в памяти строго укорачивает шаг: GPM платит скоростью
обучения нового домена (983576b выключил защиту: CE 0.754 → 0.598). -/
theorem projOut_norm_lt (u g : Fin n → ℝ) (hu : dot u u = 1) (h : dot u g ≠ 0) :
    dot (projOut (fun _ : Fin 1 => u) g) (projOut (fun _ : Fin 1 => u) g) < dot g g := by
  have := pythagoras_one u g hu
  nlinarith [sq_pos_of_ne_zero h]

/-- Общая цена GPM-защиты: `‖g‖² = ‖Pg‖² + ∑_j ⟨u_j,g⟩²` — длина шага
теряет ровно энергию градиента в памяти. -/
theorem dot_sub_right (x y z : Fin n → ℝ) : dot x (y - z) = dot x y - dot x z := by
  rw [dot_comm, dot_sub_left, dot_comm z x, dot_comm y x]
theorem dot_add_left (x y z : Fin n → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]
theorem dot_add_right (x y z : Fin n → ℝ) : dot x (y + z) = dot x y + dot x z := by
  rw [dot_comm, dot_add_left, dot_comm y x, dot_comm z x]
theorem dot_sum_left (f : Fin k → ℝ) (u : Fin k → (Fin n → ℝ)) (x : Fin n → ℝ) :
    dot (∑ i, f i • u i) x = ∑ i, f i * dot (u i) x := by
  rw [dot_comm, dot_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [dot_comm (u i) x]
/-- Разложение: `g = Pg + ∑ c_j u_j`, `c_j = ⟨u_j, g⟩`. -/
theorem proj_decomp (U : Fin k → (Fin n → ℝ)) (g : Fin n → ℝ) :
    g = projOut U g + ∑ j, dot (U j) g • U j := by
  unfold projOut; funext a; simp [Finset.sum_apply]
/-- Пифагор для ортонормированной памяти: `‖g‖² = ‖Pg‖² + ∑ ⟨u_j,g⟩²`. -/
theorem pythagoras_k (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (g : Fin n → ℝ) :
    dot g g = dot (projOut U g) (projOut U g) + ∑ j, dot (U j) g ^ 2 := by
  have hdecomp := proj_decomp U g
  have horth : dot (projOut U g) (∑ j, dot (U j) g • U j) = 0 := by
    rw [dot_comm, dot_sum_left]
    exact Finset.sum_eq_zero fun j _ => by
      rw [dot_comm (U j) (projOut U g), projOut_orth U hU j g]; ring
  have hnorm : dot (∑ j, dot (U j) g • U j) (∑ j, dot (U j) g • U j)
      = ∑ j, dot (U j) g ^ 2 := by
    rw [dot_sum_left]
    have : ∀ j, dot (U j) g * dot (U j) (∑ l, dot (U l) g • U l) = dot (U j) g ^ 2 := by
      intro j
      rw [dot_sum_right]
      have hsum : ∑ l, dot (U j) g * (dot (U l) g * dot (U j) (U l)) = dot (U j) g ^ 2 := by
        have hterm : ∀ l, dot (U j) g * (dot (U l) g * dot (U j) (U l))
            = if j = l then dot (U j) g ^ 2 else 0 := by
          intro l
          by_cases h : j = l
          · subst h; rw [hU.1, if_pos rfl]; ring
          · rw [hU.2 j l h, if_neg h]; ring
        rw [Finset.sum_congr rfl (fun l _ => hterm l)]
        rw [Finset.sum_ite_eq univ j (fun _ => dot (U j) g ^ 2)]
        simp
      calc dot (U j) g * ∑ l, dot (U l) g * dot (U j) (U l)
          = ∑ l, dot (U j) g * (dot (U l) g * dot (U j) (U l)) := by rw [Finset.mul_sum]
        _ = dot (U j) g ^ 2 := hsum
    rw [Finset.sum_congr rfl (fun j _ => this j)]
  have hcross : dot (projOut U g) (∑ j, dot (U j) g • U j)
      + dot (∑ j, dot (U j) g • U j) (projOut U g) = 0 := by
    rw [horth, dot_comm, horth]; ring
  have hadd : dot g g = dot (projOut U g + ∑ j, dot (U j) g • U j)
      (projOut U g + ∑ j, dot (U j) g • U j) := by rw [← hdecomp]
  have hexpand : dot (projOut U g + ∑ j, dot (U j) g • U j) (projOut U g + ∑ j, dot (U j) g • U j)
      = dot (projOut U g) (projOut U g) + dot (projOut U g) (∑ j, dot (U j) g • U j)
        + dot (∑ j, dot (U j) g • U j) (projOut U g)
        + dot (∑ j, dot (U j) g • U j) (∑ j, dot (U j) g • U j) := by
    simp only [dot_add_left, dot_add_right]
    ring
  rw [hexpand, hnorm] at hadd
  linarith

/-- `projOut` линеен. -/
theorem projOut_sub (U : Fin k → (Fin n → ℝ)) (g h : Fin n → ℝ) :
    projOut U (g - h) = projOut U g - projOut U h := by
  unfold projOut
  simp only [dot_sub_right, sub_mul, Pi.sub_apply, Finset.sum_sub_distrib, Pi.sub_apply,
    Pi.sub_apply]
  ext a
  simp only [Pi.sub_apply]
  ring
theorem projOut_dot_smul (U : Fin k → (Fin n → ℝ)) (c : ℝ) (g : Fin n → ℝ) (i : Fin k) :
    dot (U i) (c • g) = c * dot (U i) g := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp [Pi.smul_apply]
  ring
theorem projOut_smul (U : Fin k → (Fin n → ℝ)) (c : ℝ) (g : Fin n → ℝ) :
    projOut U (c • g) = c • projOut U g := by
  unfold projOut
  simp only [projOut_dot_smul, Pi.smul_apply, smul_eq_mul]
  ext a
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  apply congrArg (fun s => c * g a - s)
  apply Finset.sum_congr rfl
  intro x _
  ring
/-- Идемпотентность: `projOut U (projOut U g) = projOut U g`. -/
theorem projOut_idem (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U) (g : Fin n → ℝ) :
    projOut U (projOut U g) = projOut U g := by
  show (fun a => projOut U g a - ∑ i, dot (U i) (projOut U g) * U i a) = projOut U g
  have h : ∀ i, dot (U i) (projOut U g) = 0 := fun i =>
    dot_comm (projOut U g) (U i) ▸ projOut_orth U hU i g
  funext a
  simp only [h, zero_mul, Finset.sum_const_zero, sub_zero]
/-- Вектор `⊥ U` — `projOut` его не меняет. -/
theorem projOut_of_orth (U : Fin k → (Fin n → ℝ)) (g : Fin n → ℝ)
    (hg : ∀ i, dot (U i) g = 0) : projOut U g = g := by
  unfold projOut
  simp only [hg, zero_mul, Finset.sum_const_zero, sub_zero]
/-- Защищённый весовой спад (`projected_weight_decay`): `W' = W − dC − c·projOut W`,
`projOut W = W − W·P` — незащищённая часть, `c` — скорость спада. -/
noncomputable def decayed (U : Fin k → (Fin n → ℝ)) (W dC : Fin n → ℝ) (c : ℝ) : Fin n → ℝ :=
  W - dC - c • projOut U W
/-- Защищённая компонента сохраняется точно: если `dC ⊥ U j`, то `⟨W', U j⟩ = ⟨W, U j⟩`. -/
theorem decay_keeps_protected (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U)
    (W dC : Fin n → ℝ) (c : ℝ) (j : Fin k) (hdC : dot dC (U j) = 0) :
    dot (decayed U W dC c) (U j) = dot W (U j) := by
  unfold decayed
  have hsm : dot (c • projOut U W) (U j) = c * dot (projOut U W) (U j) := by
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp [Pi.smul_apply, mul_assoc]
  rw [dot_sub_left, dot_sub_left, hsm]
  have h := projOut_orth U hU j W
  rw [h, hdC]
  ring
/-- Незащищённая компонента: при `dC ⊥ U` — `projOut W' = (1 − c)·projOut W − dC`:
спад действует только на неё, а весь градиент `dC` (ортогональный старым
выходам) попадает в незащищённую часть. -/
theorem decay_unprotected (U : Fin k → (Fin n → ℝ)) (hU : Orthonormal U)
    (W dC : Fin n → ℝ) (c : ℝ) (hdC : ∀ j, dot dC (U j) = 0) :
    projOut U (decayed U W dC c) = (1 - c) • projOut U W - dC := by
  have hdC' : ∀ i, dot (U i) dC = 0 := fun i => dot_comm dC (U i) ▸ hdC i
  unfold decayed
  simp only [projOut_sub, projOut_of_orth U dC hdC', projOut_smul, projOut_idem U hU W]
  ext a
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Hagi.Step.GPM

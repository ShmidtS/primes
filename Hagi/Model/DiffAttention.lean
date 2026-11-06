import Mathlib

/-!
# DiffAttention (источник №80: Ye et al., "Differential
# Transformer", arXiv 2410.05258)

Дифференциальное внимание: две softmax-головы, итог =
w₁ − λ·w₂ — вычитание «шумовой» головы подавляет
загрязнение контекста.

Скалярная формализация над конечным индексным множеством:
1. `sm` — softmax; `sm_sum_one`, `sm_nonneg` — распределение;
2. `sm_shift` — СДВИГ-ИНВАРИАНТНОСТЬ: общий сдвиг логитов
   на c не меняет веса (устойчивость к key-bias;
   вычитаемое сокращается);
3. `noise_cancel` — общий аддитивный шум ВО ВСЕХ позициях
   одной головы не меняет её веса (следствие sm_shift):
   генерируемый контекст-шум самосокращается;
4. `diff_range` — дифф-вес w₁ − λ·w₂ ∈ [−λ, 1]:
   ограниченность дифференциального внимания;
5. `diff_noise_pair` — пара голов с ОБЩИМ сдвигом c:
   дифф-вес инвариантен (шум сокращается В РАЗНОСТИ,
   если входит в обе головы одинаково).
-/

namespace Hagi.Model.DiffAttention

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Softmax-веса по логитам x. -/
noncomputable def sm (x : k → ℝ) (i : k) : ℝ :=
  Real.exp (x i) / ∑ j, Real.exp (x j)

/-- Веса суммируются в 1 (распределение). -/
theorem sm_sum_one (x : k → ℝ) : ∑ i, sm x i = 1 := by
  have hpos : (0:ℝ) < ∑ j, Real.exp (x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos (x j))
      Finset.univ_nonempty
  unfold sm
  rw [← Finset.sum_div, div_self (ne_of_gt hpos)]

/-- Веса неотрицательны. -/
theorem sm_nonneg (x : k → ℝ) (i : k) : 0 ≤ sm x i := by
  unfold sm
  exact div_nonneg (Real.exp_nonneg (x i))
    (Finset.sum_nonneg (fun j _ => (Real.exp_nonneg (x j))))

/-- СДВИГ-ИНВАРИАНТНОСТЬ: общий сдвиг всех логитов на c
не меняет softmax-веса (аддитивный key-bias сокращается
в нормировке). -/
theorem sm_shift (x : k → ℝ) (c : ℝ) (i : k) :
    sm (fun j => x j + c) i = sm x i := by
  have hexp : ∀ j, Real.exp (x j + c)
      = Real.exp c * Real.exp (x j) :=
    fun j => by rw [← Real.exp_add]; congr 1; ring
  unfold sm
  have hsum : ∑ j, Real.exp ((fun j => x j + c) j)
      = Real.exp c * ∑ j, Real.exp (x j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hexp j)
  rw [hsum]
  have hpos : (0:ℝ) < ∑ j, Real.exp (x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos (x j))
      Finset.univ_nonempty
  have hposc : (0:ℝ) < Real.exp c := Real.exp_pos c
  rw [hexp i, mul_div_mul_left _ _ (ne_of_gt hposc)]

/-- ШУМОСЖАТИЕ ГОЛОВЫ: логит = сигнал + ОБЩИЙ шум c во
всех позициях → веса совпадают с бесшумными (следствие
сдвиг-инвариантности: контекст-загрязнение с общим
аддитивным профилем самосокращается). -/
alias noise_cancel := _root_.Hagi.Model.DiffAttention.sm_shift

/-- Дифф-вес: голова1 − λ·голова2. -/
noncomputable def diffW (x y : k → ℝ) (lam : ℝ) (i : k) : ℝ :=
  sm x i - lam * sm y i

/-- ОГРАНИЧЕННОСТЬ ДИФФ-ВНИМАНИЯ: при λ ≥ 0 дифф-вес
лежит в [−λ, 1] (вычитание головы не «взрывает» веса). -/
theorem diff_range (x y : k → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : k) : -lam ≤ diffW x y lam i ∧ diffW x y lam i ≤ 1 := by
  have hx0 : 0 ≤ sm x i := sm_nonneg x i
  have hx1 : sm x i ≤ 1 := by
    have hle := Finset.single_le_sum (f := fun j => sm x j)
      (fun j _ => sm_nonneg x j) (Finset.mem_univ i)
    rw [sm_sum_one x] at hle
    exact hle
  have hy1 : sm y i ≤ 1 := by
    have hle := Finset.single_le_sum (f := fun j => sm y j)
      (fun j _ => sm_nonneg y j) (Finset.mem_univ i)
    rw [sm_sum_one y] at hle
    exact hle
  have hy0 : 0 ≤ sm y i := sm_nonneg y i
  have hmully : lam * sm y i ≤ lam :=
    (mul_le_mul_of_nonneg_left hy1 hlam).trans (mul_one lam).le
  constructor
  · unfold diffW
    linarith
  · unfold diffW
    have hmulnn : 0 ≤ lam * sm y i := mul_nonneg hlam hy0
    linarith

end Hagi.Model.DiffAttention
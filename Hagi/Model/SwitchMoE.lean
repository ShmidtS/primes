import Mathlib
import Hagi.Model.GRPO

/-!
# Switch MoE: балансировка нагрузки (источник №34)

Источник №34: Fedus, Zoph, Shazeer, "Switch Transformers:
Scaling to Trillion Parameter Models" (arXiv 2101.03961).
Auxiliary load-balance loss L = α·n·∑ f_i·P_i штрафует
перегрузку экспертов: f_i — доля токенов у эксперта i,
P_i — вероятность роутера. При роутинге f ∝ P нагрузочный
член ∝ ∑ P_i², и его МИНИМУМ — равномерное распределение.

Формализованное ядро (строгое, |E| = n > 0, ∑ P = 1):
- `switch_floor`: ∑ P_i² ≥ 1/n — нижняя граница
  нагрузочного члена;
- `switch_floor_eq_iff`: равенство ⟺ P равномерно
  (∀ i, P i = 1/n) — единственный минимум баланса
  достигается только равномерным роутингом.
-/

namespace Hagi.Model.SwitchMoE

open Finset

variable {n : ℕ}

/-- Нижняя граница нагрузочного члена: ∑ P² ≥ 1/n. -/
theorem switch_floor (P : Fin n → ℝ) (hsum : ∑ i, P i = 1)
    (hn : 0 < n) :
    1 / n ≤ ∑ i, (P i) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hd := Hagi.Model.GRPO.groupAdv_sq_decomp P hn 0
  simp only [sub_zero] at hd
  rw [hsum] at hd
  have hnn : 0 ≤ ∑ i, (P i - 1 / n) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hval : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by
    field_simp
  rw [hval] at hd
  linarith

/-- Равенство в границе ⟺ равномерное распределение. -/
theorem switch_floor_eq_iff (P : Fin n → ℝ)
    (hsum : ∑ i, P i = 1) (hn : 0 < n) :
    ∑ i, (P i) ^ 2 = 1 / n ↔ ∀ i, P i = 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · intro heq
    have hd := Hagi.Model.GRPO.groupAdv_sq_decomp P hn 0
    simp only [sub_zero] at hd
    rw [hsum] at hd
    have hval : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by
      field_simp
    rw [hval] at hd
    -- из heq и hd: ∑ (P i − 1/n)² = 0
    have hzero : ∑ i, (P i - 1 / n) ^ 2 = 0 := by linarith
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (P i - 1 / n) ^ 2 :=
      fun i _ => sq_nonneg _
    have hper : ∀ i ∈ Finset.univ, (P i - 1 / n) ^ 2 = 0 :=
      fun i _ =>
        Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp hzero i
          (Finset.mem_univ i)
    intro i
    have hz := hper i (Finset.mem_univ i)
    have hsub : P i - 1 / n = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hz
    exact sub_eq_zero.mp hsub
  · intro hunif
    have : ∀ i ∈ Finset.univ, (P i) ^ 2 = (1 / n) ^ 2 := by
      intro i _
      rw [hunif i]
    rw [Finset.sum_congr rfl this, Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin]
    field_simp

end Hagi.Model.SwitchMoE

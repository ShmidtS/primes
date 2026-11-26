/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Algebra.Order.Rearrangement
import Hagi.Theory.ArchiverCodeLength

/-!
# MDLSearchOrder — почему перебор кандидатов по длине кода оптимален

Синтез программ (`iter_candidates_mdl`) выдаёт кандидатов в порядке возрастания
длины описания. Здесь это доказано: ожидаемая позиция первой точной программы
минимальна, когда приор не возрастает по позиции.

* `expectedRank` — `Σ k·p_k·Π_{j<k}(1−p_j)`: позиция первой точной, если `p_k` —
  вероятность точности кандидата `k`.
* `expectedRank_le` — не выше `Σ k·p_k`.
* `mdl_order_optimal` — при убывающем `p` перестановка не уменьшает `Σ k·p_{σ k}`
  (rearrangement inequality); порядок по MDL и есть такой.
* `expectedRank_le_kraft` — для `p_k = 2^{-L_k}` ожидаемая позиция `≤ Σ k·2^{-L_k}`.
-/

namespace Hagi.Theory.MDLSearchOrder

open Finset

noncomputable def expectedRank (N : ℕ) (p : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, (k : ℝ) * p k * ∏ j ∈ Finset.Iio k, (1 - p j)
/-- `q` — субраспределение: ожидаемая позиция не выше `Σ k·p_k`. -/
theorem expectedRank_le (N : ℕ) (p : Fin N → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1) :
    expectedRank N p ≤ ∑ k : Fin N, (k : ℝ) * p k := by
  unfold expectedRank
  refine Finset.sum_le_sum fun k _ => ?_
  have hprod1 : ∏ j ∈ Finset.Iio k, (1 - p j : ℝ) ≤ 1 := by
    have h := Finset.prod_induction (s := Finset.Iio k) (fun j : Fin N => (1 - p j : ℝ))
      (fun x => 0 ≤ x ∧ x ≤ 1) (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, by
        have := mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1); linarith⟩) ⟨by norm_num, by norm_num⟩
      (fun x _ => ⟨by linarith [hp x], by linarith [hp x]⟩)
    exact h.2
  have hk0 : (0:ℝ) ≤ (k : ℝ) * p k := by
    have : (0:ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    nlinarith [(hp k).1]
  calc (k : ℝ) * p k * ∏ j ∈ Finset.Iio k, (1 - p j)
      ≤ (k : ℝ) * p k * 1 := by nlinarith
    _ = (k : ℝ) * p k := mul_one _
/-- MDL-порядок оптимален: если `p` не возрастает по позиции (длинный код — не вероятнее),
любая перестановка кандидатов не уменьшает ожидаемую позицию (rearrangement). -/
theorem mdl_order_optimal {N : ℕ} (p : Fin N → ℝ) (hanti : Antivary p (fun k => (k : ℕ)))
    (σ : Equiv.Perm (Fin N)) :
    ∑ k : Fin N, (k : ℝ) * p k ≤ ∑ k : Fin N, (k : ℝ) * p (σ k) := by
  have h : Antivary (fun k : Fin N => (k : ℝ)) p := by
    intro i j hij
    have hle : (j : ℕ) ≤ (i : ℕ) := not_lt.1 fun hlt => (not_lt.2 (hanti hlt)) hij
    show ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ)
    exact_mod_cast hle
  have h2 := h.sum_smul_le_sum_smul_comp_perm (σ := σ)
  simpa [smul_eq_mul] using h2
/-- Kraft-приор `p_k = 2^{-L_k}`: ожидаемая позиция `≤ Σ k·2^{-L_k}` — конечный Levin-поиск. -/
theorem expectedRank_le_kraft {N : ℕ} (L : Fin N → ℕ) :
    expectedRank N (fun k => (1 / 2 : ℝ) ^ L k) ≤ ∑ k : Fin N, (k : ℝ) * (1 / 2 : ℝ) ^ L k := by
  apply expectedRank_le
  intro k
  exact ⟨pow_nonneg (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩

end Hagi.Theory.MDLSearchOrder

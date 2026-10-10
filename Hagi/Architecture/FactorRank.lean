/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Mathlib
set_option linter.style.header false

/-!
# FactorRank — неотрицательный ранг vs обычный (gap-aware)

По статье «Gap-Aware Exact Nonnegative Matrix Factorization»
(source: 2606.25715).

* `nonnegFactorization M k` — `M = W * H` с `W, H ≥ 0` и
  внутренней размерностью `k`; `nonnegRank` — минимальная
  такая `k`.
* `rank_le_nonnegRank` — при существовании факторизации
  `rank(M) ≤ nonnegRank(M)`: gap `r₊ − r ≥ 0` всегда.
* `factorGap` — `rank(M) < nonnegRank(M)` (диагностический
  предикат, не теорема о loss).
* `positive_measure_pos_prob` — из `μ F > 0` следует лишь
  `μ Fᶜ < 1`, а не `μ Fᶜ = 0`.
* `regimeAFactor` / `regimeCFactor` / `regimeC_fractional` —
  классификация фактора `W` и дробный рост capacity в
  режиме C.

NMF-допущения на signed transformer weights не переносятся;
это здесь не формализуется.
-/

open Matrix MeasureTheory Finset

namespace Hagi.Architecture

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ## Неотрицательная факторизация -/

/-- M = W·H с W, H ≥ 0 и внутренней размерностью k. -/
def nonnegFactorization (M : Matrix m n ℝ) (k : ℕ) : Prop :=
  ∃ (W : Matrix m (Fin k) ℝ) (H : Matrix (Fin k) n ℝ),
    (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧ M = W * H

/-- Если `M` имеет неотрицательную факторизацию внутренней
размерности `k`, то `M.rank ≤ k`. -/
theorem rank_le_of_nonnegFactorization (M : Matrix m n ℝ) (k : ℕ)
    (hf : nonnegFactorization M k) :
    M.rank ≤ k := by
  obtain ⟨W, H, _, _, hM⟩ := hf
  have h1 : M.rank = (W * H).rank := by rw [hM]
  rw [h1]
  have h2 := rank_mul_le W H
  have h3 : W.rank ≤ Fintype.card (Fin k) := rank_le_card_width W
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  rw [hcard] at h3
  exact le_trans (le_trans h2 (min_le_left _ _)) h3

/-- Неотрицательный ранг: минимальная внутренняя
размерность неотрицательной факторизации (0 при отсутствии
— используем sInf ∅ = 0, что только ослабляет неравенства). -/
noncomputable def nonnegRank (M : Matrix m n ℝ) : ℕ :=
  sInf {k | nonnegFactorization M k}

/-- Если существует хоть одна неотрицательная факторизация,
то `M.rank ≤ nonnegRank M`. -/
theorem rank_le_nonnegRank (M : Matrix m n ℝ)
    (hexists : ∃ k, nonnegFactorization M k) :
    M.rank ≤ nonnegRank M := by
  obtain ⟨k, hk⟩ := hexists
  have hne : {j | nonnegFactorization M j}.Nonempty := ⟨k, hk⟩
  have hmem : sInf {j | nonnegFactorization M j}
      ∈ {j | nonnegFactorization M j} := Nat.sInf_mem hne
  show M.rank ≤ sInf {j | nonnegFactorization M j}
  exact rank_le_of_nonnegFactorization M _ hmem

/-- Gap-предикат: `M.rank < nonnegRank M`. -/
def factorGap (M : Matrix m n ℝ) : Prop :=
  M.rank < nonnegRank M

/-! ## Честная вероятность (§12 разбора) -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- Если `F` измеримо и `0 < μ F`, то `μ Fᶜ < 1`.
Сильная форма (`μ Fᶜ = 0`) здесь не доказывается. -/
theorem positive_measure_pos_prob (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Set Ω) (hF : MeasurableSet F)
    (hpos : 0 < μ F) :
    0 < μ F ∧ μ Fᶜ < 1 := by
  have h1 : μ F + μ Fᶜ = 1 := prob_add_prob_compl hF
  refine ⟨hpos, ?_⟩
  have h1 : μ F + μ Fᶜ = 1 := prob_add_prob_compl hF
  have hFtop : μ F ≠ ⊤ := by
    intro hh
    rw [hh] at h1
    simp at h1
  have hle : μ Fᶜ ≤ 1 := by
    rw [← h1]
    calc μ Fᶜ = 0 + μ Fᶜ := by ring
      _ ≤ μ F + μ Fᶜ := add_le_add bot_le (le_refl _)
  have hFc : μ Fᶜ ≠ ⊤ :=
    (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  -- toReal-переход (обе ≠ ⊤)
  have hrt : (μ F).toReal + (μ Fᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add hFtop hFc, h1, ENNReal.toReal_one]
  have hpos' : 0 < (μ F).toReal :=
    ENNReal.toReal_pos hpos.ne' hFtop
  have hc' : (μ Fᶜ).toReal < 1 := by linarith
  exact (ENNReal.toReal_lt_toReal hFc ENNReal.one_ne_top).mp hc'

/-! ## Три режима (§5 разбора) -/

/-- Режим A: фактор `W` использует всю внутреннюю
размерность (`W.rank = k`). Режим C (`regimeCFactor`) —
дробный рост: `r < W.rank < k`. -/
def regimeAFactor (W : Matrix m (Fin k) ℝ) : Prop :=
  W.rank = k

def regimeCFactor (W : Matrix m (Fin k) ℝ) (r : ℕ) : Prop :=
  r < W.rank ∧ W.rank < k

/-- В режиме C: `0 < W.rank - r` и `W.rank - r < k - r`. -/
theorem regimeC_fractional {W : Matrix m (Fin k) ℝ} {r : ℕ}
    (hC : regimeCFactor W r) :
    0 < W.rank - r ∧ W.rank - r < k - r := by
  obtain ⟨h1, h2⟩ := hC
  constructor <;> omega

end Hagi.Architecture

namespace Hagi
export Hagi.Architecture (nonnegFactorization rank_le_of_nonnegFactorization nonnegRank rank_le_nonnegRank factorGap positive_measure_pos_prob regimeAFactor regimeCFactor regimeC_fractional)
end Hagi

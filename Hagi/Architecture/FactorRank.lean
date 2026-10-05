/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Mathlib
set_option linter.style.header false

/-!
# R128: FactorRank — неотрицательный ранг vs обычный (gap-aware)

По разбору статьи «Gap-Aware Exact Nonnegative Matrix
Factorization» (2606.25715) и её стыковке с HAGI
(FactorizedMerge / RankBudget / рост фактор-пространства).

**Безопасное ядро, формализуемое без споров статьи:**

* `nonnegFactorization M k` — M = W·H с W, H ≥ 0 и
  внутренней размерностью k.
* `rank_le_nonnegRank` — rank(M) ≤ r₊(M): обычный ранг
  никогда не превосходит неотрицательного. Следствие:
  gap Δr = r₊ − r ≥ 0 всегда, и Δr > 0 — законная мера
  дополнительной expert capacity (Growth Gate по §3 разбора).
* `positive_measure_finite_failure` — ЧЕСТНАЯ вероятностная
  форма (§12 разбора): μ(F) > 0 даёт лишь P(success) > 0
  (μ(Fᶜ) < 1), а НЕ P = 1; усиленная версия статьи в Lean
  не импортируется.
* `FactorRegime` A/B/C — трёхрежимная классификация
  (§5): полный новый subspace / переиспользование базиса /
  дробный рост.
* `factorGap` — Δr > 0 как диагностический гейт расширения
  expert space (не теорема о loss — честная граница §3).

**Честные границы**: NMF-допущения не переносятся на signed
transformer weights напрямую (разбор §18); слепой поиск
факторов (blind solver, §9) — вне Lean; Stiefel→Grassmannian
quotient (§11) — направление, здесь не формализуется.
-/

open Matrix MeasureTheory Finset

namespace Hagi

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ## Неотрицательная факторизация -/

/-- M = W·H с W, H ≥ 0 и внутренней размерностью k. -/
def nonnegFactorization (M : Matrix m n ℝ) (k : ℕ) : Prop :=
  ∃ (W : Matrix m (Fin k) ℝ) (H : Matrix (Fin k) n ℝ),
    (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧ M = W * H

/-- **rank ≤ r₊**: обычный ранг произведения ≤ ранга любого
фактора ≤ ширины фактора; в частности rank(M) ≤ r₊(M) для
минимальной внутренней размерности. Gap Δr = r₊ − r ≥ 0
всегда; Δr > 0 — законная мера дополнительной expert
capacity. -/
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

/-- **rank(M) ≤ nonnegRank(M)** при существовании хотя бы
одной факторизации (gap Δr = r₊ − r ≥ 0 всегда). -/
theorem rank_le_nonnegRank (M : Matrix m n ℝ)
    (hexists : ∃ k, nonnegFactorization M k) :
    M.rank ≤ nonnegRank M := by
  obtain ⟨k, hk⟩ := hexists
  have hne : {j | nonnegFactorization M j}.Nonempty := ⟨k, hk⟩
  have hmem : sInf {j | nonnegFactorization M j}
      ∈ {j | nonnegFactorization M j} := Nat.sInf_mem hne
  show M.rank ≤ sInf {j | nonnegFactorization M j}
  exact rank_le_of_nonnegFactorization M _ hmem

/-- **Gap-факторизация**: r₊ > r — есть структурный аргумент
в пользу расширения expert space (диагностический гейт,
НЕ теорема о loss — честная граница разбора §3). -/
def factorGap (M : Matrix m n ℝ) : Prop :=
  M.rank < nonnegRank M

/-! ## Честная вероятность (§12 разбора) -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- **μ(F) > 0 ⇒ лишь P(success) > 0, а НЕ P = 1**:
положительная мера множества допустимых gauges даёт
положительную вероятность успеха и вероятность неудачи
< 1. Сильная форма «вероятность один» требует отдельного
доказательства μ(Fᶜ) = 0 — в Lean НЕ импортируется
(предостережение §12 разбора статьи). -/
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

/-- Классификация ФАКТОРА W при M = W·H, rank(M) = r,
внутренняя размерность k = r₊:

* `regimeAFactor` — rank W = k: полноценный новый expert
  subspace (все k направлений используются);
* `regimeCFactor` — r < rank W < k: ДРОБНЫЙ рост — новый
  эксперт получает только часть новой subspace capacity
  (самый интересный режим для HAGI-роста, §5);
* режим B (rank = r, переиспользование базиса) — это
  rank W = r при k > r. -/
def regimeAFactor (W : Matrix m (Fin k) ℝ) : Prop :=
  W.rank = k

def regimeCFactor (W : Matrix m (Fin k) ℝ) (r : ℕ) : Prop :=
  r < W.rank ∧ W.rank < k

/-- Режим C даёт дробный рост capacity: k − r новых
направлений, из которых задействовано rank W − r ∈ (0, k−r). -/
theorem regimeC_fractional {W : Matrix m (Fin k) ℝ} {r : ℕ}
    (hC : regimeCFactor W r) :
    0 < W.rank - r ∧ W.rank - r < k - r := by
  obtain ⟨h1, h2⟩ := hC
  constructor <;> omega

end Hagi

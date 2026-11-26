/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# TailGate — среднее хвостов против наихудшего домена

`unified.py` (8395dbc): гейт приёма по средней CE хвостов всех доменов
выключен по умолчанию — замер не показал выигрыша; вместо него
`WORST_TOL = 0.25` на наихудшем домене. Причина в агрегате: среднее скрывает
ухудшение отдельного домена (замер 1.56 → 1.85 при среднем 0.768 → 0.896).

* `tailMean` — средняя CE хвостов;
* `max_le_imp_mean_le` — гейт по наихудшему влечёт гейт по среднему;
* `mean_le_not_imp_max_le` — обратное неверно (контрпример из двух доменов).
-/

namespace Hagi.Unified.TailGate

/-- Средняя CE хвостов по доменам. -/
noncomputable def tailMean (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n
/-- Гейт по наихудшему влечёт гейт по среднему. -/
theorem max_le_imp_mean_le {n : ℕ} (x : Fin n → ℝ) (hn : 0 < n) (tol : ℝ)
    (h : ∀ i, x i ≤ tol) : tailMean x ≤ tol := by
  unfold tailMean
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  calc ∑ i, x i ≤ ∑ _i : Fin n, tol := Finset.sum_le_sum fun i _ => h i
    _ = tol * n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Fintype.card_fin]
/-- Гейт по среднему НЕ влечёт гейт по наихудшему: домен 0 = 1.0, домен 1 = 0.0,
среднее 0.5 ≤ 0.5, но наихудший 1.0 > 0.5. -/
theorem mean_le_not_imp_max_le :
    tailMean (fun i : Fin 2 => if i = 0 then 1 else 0) ≤ 1/2 ∧
    ¬ (∀ i : Fin 2, (if i = 0 then (1:ℝ) else 0) ≤ 1/2) := by
  constructor
  · norm_num [tailMean, Fin.sum_univ_two]
  · intro h
    have := h 0
    norm_num at this

end Hagi.Unified.TailGate

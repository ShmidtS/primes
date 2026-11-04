import Mathlib.Tactic
import Hagi.Prelude.Info
import Hagi.Information.DiscreteFannes
import Hagi.Unified.FannesComplete

set_option linter.style.header false

/-!
# InfoCanonical — канонические мосты теории информации (TD-03, цикл 15)

Дублирование определений (аудит TD-03): энтропия/TV определены
независимо в `Prelude.Info` (entDef/tvDef) и
`Information.DiscreteFannes` (shannon/tvHalf). Мосты ниже
устанавливают ТОЧНЫЕ тождества, после чего любой набор теорем
(Пинскер из Probability.PinskerTV, Фаннес из
Unified.FannesComplete) применим к обоим мирам без дублей —
merge-before-delete: сначала мосты, удаление дублирующих
обёрток — отдельное решение после аудита потребителей.
-/

open Finset

namespace Hagi.Information.InfoCanonical

/-- Энтропии совпадают: shannon = entDef. -/
theorem shannon_eq_entDef {V : Type*} [Fintype V] (p : V → ℝ) :
    Hagi.Information.shannon p = Hagi.Prelude.entDef p := by
  simp [Hagi.Information.shannon, Hagi.Prelude.entDef,
    Real.negMulLog]

/-- Полная вариация: tvHalf = tvDef. -/
theorem tvHalf_eq_tvDef {V : Type*} [Fintype V] (p q : V → ℝ) :
    Hagi.Information.tvHalf p q = Hagi.Prelude.tvDef p q := by
  rfl

/-- ПРИМЕР ДЕЛЕГАЦИИ: фаннес-граница Фаннеса в мире Prelude:
через мост переносится главная теорема FannesComplete. -/
theorem fanes_entDef {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    Hagi.Prelude.entDef p - Hagi.Prelude.entDef q
      ≤ (Hagi.Prelude.tvDef p q) * Real.log (Fintype.card V)
        + (1 + Hagi.Prelude.tvDef p q)
          * Real.binEntropy (Hagi.Prelude.tvDef p q
            / (1 + Hagi.Prelude.tvDef p q)) := by
  have hkey := Hagi.Unified.fanes_unconditional (ι := V) p q hp hq
    hp1 hq1
  rw [shannon_eq_entDef p, shannon_eq_entDef q, tvHalf_eq_tvDef] at hkey
  exact hkey

end Hagi.Information.InfoCanonical

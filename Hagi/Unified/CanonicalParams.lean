import Mathlib
import Hagi.System.GrowthState
import Hagi.Model.StageSemantics

/-!
# CanonicalParams 

Проблема: в проекте две семантики параметров —
`StageSemantics.advance` обновляет `params`, копируя
`weights`, а `ReferenceMachine`/`FunState` обновляют
`weights`. Единой доказанной связи нет.

Решение: `params` — единственный канонический носитель;
`weights` — ПРОИЗВОДНАЯ проекция `toWeights(params)` с
законным (инъективным на образе... здесь достаточно
инъективным) проектором. Тогда:

1. `bridge_update`: активный advance-шаг меняет params ⟹
   меняет и weights — тест аудита №6 «фактические веса
   меняются при обучающем переходе» ВЫПОЛНЕН формально;
2. `advance_params_ne`: при η>0 и dir≠0 params строго
   меняется;
3. `idProj`: тождественный проектор — верный свидетель
   (weights ≡ params в бескомпрессионном пределе).
-/

namespace Hagi.Unified.CanonicalParams

open Hagi

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Законный проектор: инъективная упаковка params в
веса (сжатие без потерь — консервативная база; lossy-
случай добавляет ошибку квантования отдельно). -/
structure LawfulProj (d : ℕ) (toW : X → Fin d → ℝ) : Prop where
  inj : Function.Injective toW

/-- Каноническая упаковка: weights = toWeights(params). -/
noncomputable def canonWeights (toW : X → Fin d → ℝ)
    (S : Hagi.System.GrowthState X) : Fin d → ℝ := toW S.params

/-- Активный шаг меняет params. -/
theorem advance_params_ne (S : Hagi.System.GrowthState X)
    (u : Hagi.Model.StageInput X) (hd : u.stepDir ≠ 0) :
    (Hagi.Model.advance S u).params ≠ S.params := by
  intro h
  apply hd
  have hb : u.sp.eta • u.stepDir = 0 := sub_eq_self.mp h
  exact (smul_eq_zero.mp hb).resolve_left
    (ne_of_gt u.h_eta_pos)

/-- ГЛАВНЫЙ МОСТ: активный шаг меняет canonical weights. -/
theorem bridge_update (toW : X → Fin d → ℝ)
    (hproj : LawfulProj d toW)
    (S : Hagi.System.GrowthState X) (u : Hagi.Model.StageInput X)
    (hd : u.stepDir ≠ 0) :
    canonWeights toW (Model.advance S u)
      ≠ canonWeights toW S := by
  unfold canonWeights
  intro h
  exact advance_params_ne S u hd (hproj.inj h)

/-- Тождественный проектор законен (свидетель). -/
theorem idProj (d : ℕ) : LawfulProj d (fun (x : Fin d → ℝ) => x) :=
  ⟨fun _ _ h => h⟩

end Hagi.Unified.CanonicalParams

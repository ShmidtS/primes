import Mathlib
import Hagi.Unified.CertifiedLoop
import Hagi.Unified.DescentCoreQuad

/-!
# LoopInstances (такт №300): заполнение StepCert из
# реального градиентного шага

Мост DescentCore → CertifiedLoop: квадратичная модель
поставляет зависимый сертификат честного перехода —
капстон применим к настоящему алгоритму.

`quadCert`: шаг w' = w − ∇E (η = 1/L = 1 — оптимальный:
достигает оптимума за один шаг, E(w') = 0) даёт
HonestTransition с drop = E(w) целиком.
`quadDropPos`: drop > 0 при ∇E ≠ 0.
-/

namespace Hagi.Unified.LoopInstances

open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Оптимальный градиентный шаг квадратичной цели —
честный переход с drop = вся энергия. -/
noncomputable def quadCert (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    HonestTransition (S := k → ℝ) (fun w => quadE a w) x (x - quadGrad a x)
      0 0 0 0 where
  objectiveDrop := quadE a x
  objectiveDrop_pos := by
    have h := (quad_one_step a x).2
    unfold Hagi.Unified.DescentCore.nrm2 at h
    have hsum : (0:ℝ) < ∑ i, (quadGrad a x i)^2 := by
      by_contra h0
      push_neg at h0
      apply hx
      funext i
      have hle : (quadGrad a x i)^2 ≤ ∑ j, (quadGrad a x j)^2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      have hnn : (0:ℝ) ≤ (quadGrad a x i)^2 := sq_nonneg _
      have hzi : (quadGrad a x i)^2 = 0 := by linarith
      exact sq_eq_zero_iff.mp hzi
    show 0 < quadE a x
    linarith
  actualDescent := by
    show quadE a (x - quadGrad a x) ≤ quadE a x - quadE a x
    have h0 : (quadObjective a).f (x - quadGrad a x) = 0 :=
      (quad_one_step a x).1
    have heq : (quadObjective a).f (x - quadGrad a x)
        = quadE a (x - quadGrad a x) := rfl
    rw [heq] at h0
    have hz : quadE a x - quadE a x = (0:ℝ) := by ring
    linarith
  riskBound := le_refl 0
  budgetBound := le_refl 0

omit [Nonempty k] in
/-- drop-сертификата положителен при ненулевом градиенте. -/
theorem quadCert_drop_pos (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    0 < (quadCert a x hx).objectiveDrop :=
  (quadCert a x hx).objectiveDrop_pos

omit [Nonempty k] in
/-- Реальный спуск сертификата — точное равенство нулю
энергии после оптимального шага. -/
theorem quadCert_hits_optimum (a x : k → ℝ) :
    quadE a (x - quadGrad a x) = 0 :=
  (quad_one_step a x).1


/-! ### Полный StepCert-инстанс и применение капстона -/

open Hagi.Unified.LinkedQVec Hagi.Unified.CertifiedLoop in
/-- Измеритель качества quad-модели: канал 0 —
capability = 1/(1+E). -/
noncomputable def quadMeasured (a : k → ℝ) :
    MeasuredState (k → ℝ) where
  evaluate w _ := 1 / (1 + quadE a w)

/-- Покомпонентный floor: capability ≥ половины стартовой
(floor согласован со стартовым состоянием). -/
noncomputable def quadFloor (a x : k → ℝ) : Fin 5 → ℝ :=
  fun _ => 1 / (2 * (1 + quadE a x))

/-- ПОЛНЫЙ StepCert для оптимального quad-шага:
спуск + качество + бюджет, всё зависимо. -/
noncomputable def quadStepCert (a x : k → ℝ)
    (hx : quadGrad a x ≠ 0) :
    StepCert (fun w => quadE a w) (quadMeasured a) (quadFloor a x) 0
      x (x - quadGrad a x) 0 0 where
  spend := 0
  trans := quadCert a x hx
  hdec := by norm_num
  quality := by
    intro i
    have h0 : quadE a (x - quadGrad a x) = 0 :=
      quadCert_hits_optimum a x
    have hpos : (0:ℝ) < quadE a x :=
      (quadCert a x hx).objectiveDrop_pos
    simp only [quadFloor, quadMeasured, h0]
    field_simp
    linarith



/-- Траектория: t=0 — старт, t≥1 — оптимум. -/
def qf (a x : k → ℝ) : ℕ → (k → ℝ) :=
  fun t => Nat.rec x (fun _ _ => x - quadGrad a x) t

omit [Nonempty k] in
theorem quadE_nonneg (a w : k → ℝ) : 0 ≤ quadE a w := by
  unfold quadE
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · norm_num

/-- ПРОГОН КАПСТОНА: certified_loop_strict на одношаговой
quad-траектории — энергия после сертифицированного шага
СТРОГО меньше. -/
theorem quad_loop_strict (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    quadE a (qf a x 1) < quadE a (qf a x 0) := by
  have hnn : 0 ≤ quadE a x := quadE_nonneg a x
  have h₀ : Hagi.Unified.LinkedQVec.FloorKept
      (quadMeasured a) (qf a x 0) (quadFloor a x) := by
    intro i
    show 1 / (2 * (1 + quadE a x)) ≤ 1 / (1 + quadE a x)
    have h1 : (0:ℝ) < 1 + quadE a x := by linarith
    have h2 : (0:ℝ) < 2 * (1 + quadE a x) := by linarith
    rw [div_le_div_iff₀ h2 h1]
    linarith
  have main := Hagi.Unified.CertifiedLoop.certified_loop_strict
    (fun w => quadE a w) (quadMeasured a) (quadFloor a x) 0
    (qf a x) (fun _ => 0) (fun _ => quadE a x) 1
    h₀ (le_refl 0)
    (fun t => match t with
      | ⟨0, _⟩ => quadStepCert a x hx
      | ⟨k + 1, h⟩ => nomatch h)
    (fun t => by
      have ht : t = 0 := Subsingleton.elim _ _
      subst ht
      rfl)
    (by norm_num)
  exact main.1

end Hagi.Unified.LoopInstances

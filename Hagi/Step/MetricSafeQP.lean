/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# SafeQP в метрике M

Проекция кандидата d₀ на допустимое множество
`⟪g_i, d⟫ ≥ −ε_i` в метрике d ↦ ‖A d‖ (симметричная
положительно определённая M = AᵀA при самосопряжённом
положительном A).

Существование и единственность сводятся к евклидову SafeQP
заменой координат y = A d: M-проекция d* = A⁻¹ y*, где y* —
евклидова проекция A d₀ на transported-множество с
градиентами (A⁻¹)† g_i.

Утверждений о спуске для исходной цели здесь нет:
метрическая геометрия и геометрия цели независимы —
условие спуска остаётся явной посылкой.
-/

open Real Finset InnerProductSpace InnerProduct

namespace Hagi.MetricSafeQP

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {K : Type*} [Fintype K]

/-- M-метрика, заданная невырожденным носителем A:
‖d − e‖_M := ‖A (d − e)‖. -/
def mDist (A : X ≃L[ℝ] X) (d e : X) : ℝ := ‖A (d - e)‖

/-- Транспортированные градиенты: (A⁻¹)† g_i. -/
noncomputable def transportedGrad (A : X ≃L[ℝ] X) (g : K → X) : K → X :=
  fun i => ((A.symm : X →L[ℝ] X)†) (g i)

/-- Ключевой транспорт: в координатах y = A d допустимость
задаётся транспонированными градиентами (A⁻¹)† g_i:
y ∈ safeSet(transportedGrad) ↔ A⁻¹ y ∈ safeSet g. -/
theorem inner_transport (A : X ≃L[ℝ] X) (g : K → X) (eps : K → ℝ)
    (y : X) :
    y ∈ Hagi.safeSet (transportedGrad A g) eps ↔
      A.symm y ∈ Hagi.safeSet g eps := by
  unfold transportedGrad Hagi.safeSet
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    have h1 := h i
    have hid : ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ
        = ⟪g i, A.symm y⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)
    rwa [hid] at h1
  · intro h i
    have h1 := h i
    have hid : ⟪g i, A.symm y⟫_ℝ
        = ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)).symm
    rwa [hid] at h1

/-- mDist в координатах y = A d — евклидово расстояние. -/
theorem mDist_eq (A : X ≃L[ℝ] X) (e d0 : X) :
    mDist A e d0 = dist (A e) (A d0) := by
  unfold mDist
  have h1 : e - d0 = A.symm (A e) - A.symm (A d0) := by
    rw [A.symm_apply_apply, A.symm_apply_apply]
  rw [h1, A.map_sub]
  simp only [A.apply_symm_apply, A.apply_symm_apply]
  simp [dist_eq_norm]

/-- Существование и единственность M-проекции: при
неотрицательных ε и невырожденном A M-проекция
существует и единственна — сведение к евклидову SafeQP
в координатах y = A d. -/
theorem mProject_exists_unique (A : X ≃L[ℝ] X)
    (g : K → X) (eps : K → ℝ) (heps : ∀ i, 0 ≤ eps i) (d0 : X) :
    ∃! d : X, d ∈ Hagi.safeSet g eps ∧
      ∀ e ∈ Hagi.safeSet g eps,
        mDist A d d0 ≤ mDist A e d0 := by
  obtain ⟨y, ⟨hy, hymin⟩, hyuni⟩ :=
    Hagi.safeQP_exists_unique (transportedGrad A g) (A d0) eps heps
  have hdy : mDist A (A.symm y) d0 = dist y (A d0) := by
    rw [mDist_eq A (A.symm y) d0, A.apply_symm_apply]
  refine ⟨A.symm y, ⟨?_, ?_⟩, ?_⟩
  · exact (inner_transport A g eps y).mp hy
  · intro e he
    have hAe : A e ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A e)).mpr
        (show A.symm (A e) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hmin := hymin (A e) hAe
    have hde : mDist A e d0 = dist (A e) (A d0) := mDist_eq A e d0
    rw [hdy, hde]
    exact hmin
  · intro d ⟨hd, hdmin⟩
    have hAd : A d ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A d)).mpr
        (show A.symm (A d) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hAmin : ∀ z ∈ Hagi.safeSet (transportedGrad A g) eps,
        dist (A d) (A d0) ≤ dist z (A d0) := by
      intro z hz
      have hz' : A.symm z ∈ Hagi.safeSet g eps :=
        (inner_transport A g eps z).mp hz
      have hmin := hdmin (A.symm z) hz'
      have hz1 : mDist A (A.symm z) d0 = dist z (A d0) := by
        rw [mDist_eq A (A.symm z) d0, A.apply_symm_apply]
      have hd1 : mDist A d d0 = dist (A d) (A d0) := mDist_eq A d d0
      rw [hd1, hz1] at hmin
      exact hmin
    have heq : A d = y := hyuni (A d) ⟨hAd, hAmin⟩
    calc d = A.symm (A d) := (A.symm_apply_apply d).symm
      _ = A.symm y := by rw [heq]

end Hagi.MetricSafeQP

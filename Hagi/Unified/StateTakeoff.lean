/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGITrunc

set_option linter.style.header false

/-!
# Takeoff ПОЛЯ состояния (аудит R265, проблема №1)

Рецензия: `cap : ℕ → ℝ` в MasterHAGI — отдельная
последовательность, никак не связанная с полем
`capability` состояний; теорема роста ничего не говорит о
состояниях.

Этот модуль закрывает разрыв минимально честным способом:
при полной связи состояний (FullCycleRefinement на каждом
шаге) шаг роста возможностей ВЫВОДИТСЯ из устройства цикла —
`capability S(t+1) = capability S(t) + growGain S(t)`
(grow добавляет заявленный выигрыш, merge/joint/compress
канал не меняют). Остаётся измеряемой только динамика фронта
D и коэффициент γ (как и должно быть).

Никакой вывод самих growGain/D-посылок не утверждается —
это по-прежнему h_emp_ гипотезы, теперь о полях состояния.
-/

open Real Finset InnerProductSpace Hagi Hagi.Foundations

namespace Hagi.StateTakeoff

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Полная связь состояний даёт шаг канала возможностей:
grow добавляет growGain, merge/joint/compress канал
сохраняют. -/
theorem full_cycle_capability_step (S S' : Hagi.GenState X)
    (hfull : FullCycleRefinement S S') :
    S'.toGrowthState.capability
      = S.toGrowthState.capability + S.toGrowthState.growGain := by
  obtain ⟨heq, _⟩ := hfull
  rw [heq]
  simp [grow, merge, joint, compress]

/-- **Takeoff поля capability состояний**: для
последовательности состояний, где каждый переход — полный
составной цикл (FullCycleRefinement), с измеренными
посылками фронта (γ·D_t ≤ growGain_t, динамика D, потолок и
порог β — все h_emp_), поле capability растёт
экспоненциально: capability(S_T) ≥ (1+α)^T·capability(S_0).

Разница с MasterHAGI_trunc: h_emp_step здесь НЕ посылка —
он выводится из устройства цикла (full_cycle_capability_step);
C-канал — это само поле состояния. -/
theorem state_capability_takeoff (S : ℕ → Hagi.GenState X)
    (alpha gamma rho beta : ℝ) (xi D : ℕ → ℝ) (T : ℕ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < (S 0).toGrowthState.capability)
    (hfull : ∀ t < T, FullCycleRefinement (S t) (S (t + 1)))
    (h_emp_cone0 : alpha / gamma * (S 0).toGrowthState.capability
      ≤ D 0)
    (h_emp_gain_prod : ∀ t < T, gamma * D t
      ≤ (S t).toGrowthState.growGain)
    (h_emp_dyn : ∀ t < T, rho * D t
        + beta * (S t).toGrowthState.capability - xi t
      ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, (S (t + 1)).toGrowthState.capability
      ≤ (1 + alpha) * (S t).toGrowthState.capability)
    (h_emp_beta : ∀ t < T, alpha / gamma * ((1 + alpha) - rho)
        + xi t / (S t).toGrowthState.capability ≤ beta) :
    (S 0).toGrowthState.capability * (1 + alpha) ^ T
      ≤ (S T).toGrowthState.capability := by
  -- the step premise is DERIVED, not assumed
  have hstep : ∀ t < T, (S (t + 1)).toGrowthState.capability
      = (S t).toGrowthState.capability
        + (S t).toGrowthState.growGain :=
    fun t ht => full_cycle_capability_step (S t) (S (t + 1))
      (hfull t ht)
  exact Hagi.sustained_takeoff_trunc
    (fun t => (S t).toGrowthState.capability)
    (fun t => (S t).toGrowthState.growGain)
    D alpha gamma rho beta xi T hα hγ hρ hC0 h_emp_cone0 hstep
    h_emp_gain_prod h_emp_dyn h_emp_C_cap h_emp_beta

/-- **FullCycleRefinement как основание CorePremises** (аудит,
проблема №2): старая конъюнкта h_cycle связывает только
energy/protectedRisk/budget; при полной связи состояний она
ВЫВОДИТСЯ из FullCycleRefinement (full_cycle_field_eq), а
остальные 14 конъюнкт — те же измеряемые посылки стадий. -/
theorem corePremises_of_full_refinement (S S' : Hagi.GenState X)
    (epsQ : ℝ) (w : Fin 5 → ℝ)
    (hfull : FullCycleRefinement S S')
    (h1 : 0 ≤ S.toGrowthState.gap)
    (h2 : S.toGrowthState.growEnergy
      ≤ S.toGrowthState.energy - S.toGrowthState.growGain)
    (h3 : S.toGrowthState.mergeEnergy
      ≤ S.toGrowthState.growEnergy - S.toGrowthState.gap)
    (h4 : 0 < S.toGrowthState.sp.L)
    (h5 : S.toGrowthState.sp.eta ≤ 1 / S.toGrowthState.sp.L)
    (h6 : 0 ≤ S.toGrowthState.sp.eta)
    (h7 : ‖S.toGrowthState.stepDir‖ ^ 2
      ≤ ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ)
    (h8 : S.toGrowthState.jointEnergy
      ≤ S.toGrowthState.mergeEnergy
        - S.toGrowthState.sp.eta
          * ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ
        + S.toGrowthState.sp.L * S.toGrowthState.sp.eta ^ 2
          * ‖S.toGrowthState.stepDir‖ ^ 2 / 2)
    (h9 : 0 ≤ S.toGrowthState.sp.kappa)
    (h10 : 0 ≤ S.toGrowthState.sp.s)
    (h11 : 0 ≤ S.toGrowthState.quantErr)
    (h12 : S.toGrowthState.quantErr ≤ 1 / 2)
    (h13 : S.toGrowthState.compressEnergy - S.toGrowthState.jointEnergy
      ≤ S.toGrowthState.sp.kappa * S.toGrowthState.sp.s
        * S.toGrowthState.quantErr)
    (h15 : Qgen S.gen w - epsQ ≤ Qgen S'.gen w) :
    CorePremises S S' epsQ w := by
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, ?_, h15⟩
  exact full_cycle_field_eq hfull

end Hagi.StateTakeoff

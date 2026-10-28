import Hagi.Unified.MasterHAGI
import Hagi.Unified.DerivAlong

/-!
# CorePremisesDerived — премисы стадий как ТЕОРЕМЫ (аудит v6, шаг 1)

Аудит v6: «Подключить DerivAlong к CorePremises, чтобы хотя
бы для joint и compress премисы стали теоремами».

Конъюнкт 8 (h_emp_smooth) и конъюнкт 13 (h_emp_lip) набора
CorePremises — свободные поля effects.jointEnergy /
compressEnergy. Здесь показано: при ОПЕРАЦИОНАЛЬНЫХ
определениях (jointEnergy := E(params − η•stepDir) для
реальной L-гладкой функции потерь E; compressEnergy :=
E(gridQ Δ x) при κ-ограниченном градиенте, quantErr —
фактическая ошибка сетки, s = 1) оба конъюнкта ВЫВОДЯТСЯ из
свойств E (DerivAlong). Упаковка
core_premises_operational_scalar: для скалярных состояний
(X = ℝ) CorePremises держится на структурных посылках —
две «эмпирические» стали теоремами.
-/

namespace Hagi.Unified

open InnerProductSpace

/-- КОНЪЮНКТ 8 (h_emp_smooth) КАК ТЕОРЕМА (общий X):
jointEnergy ОПРЕДЕЛЕНА как энергия реального шага
E(params − η•stepDir) с L-гладким градиентом E и
направленной производной ⟨grad, stepDir⟩ ⟹ эмпирическая
предпосылка гладкости стадии joint ВЫВОДИТСЯ
(DerivAlong.core_premises_joint_operational). -/
theorem conj8_h_emp_smooth_derived {X : Type}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (E : X → ℝ) (S : Hagi.System.GrowthState X)
    (hdiff : ∀ w : X, HasFDerivAt E (fderiv ℝ E w) w)
    (hsmooth : ∀ x y : X, ‖fderiv ℝ E y - fderiv ℝ E x‖
      ≤ S.sp.L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E
      (S.params + t • (-(S.sp.eta)•S.stepDir))
      (-(S.sp.eta)•S.stepDir))
    (hgrad : fderiv ℝ E S.params S.stepDir = ⟪S.grad, S.stepDir⟫_ℝ)
    (heta : 0 ≤ S.sp.eta)
    (hE : E S.params ≤ S.effects.mergeEnergy)
    (hdef : S.effects.jointEnergy
      = E (S.params - S.sp.eta • S.stepDir)) :
    S.effects.jointEnergy
      ≤ S.effects.mergeEnergy
        - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
        + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2 := by
  have h := core_premises_joint_operational
    (E := E) (S := S) (hdiff := hdiff) (hsmooth := hsmooth)
    (hgcont := hgcont) (hgrad := hgrad) (heta := heta)
    (hE := hE)
  rw [hdef]
  exact h

/-- КОНЪЮНКТ 13 (h_emp_lip) КАК ТЕОРЕМА (X = ℝ):
compressEnergy ОПРЕДЕЛЕНА как энергия реально
квантованных весов E(gridQ Δ x), E имеет κ-ограниченный
градиент, jointEnergy доминирует E(x), quantErr — фактическая
ошибка сетки, s = 1 ⟹ предпосылка сжатия ВЫВОДИТСЯ
(DerivAlong.core_premises_compress_operational). -/
theorem conj13_h_emp_lip_derived
    (E : ℝ → ℝ) (kappa : ℝ)
    (hdiff : ∀ x : ℝ, HasFDerivAt E (fderiv ℝ E x) x)
    (hnorm : ∀ x : ℝ, ‖fderiv ℝ E x‖ ≤ kappa)
    (Δ : ℝ) (hΔ : 0 < Δ) (x jointEnergy : ℝ)
    (hjoint : E x ≤ jointEnergy)
    (compressEnergy : ℝ)
    (hdef : compressEnergy = E (Hagi.Energy.gridQ Δ hΔ x))
    (quantErr : ℝ)
    (hq : quantErr = |x - Hagi.Energy.gridQ Δ hΔ x|) :
    compressEnergy - jointEnergy ≤ kappa * 1 * quantErr := by
  have hbr := core_premises_compress_operational E kappa hdiff
    hnorm Δ hΔ x jointEnergy hjoint
  rw [hdef, hq]
  exact hbr

/-- СВЕДЕНИЕ CorePremises (аудит v6, шаг 1, скалярный
случай): при операциональных определениях jointEnergy
(реальный шаг L-гладкой функции) и compressEnergy (реальное
квантование gridQ, κ-ограниченный градиент, фактическая
ошибка сетки, s = 1) конъюнкты 8 и 13 — ТЕОРЕМЫ; CorePremises
держится на структурных посылках (бухгалтерия стадий,
SafeQP-окно, связка S' = compress∘joint∘merge∘grow,
ген-толерантность). -/
theorem core_premises_operational_scalar
    (S S' : GenState ℝ) (epsQ : ℝ) (w : Fin 5 → ℝ)
    -- структурные посылки (конъюнкты 1–7, 9–12, 14, 15)
    (hgap : 0 ≤ S.toGrowthState.gap)
    (h_emp_grow : S.toGrowthState.effects.growEnergy
      ≤ S.toGrowthState.energy - S.toGrowthState.effects.growGain)
    (h_emp_merge : S.toGrowthState.effects.mergeEnergy
      ≤ S.toGrowthState.effects.growEnergy - S.toGrowthState.gap)
    (hL : 0 < S.toGrowthState.sp.L)
    (heta : S.toGrowthState.sp.eta ≤ 1 / S.toGrowthState.sp.L)
    (heta0 : 0 ≤ S.toGrowthState.sp.eta)
    (hdescent : ‖S.toGrowthState.stepDir‖ ^ 2
      ≤ ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ)
    (hkappa : 0 ≤ S.toGrowthState.sp.kappa)
    (hs : 0 ≤ S.toGrowthState.sp.s)
    (hdn : 0 ≤ S.toGrowthState.effects.quantErr)
    (h_emp_dist : S.toGrowthState.effects.quantErr ≤ 1 / 2)
    (heq : S'.toGrowthState
      = compress (joint (merge (grow S.toGrowthState))))
    (hgenq : ∀ i, Qvec S'.gen i ≤ Qvec S.gen i + epsQ)
    (h_emp_G : Qgen S.gen w - epsQ ≤ Qgen S'.gen w)
    -- операциональные определения (конъюнкты 8, 13 → теоремы)
    (E : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, HasFDerivAt E (fderiv ℝ E x) x)
    (hsmooth : ∀ x y : ℝ, ‖fderiv ℝ E y - fderiv ℝ E x‖
      ≤ S.toGrowthState.sp.L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E
      (S.toGrowthState.params
        + t • (-(S.toGrowthState.sp.eta)•S.toGrowthState.stepDir))
      (-(S.toGrowthState.sp.eta)•S.toGrowthState.stepDir))
    (hgrad : fderiv ℝ E S.toGrowthState.params
        S.toGrowthState.stepDir
      = ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ)
    (hEmerge : E S.toGrowthState.params
      ≤ S.toGrowthState.effects.mergeEnergy)
    (hjointE : E S.toGrowthState.params
      ≤ S.toGrowthState.effects.jointEnergy)
    (hjointdef : S.toGrowthState.effects.jointEnergy
      = E (S.toGrowthState.params
        - S.toGrowthState.sp.eta • S.toGrowthState.stepDir))
    (hnorm : ∀ x : ℝ, ‖fderiv ℝ E x‖ ≤ S.toGrowthState.sp.kappa)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hcompdef : S.toGrowthState.effects.compressEnergy
      = E (Hagi.Energy.gridQ Δ hΔ S.toGrowthState.params))
    (hquantdef : S.toGrowthState.effects.quantErr
      = |S.toGrowthState.params
        - Hagi.Energy.gridQ Δ hΔ S.toGrowthState.params|)
    (hs1 : S.toGrowthState.sp.s = 1) :
    CorePremises S S' epsQ w := by
  have h8 := conj8_h_emp_smooth_derived E S.toGrowthState hdiff
    hsmooth hgcont hgrad heta0 hEmerge hjointdef
  have h13 := conj13_h_emp_lip_derived E S.toGrowthState.sp.kappa
    hdiff hnorm Δ hΔ S.toGrowthState.params
    S.toGrowthState.effects.jointEnergy hjointE
    S.toGrowthState.effects.compressEnergy hcompdef
    S.toGrowthState.effects.quantErr hquantdef
  have h13' : S.toGrowthState.effects.compressEnergy
      - S.toGrowthState.effects.jointEnergy
      ≤ S.toGrowthState.sp.kappa * S.toGrowthState.sp.s
        * S.toGrowthState.effects.quantErr := by
    rw [hs1]
    exact h13
  exact ⟨hgap, h_emp_grow, h_emp_merge, hL, heta, heta0, hdescent,
    h8, hkappa, hs, hdn, h_emp_dist, h13', heq, hgenq, h_emp_G⟩


/-- КАПСТОУН-МОСТ (аудит v6, шаг 1): операциональный
MasterHAGICore — при операциональных определениях энергий
стадий (реальный шаг L-гладкой функции потерь, реальное
квантование gridQ) эмпирические конъюнкты 8/13 CorePremises
ВЫВОДЯТСЯ, и одностадийный мастер-результат (убывание Φ_HAGI
с точностью до λ·riskSpend + ν·ε_Q, точная бюджетная
бухгалтерия) следует из структурных посылок и свойств
РЕАЛЬНОЙ функции потерь, а не из постулируемых полей. -/
theorem MasterHAGICoreOperational
    (S S' : GenState ℝ) (lam nu Qtarget epsQ : ℝ)
    (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu) (h_epsQ : 0 ≤ epsQ)
    (hgap : 0 ≤ S.toGrowthState.gap)
    (h_emp_grow : S.toGrowthState.effects.growEnergy
      ≤ S.toGrowthState.energy - S.toGrowthState.effects.growGain)
    (h_emp_merge : S.toGrowthState.effects.mergeEnergy
      ≤ S.toGrowthState.effects.growEnergy - S.toGrowthState.gap)
    (hL : 0 < S.toGrowthState.sp.L)
    (heta : S.toGrowthState.sp.eta ≤ 1 / S.toGrowthState.sp.L)
    (heta0 : 0 ≤ S.toGrowthState.sp.eta)
    (hdescent : ‖S.toGrowthState.stepDir‖ ^ 2
      ≤ ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ)
    (hkappa : 0 ≤ S.toGrowthState.sp.kappa)
    (hs : 0 ≤ S.toGrowthState.sp.s)
    (hdn : 0 ≤ S.toGrowthState.effects.quantErr)
    (h_emp_dist : S.toGrowthState.effects.quantErr ≤ 1 / 2)
    (heq : S'.toGrowthState
      = compress (joint (merge (grow S.toGrowthState))))
    (hgenq : ∀ i, Qvec S'.gen i ≤ Qvec S.gen i + epsQ)
    (h_emp_G : Qgen S.gen w - epsQ ≤ Qgen S'.gen w)
    (E : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, HasFDerivAt E (fderiv ℝ E x) x)
    (hsmooth : ∀ x y : ℝ, ‖fderiv ℝ E y - fderiv ℝ E x‖
      ≤ S.toGrowthState.sp.L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E
      (S.toGrowthState.params
        + t • (-(S.toGrowthState.sp.eta)•S.toGrowthState.stepDir))
      (-(S.toGrowthState.sp.eta)•S.toGrowthState.stepDir))
    (hgrad : fderiv ℝ E S.toGrowthState.params
        S.toGrowthState.stepDir
      = ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ)
    (hEmerge : E S.toGrowthState.params
      ≤ S.toGrowthState.effects.mergeEnergy)
    (hjointE : E S.toGrowthState.params
      ≤ S.toGrowthState.effects.jointEnergy)
    (hjointdef : S.toGrowthState.effects.jointEnergy
      = E (S.toGrowthState.params
        - S.toGrowthState.sp.eta • S.toGrowthState.stepDir))
    (hnorm : ∀ x : ℝ, ‖fderiv ℝ E x‖ ≤ S.toGrowthState.sp.kappa)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hcompdef : S.toGrowthState.effects.compressEnergy
      = E (Hagi.Energy.gridQ Δ hΔ S.toGrowthState.params))
    (hquantdef : S.toGrowthState.effects.quantErr
      = |S.toGrowthState.params
        - Hagi.Energy.gridQ Δ hΔ S.toGrowthState.params|)
    (hs1 : S.toGrowthState.sp.s = 1) :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - (verify S.toGrowthState).decrease
        + lam * (verify S.toGrowthState).riskSpend + nu * epsQ
    ∧ S'.toGrowthState.budget
      = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend := by
  exact MasterHAGICore S S' lam nu Qtarget epsQ w hlam hnu h_epsQ
    (core_premises_operational_scalar S S' epsQ w hgap h_emp_grow
      h_emp_merge hL heta heta0 hdescent hkappa hs hdn h_emp_dist heq
      hgenq h_emp_G E hdiff hsmooth hgcont hgrad hEmerge hjointE
      hjointdef hnorm Δ hΔ hcompdef hquantdef hs1)

end Hagi.Unified

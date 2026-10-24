import Hagi.Optimization.MirrorDescent
-- Мост Cortex (2610.20399 §3.3) ↔ MirrorDescent (KL-дистилляция).
open Hagi.Optimization

namespace Hagi.Model

/-!
Мост Cortex (arXiv 2610.20399 §3.3) ↔ MirrorDescent:
KL-дистилляция (учитель с контекстом γ, студент σ) —
это зеркальное тождество; учитель-Гиббс — единственный
минимум student objective (вариационный принцип).
-/

/-- КЛ-ДИСТИЛЛЯЦИЯ = зеркальное тождество: расхождение студента
σ от учителя γ (Гиббс по ℓ, температуре T, приоре ρ₀):
T·KL(σ‖γ) = ⟨σ,ℓ⟩ + T·KL(σ‖ρ₀) + T·log Z. -/
theorem context_distillation_identity
    {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (σ : V → ℝ) (hσ : ∀ v, 0 < σ v) (hσ1 : ∑ v, σ v = 1) :
    T * (∑ v, σ v * Real.log (σ v
        / mirrorStep ρ₀ ℓ T v))
      = (∑ v, σ v * ℓ v)
        + T * (∑ v, σ v * Real.log (σ v / ρ₀ v))
        + T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)) :=
  mirror_descent_identity ρ₀ ℓ T hT hρ₀ σ hσ hσ1

/-- ВАРИАЦИОННЫЙ ПРИНЦИП ГИББСА (ядро дистилляции):
для любого студента-распределения σ
⟨σ,ℓ⟩ + T·KL(σ‖ρ₀) ≥ −T·log Z, т.е. учитель-Гиббс
достигает минимума free energy; единственность минимума —
равенство ⟺ KL(σ‖γ)=0. Нижняя граница следует из
тождества и KL ≥ 0. -/
theorem gibbs_variational_floor
    {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (σ : V → ℝ) (hσ : ∀ v, 0 < σ v) (hσ1 : ∑ v, σ v = 1) :
    -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T))
      ≤ (∑ v, σ v * ℓ v)
        + T * (∑ v, σ v * Real.log (σ v / ρ₀ v)) := by
  have h := context_distillation_identity ρ₀ ℓ T hT hρ₀ σ hσ hσ1
  have hkl : (0:ℝ) ≤ ∑ v, σ v * Real.log (σ v
      / mirrorStep ρ₀ ℓ T v) := by
    apply Hagi.Probability.finite_kl_nonneg
    · exact hσ
    · exact hσ1
    · intro v
      exact Hagi.Optimization.mirrorStep_pos ρ₀ ℓ T hT hρ₀ v
    · exact Hagi.Optimization.mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have h' := mul_nonneg hT.le hkl
  linarith [h, h']


/-- ЕДИНСТВЕННОСТЬ МИНИМУМА дистилляции (в KL-форме):
студент σ достигает вариационного пола
⟨σ,ℓ⟩+T·KL(σ‖ρ₀) = −T·log Z (минимума, который реализует
учитель-Гиббс γ) тогда и только тогда, когда KL(σ‖γ) = 0,
т.е. расхождение студента с учителем нулевое. -/
theorem distillation_floor_attained_iff_kl_zero
    {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (σ : V → ℝ) (hσ : ∀ v, 0 < σ v) (hσ1 : ∑ v, σ v = 1) :
    ((∑ v, σ v * ℓ v)
        + T * (∑ v, σ v * Real.log (σ v / ρ₀ v))
      = -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)))
    ↔ (∑ v, σ v * Real.log (σ v
        / mirrorStep ρ₀ ℓ T v)) = 0 := by
  have hid := context_distillation_identity ρ₀ ℓ T hT hρ₀ σ hσ hσ1
  constructor <;> intro h
  · nlinarith
  · nlinarith


end Hagi.Model

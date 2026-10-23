/-
MirrorDescent: единый вариационный принцип.

Зеркальный шаг с энтропийным зеркалом: для любой ссылки ρ₀
(равномерной в Гиббсе, предыдущих весов в MWU/Hedge,
априорных убеждений в Active Inference) решение задачи
argmin_{ρ ∈ Δ} { ⟨ρ, ℓ⟩ + T·KL(ρ‖ρ₀) } — мера
γ_v ∝ ρ₀_v·e^{−ℓ_v/T}: Гиббс, MWU-обновление и EFE-минимум
AIF — одно и то же аналитическое решение с минимальным
значением −T·log Z. Тождество:
T·KL(ρ‖γ) = ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) + T·log Z.
-/
import Hagi.Probability.GibbsInfoCore

namespace Hagi.Optimization

open Finset

/-- Зеркальный шаг (энтропийное зеркало): γ_v = ρ₀_v·e^{−ℓ_v/T}/Z,
где Z = Σ_v ρ₀_v·e^{−ℓ_v/T} — нормировка. -/
noncomputable def mirrorStep {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) : V → ℝ :=
  fun v => ρ₀ v * Real.exp (-(ℓ v)/T)
    / ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)

/-- Позитивность зеркального шага при T > 0 и ρ₀ > 0. -/
theorem mirrorStep_pos {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (v : V) :
    0 < mirrorStep ρ₀ ℓ T v := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  unfold mirrorStep
  exact div_pos (mul_pos (hρ₀ v) (Real.exp_pos _)) hZpos

/-- Зеркальный шаг — распределение: сумма равна 1. -/
theorem mirrorStep_sum_one {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    ∑ v, mirrorStep ρ₀ ℓ T v = 1 := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  unfold mirrorStep
  rw [← Finset.sum_div]
  exact div_self hZpos.ne'

/-- ТОЖДЕСТВО ЗЕРКАЛЬНОГО ШАГА: для γ = mirrorStep ρ₀ ℓ T и
любого ρ ∈ Δ:
T·KL(ρ‖γ) = ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) + T·log Z.
Следствие неотрицательности KL: ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀)
минимизируется мерой γ, минимум равен −T·log Z —
Гиббс (ρ₀ равномерна), MWU-обновление (ρ₀ = предыдущие
веса) и EFE-минимум AIF — одно и то же решение. -/
theorem mirror_descent_identity {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    T * (∑ v, ρ v * Real.log (ρ v
        / mirrorStep ρ₀ ℓ T v))
      = (∑ v, ρ v * ℓ v)
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v))
        + T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)) := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  set Z := ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) with hZ
  have hlogγ : ∀ v : V, Real.log (mirrorStep ρ₀ ℓ T v)
      = Real.log (ρ₀ v) - ℓ v / T - Real.log Z := by
    intro v
    unfold mirrorStep
    have hnum : (0:ℝ) < ρ₀ v * Real.exp (-(ℓ v)/T) :=
      mul_pos (hρ₀ v) (Real.exp_pos _)
    rw [Real.log_div hnum.ne' hZpos.ne',
      Real.log_mul (hρ₀ v).ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  -- почленное разложение под суммой
  have hsplit : ∀ v : V,
      T * (ρ v * Real.log (ρ v / mirrorStep ρ₀ ℓ T v))
      = ρ v * ℓ v
        + T * (ρ v * Real.log (ρ v / ρ₀ v))
        + ρ v * (T * Real.log Z) := by
    intro v
    rw [Real.log_div (hρ v).ne' (hγpos v).ne',
      Real.log_div (hρ v).ne' (hρ₀ v).ne', hlogγ v]
    field_simp
    ring
  -- суммирование трёх частей
  rw [Finset.mul_sum,
    Finset.sum_congr rfl (fun v _ => hsplit v),
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum,
    ← Finset.sum_mul, hρ1, one_mul]

/-- НИЖНЯЯ ГРАНЬ ЗЕРКАЛЬНОГО ШАГА (унификация): для любого
ρ ∈ Δ выполнено ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) ≥ −T·log Z, где
Z = Σ ρ₀·e^{−ℓ/T}; равенство достигается на γ = mirrorStep:
единая нижняя грань для меры Гиббса, MWU/Hedge-потенциала
и свободной энергии EFE из Active Inference. -/
theorem mirror_descent_floor {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T))
      ≤ (∑ v, ρ v * ℓ v)
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
  classical
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hKL : (0:ℝ) ≤ ∑ v, ρ v * Real.log (ρ v
      / mirrorStep ρ₀ ℓ T v) :=
    finite_kl_nonneg ρ (mirrorStep ρ₀ ℓ T) hρ hρ1 hγpos hγ1
  have hid := mirror_descent_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  have hTnn : (0:ℝ) ≤ T := le_of_lt hT
  have hTKL : (0:ℝ) ≤ T * (∑ v, ρ v * Real.log (ρ v
      / mirrorStep ρ₀ ℓ T v)) := mul_nonneg hTnn hKL
  linarith

end Hagi.Optimization

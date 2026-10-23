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
import Hagi.Probability.MWU

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

/-- ДОСТИЖИМОСТЬ ПОЛА ЗЕРКАЛЬНОГО ШАГА: на мере
γ = mirrorStep ρ₀ ℓ T свободная энергия ⟨γ,ℓ⟩+T·KL(γ‖ρ₀)
равна в точности −T·log Z — нижняя грань mirror_descent_floor
достигается: γ — минимизатор вариационной задачи,
полнота унификации Гиббса/MWU/EFE. -/
theorem mirror_descent_attainment {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      + T * (∑ v, mirrorStep ρ₀ ℓ T v
          * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v))
      = -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have h := mirror_descent_identity ρ₀ ℓ T hT hρ₀
    (mirrorStep ρ₀ ℓ T) hγpos hγ1
  have hsum : (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v
        / mirrorStep ρ₀ ℓ T v)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    rw [div_self (hγpos v).ne', Real.log_one, mul_zero]
  rw [hsum, mul_zero] at h
  linarith

/-- МОСТ MWU ↔ ЗЕРКАЛЬНЫЙ СПУСК: hedge-обновление
γ = mirrorStep w ℓ (1/η) — в точности зеркальный шаг с
T = 1/η; комбинируя достижимость пола (F(γ) = −T log Z) с
оценкой нормировки MWU (log Z ≥ −2η⟨ℓ⟩_w при ηℓ ≤ 1/2),
получаем F(γ) ≤ 2⟨ℓ⟩_w: свободная энергия обновлённой смеси
не более удвоенных текущих средних потерь — мост между
экспоненциальными весами и вариационным принципом. -/
theorem hedge_free_energy_step {V : Type*} [Fintype V]
    [Nonempty V] (w ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    (∑ v, mirrorStep w ℓ (1/η) v * ℓ v)
      + (1/η) * (∑ v, mirrorStep w ℓ (1/η) v
          * Real.log (mirrorStep w ℓ (1/η) v / w v))
      ≤ 2 * (∑ v, w v * ℓ v) := by
  -- достижимость: F(γ) = −(1/η)·log Z
  have hT : (0:ℝ) < 1/η := one_div_pos.mpr hη
  have hatt := mirror_descent_attainment w ℓ (1/η) hT hw
  -- MWU-оценка нормировки: log Z ≥ −2η⟨ℓ⟩_w
  have hmwu := mwu_potential_step w ℓ η hw hw1 hℓ hη hsmall
  -- Z в обоих утверждениях совпадает: exp(−ηℓ) = exp(−ℓ/(1/η))
  have hZeq : (∑ v, w v * Real.exp (-(ℓ v)/(1/η)))
      = ∑ v, w v * Real.exp (-(η * ℓ v)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    field_simp
  rw [hZeq] at hatt
  -- F(γ) = (1/η)·(−log Z) ≤ (1/η)·2η⟨ℓ⟩_w = 2⟨ℓ⟩_w
  have hneg : -Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≤ 2 * η * (∑ v, w v * ℓ v) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hneg hT.le
  have hconv : (1/η) * (2 * η * (∑ v, w v * ℓ v))
      = 2 * (∑ v, w v * ℓ v) := by
    field_simp
  have hsplit : (∑ v, mirrorStep w ℓ (1/η) v * ℓ v)
      + (1/η) * (∑ v, mirrorStep w ℓ (1/η) v
          * Real.log (mirrorStep w ℓ (1/η) v / w v))
      = (1/η) * (-Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))) := by
    rw [hatt]
    ring
  rw [hsplit]
  calc (1/η) * (-Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
      ≤ (1/η) * (2 * η * (∑ v, w v * ℓ v)) := hmul
    _ = 2 * (∑ v, w v * ℓ v) := hconv

/-- EFE-ШАГ ACTIVE INFERENCE = ЗЕРКАЛЬНЫЙ ШАГ: при разложении
потерь ℓ = surprise − information gain минимизатор ожидаемой
свободной энергии — мера mirrorStep ρ₀ (s−g) T, и её свободная
энергия равна в точности −T·log Z(s−g): третий член
унификации Гиббс == MWU == EFE. -/
theorem aif_efe_attainment {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ s g : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    (∑ v, mirrorStep ρ₀ (fun v => s v - g v) T v * (s v - g v))
      + T * (∑ v, mirrorStep ρ₀ (fun v => s v - g v) T v
          * Real.log (mirrorStep ρ₀ (fun v => s v - g v) T v
            / ρ₀ v))
      = -T * Real.log (∑ w, ρ₀ w
          * Real.exp (-(s w - g w)/T)) :=
  mirror_descent_attainment ρ₀ (fun v => s v - g v) T hT hρ₀

/-- EFE-ДОМИНИРОВАНИЕ: EFE-шаг не хуже любого убеждения ρ ∈ Δ:
−T·log Z(s−g) ≤ ⟨ρ, s−g⟩ + T·KL(ρ‖ρ₀) — ожидаемая свободная
энергия mirrorStep-убеждения доминируется снизу единой
вариационной гранью (специализация mirror_descent_floor). -/
theorem aif_efe_floor {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ s g : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ w, ρ₀ w * Real.exp (-(s w - g w)/T))
      ≤ (∑ v, ρ v * (s v - g v))
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) :=
  mirror_descent_floor ρ₀ (fun v => s v - g v) T hT hρ₀
    ρ hρ hρ1

/-- ГИББС = ЗЕРКАЛЬНЫЙ ШАГ С РАВНОМЕРНОЙ ССЫЛКОЙ:
вариационная грань Гиббса (R421, gibbs_variational)
выводится из mirror_descent_floor при ρ₀ = 1/n:
-T·log(Σ e^{-ℓ/T}) ≤ ⟨ρ,ℓ⟩ + T·Σ ρ log ρ —
слагаемые T·log n сокращаются: мера Гиббса, MWU и EFE —
три проекции одного зеркального шага. -/
theorem gibbs_from_mirror {V : Type*} [Fintype V] [Nonempty V]
    (ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ v, Real.exp (-(ℓ v)/T))
      ≤ (∑ v, ρ v * ℓ v) + T * (∑ v, ρ v * Real.log (ρ v)) := by
  have hcard : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcardne : ((Fintype.card V : ℝ)) ≠ 0 := ne_of_gt hcard
  have hρ₀pos : ∀ v : V, (0:ℝ) < 1 / (Fintype.card V : ℝ) := by
    intro v; positivity
  have hρ₀1 : ∑ v : V, 1 / (Fintype.card V : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      one_div, mul_inv_cancel₀ hcardne]
  have hfl := mirror_descent_floor
    (fun _ => 1 / (Fintype.card V : ℝ)) ℓ T hT hρ₀pos ρ hρ hρ1
  -- Z = (1/n)·Σ e^{−ℓ/T}
  have hZ : (∑ w, (1 / (Fintype.card V : ℝ))
        * Real.exp (-(ℓ w)/T))
      = (∑ v, Real.exp (-(ℓ v)/T)) / (Fintype.card V : ℝ) := by
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
  -- KL-слагаемое: Σ ρ log(ρ·n) = Σ ρ log ρ + log n
  have hKL : (∑ v, ρ v
        * Real.log (ρ v / (1 / (Fintype.card V : ℝ))))
      = (∑ v, ρ v * Real.log (ρ v))
        + Real.log (Fintype.card V : ℝ) := by
    have hsplit : ∀ v : V, ρ v
        * Real.log (ρ v / (1 / (Fintype.card V : ℝ)))
        = ρ v * Real.log (ρ v)
          + ρ v * Real.log (Fintype.card V : ℝ) := by
      intro v
      have hrw : ρ v / (1 / (Fintype.card V : ℝ))
          = ρ v * (Fintype.card V : ℝ) := by
        field_simp
      rw [hrw, Real.log_mul (hρ v).ne' hcardne]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hρ1, one_mul]
  rw [hKL] at hfl
  -- log Z = log Σ − log n
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(ℓ v)/T) :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hlogZ : Real.log ((∑ v, Real.exp (-(ℓ v)/T))
      / (Fintype.card V : ℝ))
      = Real.log (∑ v, Real.exp (-(ℓ v)/T))
        - Real.log (Fintype.card V : ℝ) :=
    Real.log_div hZpos.ne' hcardne
  rw [hZ, hlogZ] at hfl
  nlinarith [hfl]

/-- ОДНОШАГОВОЕ ТОЖДЕСТВО ПРОГРЕССА зеркального спуска:
для любого ρ ∈ Δ и шага γ = mirrorStep ρ₀ ℓ T:
⟨ρ,ℓ⟩ − F(γ) = T·(KL(ρ‖γ) − KL(ρ‖ρ₀)), где F(γ) — свободная
энергия γ (достигаемый пол): превышение любых потерь над
полом равно приросту расстояния Брегмана до цели ρ — база
телескопирования регрета MWU/Hedge. -/
theorem mirror_progress_identity {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    (∑ v, ρ v * ℓ v)
      - ((∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
          + T * (∑ v, mirrorStep ρ₀ ℓ T v
              * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)))
      = T * ((∑ v, ρ v * Real.log (ρ v
              / mirrorStep ρ₀ ℓ T v))
          - (∑ v, ρ v * Real.log (ρ v / ρ₀ v))) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hid := mirror_descent_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  rw [hatt]
  linarith

/-- Итерированные зеркальные веса: w₀ = ρ₀,
w_{k+1} = mirrorStep w_k (ℓ_k) T — траектория hedge/MWU
при постоянной температуре T. -/
noncomputable def mirrorIterate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) : ℕ → V → ℝ
  | 0 => ρ₀
  | k+1 => mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T

/-- Позитивность траектории сохраняется. -/
theorem mirrorIterate_pos {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (k : ℕ) :
    ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v := by
  induction k with
  | zero => exact hρ₀
  | succ n ih =>
      intro v
      unfold mirrorIterate
      exact mirrorStep_pos _ _ T hT ih v

/-- Траектория остаётся распределением. -/
theorem mirrorIterate_sum_one {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (k : ℕ) :
    ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 := by
  induction k with
  | zero => exact hρ₀1
  | succ n ih =>
      unfold mirrorIterate
      exact mirrorStep_sum_one _ _ T hT
        (mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n)

/-- ОДНОШАГОВОЕ НЕРАВЕНСТВО РЕГРЕТА: обновлённые веса γ
проигрывают цели ρ* не более убыли T·KL:
⟨γ,ℓ⟩ − ⟨ρ*,ℓ⟩ ≤ T·(KL(ρ*‖ρ₀) − KL(ρ*‖γ)) — следствие
тождества прогресса и неотрицательности KL(γ‖ρ₀). -/
theorem mirror_step_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) - (∑ v, ρ v * ℓ v)
      ≤ T * ((∑ v, ρ v * Real.log (ρ v / ρ₀ v))
        - (∑ v, ρ v * Real.log (ρ v
            / mirrorStep ρ₀ ℓ T v))) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hklγ : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    have h := finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀
      hγpos hγ1 hρ₀ hρ₀1
    exact mul_nonneg (le_of_lt hT) h
  -- hprog: ⟨ρ,ℓ⟩ − (⟨γ,ℓ⟩ + T·KL(γ‖ρ₀)) = T(KL(ρ‖γ) − KL(ρ‖ρ₀))
  have hprog := mirror_progress_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  linarith

/-- ТЕЛЕСКОПИРОВАННЫЙ РЕГРЕТ HEDGE/MWU: суммарное превышение
потерь обновляемых весов w_{k+1} = mirrorStep w_k ℓ_k T над
любой фиксированной целью ρ* ≤ T·KL(ρ*‖w₀) — KL-убыль
телескопирует, регрет ограничен начальным расстоянием
Брегмана: полная формализация regret-границы зеркального
спуска (база MWU/Hedge-анализа). -/
theorem mirror_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1)
    (n : ℕ) :
    ∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
  -- индукция по n с одношаговым неравенством
  have key : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v)))
      + T * (∑ v, ρ v * Real.log (ρ v
          / mirrorIterate ρ₀ ℓs T n v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have h0 : ∀ v, mirrorIterate ρ₀ ℓs T 0 v = ρ₀ v :=
          fun v => rfl
        simp only [h0, zero_add]
        exact le_of_eq rfl
    | succ m ih =>
        rw [Finset.sum_range_succ]
        -- одношаговое неравенство на шаге m
        have hposm : ∀ v, 0 < mirrorIterate ρ₀ ℓs T m v :=
          mirrorIterate_pos ρ₀ ℓs T hT hρ₀ m
        have h1m : ∑ v, mirrorIterate ρ₀ ℓs T m v = 1 :=
          mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 m
        have hstep := mirror_step_regret
          (mirrorIterate ρ₀ ℓs T m) (ℓs m) T hT hposm h1m
          ρ hρ hρ1
        -- w_{m+1} = mirrorStep w_m ℓ_m T по определению
        have hdef : mirrorIterate ρ₀ ℓs T (m+1)
            = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
          simp only [mirrorIterate]
        rw [hdef]
        linarith
  have h := key n
  -- финальный KL ≥ 0 → регрет ≤ границы
  have hposn : ∀ v, 0 < mirrorIterate ρ₀ ℓs T n v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n
  have h1n : ∑ v, mirrorIterate ρ₀ ℓs T n v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 n
  have hkl : (0:ℝ) ≤ T * (∑ v, ρ v * Real.log (ρ v
      / mirrorIterate ρ₀ ℓs T n v)) :=
    mul_nonneg (le_of_lt hT)
      (finite_kl_nonneg ρ (mirrorIterate ρ₀ ℓs T n)
        hρ hρ1 hposn h1n)
  linarith

/-- КЛАССИЧЕСКАЯ ГРАНИЦА MWU: при равномерном старте
w₀ = 1/n регрет hedge/MWU относительно любой цели ρ* ≤
T·log n — KL(ρ*‖u) = Σρ*log ρ + log n ≤ log n, поскольку
ρ ≤ 1 ⟹ log ρ ≤ 0: каноническая regret-граница
экспоненциальных весов выводится из зеркального
телескопирования. -/
theorem mirror_regret_uniform {V : Type*} [Fintype V] [Nonempty V]
    (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1)
    (n : ℕ) :
    ∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate (fun _ => 1 / (Fintype.card V : ℝ))
            ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v))
      ≤ T * Real.log (Fintype.card V : ℝ) := by
  have hcard : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcardne : ((Fintype.card V : ℝ)) ≠ 0 := ne_of_gt hcard
  have hupos : ∀ v : V,
      (0:ℝ) < 1 / (Fintype.card V : ℝ) := by
    intro v; positivity
  have hu1 : ∑ v : V, 1 / (Fintype.card V : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      one_div, mul_inv_cancel₀ hcardne]
  -- ρ v ≤ 1: иначе сумма превысила бы 1
  have hle1 : ∀ v, ρ v ≤ 1 := by
    intro v
    have hs := Finset.single_le_sum
      (fun w _ => le_of_lt (hρ w)) (Finset.mem_univ v)
    linarith
  -- Σ ρ log ρ ≤ 0 (log ρ ≤ 0 при 0 < ρ ≤ 1)
  have hlogneg : (∑ v, ρ v * Real.log (ρ v)) ≤ 0 := by
    refine Finset.sum_nonpos fun v _ => ?_
    have hlog : Real.log (ρ v) ≤ 0 := by
      have h2 := Real.log_le_log (hρ v) (hle1 v)
      rw [Real.log_one] at h2
      exact h2
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (hρ v)) hlog
  -- KL(ρ‖u) = Σρ log ρ + log n
  have hKL : (∑ v, ρ v
        * Real.log (ρ v / (1 / (Fintype.card V : ℝ))))
      = (∑ v, ρ v * Real.log (ρ v))
        + Real.log (Fintype.card V : ℝ) := by
    have hsplit : ∀ v : V, ρ v
        * Real.log (ρ v / (1 / (Fintype.card V : ℝ)))
        = ρ v * Real.log (ρ v)
          + ρ v * Real.log (Fintype.card V : ℝ) := by
      intro v
      have hrw : ρ v / (1 / (Fintype.card V : ℝ))
          = ρ v * (Fintype.card V : ℝ) := by
        field_simp
      rw [hrw, Real.log_mul (hρ v).ne' hcardne]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hρ1, one_mul]
  -- зеркальный регрет с равномерным стартом
  have hr := mirror_regret
    (fun _ => 1 / (Fintype.card V : ℝ)) ℓs T hT hupos hu1
    ρ hρ hρ1 n
  -- KL ≤ log n, тогда T·KL ≤ T·log n
  have hKLle : (∑ v, ρ v
      * Real.log (ρ v / (1 / (Fintype.card V : ℝ))))
      ≤ Real.log (Fintype.card V : ℝ) := by linarith
  have hTL : T * (∑ v, ρ v
      * Real.log (ρ v / (1 / (Fintype.card V : ℝ))))
      ≤ T * Real.log (Fintype.card V : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hKLle (le_of_lt hT)
    have hcomm : Real.log (Fintype.card V : ℝ) * T
        = T * Real.log (Fintype.card V : ℝ) := mul_comm _ _
    linarith
  linarith

end Hagi.Optimization

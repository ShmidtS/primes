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

/-- ПОЛУГРУППОВОЙ ЗАКОН ЗЕРКАЛЬНОГО ШАГА: два
последовательных зеркальных шага (ℓ₁, затем ℓ₂, одна
температура T) равны одному шагу с суммарными потерями
ℓ₁+ℓ₂ — экспоненциальные веса перемножаются, нормировки
согласованы (Z₂·Z₁ = Z₁₂): траектория hedge за n шагов
есть один шаг с кумулятивными потерями. -/
theorem mirror_step_semigroup {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T
      = mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hZ₂ : (0:ℝ) < ∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hγpos w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have he : ∀ w : V, Real.exp (-(ℓ₁ w)/T)
      * Real.exp (-(ℓ₂ w)/T)
      = Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    rw [← Real.exp_add]
    congr 1
    ring
  -- почленно: γ₁(w)·e^{−ℓ₂/T}·Z₁ = ρ₀(w)·e^{−(ℓ₁+ℓ₂)/T}
  have hterm : ∀ w : V, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T)
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    unfold mirrorStep
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZ₁.ne',
      show ρ₀ w * Real.exp (-(ℓ₁ w)/T)
          * Real.exp (-(ℓ₂ w)/T)
        = ρ₀ w * (Real.exp (-(ℓ₁ w)/T)
            * Real.exp (-(ℓ₂ w)/T)) from by ring, he w]
  -- суммарно: Z₂·Z₁ = Z₁₂
  have hsum : (∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T))
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun w _ => hterm w)
  -- поэлементное совпадение
  funext v
  have htermv : mirrorStep ρ₀ ℓ₁ T v
      * Real.exp (-(ℓ₂ v)/T)
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T)) :=
    eq_div_of_mul_eq hZ₁.ne' (hterm v)
  have hL : mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T v
      = (mirrorStep ρ₀ ℓ₁ T v * Real.exp (-(ℓ₂ v)/T))
        / (∑ w, mirrorStep ρ₀ ℓ₁ T w
            * Real.exp (-(ℓ₂ w)/T)) := rfl
  have hR : mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T v
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ w, ρ₀ w
            * Real.exp (-(ℓ₁ w + ℓ₂ w)/T)) := by
    dsimp only [mirrorStep]
  rw [hL, hR, htermv, ← hsum]
  field_simp

/-- НУЛЕВЫЕ ПОТЕРИ: зеркальный шаг при ℓ = 0 возвращает
ссылку (Z = Σρ₀·e⁰ = 1): тождественное обновление. -/
theorem mirrorStep_zero_loss {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    mirrorStep ρ₀ (fun _ => 0) T = ρ₀ := by
  have hexp : ∀ w : V, Real.exp (-(0:ℝ)/T) = 1 := by
    intro w
    have hz : (-(0:ℝ)/T) = 0 := by
      rw [neg_zero, zero_div]
    rw [hz, Real.exp_zero]
  have hZ : (∑ w, ρ₀ w * Real.exp (-(0:ℝ)/T)) = 1 := by
    rw [Finset.sum_congr rfl (fun w _ => by rw [hexp w, mul_one])]
    exact hρ₀1
  funext v
  have hnum : ρ₀ v * Real.exp (-(0:ℝ)/T) = ρ₀ v := by
    rw [hexp v, mul_one]
  unfold mirrorStep
  rw [hZ, div_one, hnum]

/-- N-КРАТНЫЙ ПОЛУГРУППОВОЙ ЗАКОН: траектория hedge за n
шагов есть ОДИН зеркальный шаг с кумулятивными потерями
Σ_{k<n} ℓ_k: экспоненциальные веса накапливают потери
аддитивно, нормировки глобальны. -/
theorem mirrorIterate_cumulative {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ)
    (hT : 0 < T) (hρ₀ : ∀ v, 0 < ρ₀ v)
    (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    mirrorIterate ρ₀ ℓs T n
      = mirrorStep ρ₀
          (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ ℓs T 0 = ρ₀ := rfl
      rw [h0]
      exact (mirrorStep_zero_loss ρ₀ T hT hρ₀ hρ₀1).symm
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ ℓs T (m+1)
          = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
        simp only [mirrorIterate]
      rw [hdef, ih, mirror_step_semigroup ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀]
      congr 1
      funext v
      simp only [Finset.sum_range_succ]

/-- МОНОТОННОСТЬ ЭНЕРГИИ HEDGE: зеркальный шаг по потерям ℓ
никогда не поднимает ожидаемые потери по ним:
⟨mirrorStep ρ₀ ℓ T, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩. Цепочка:
⟨γ,ℓ⟩ ≤ F(γ) (KL(γ‖ρ₀) ≥ 0), F(γ) = −T·log Z
(attainment), −T·log Z ≤ ⟨ρ₀,ℓ⟩ (Йенсен выпуклости exp:
e^{−⟨ρ₀,ℓ⟩/T} ≤ Z). -/
theorem mirror_energy_decrease {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) ≤ (∑ v, ρ₀ v * ℓ v) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  -- KL(γ‖ρ₀) ≥ 0
  have hkl : (0:ℝ) ≤ ∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v) :=
    finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀ hγpos hγ1 hρ₀ hρ₀1
  -- attainment: F(γ) = −T·log Z
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- Йенсен: e^{−⟨ρ₀,ℓ⟩/T} ≤ Z
  have hZpos : (0:ℝ) < ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) :=
    Finset.sum_pos
      (fun v _ => mul_pos (hρ₀ v) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hjensen : Real.exp ((∑ v, ρ₀ v * (-(ℓ v)/T)))
      ≤ ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) := by
    have hconv := convexOn_exp.map_sum_le
      (p := fun v => -(ℓ v)/T)
      (fun v _ => le_of_lt (hρ₀ v)) hρ₀1
      (fun v _ => Set.mem_univ v)
    simp only [smul_eq_mul] at hconv
    exact hconv
  -- log-монотонность: −⟨ρ₀,ℓ⟩/T ≤ log Z
  have hlogj : (∑ v, ρ₀ v * (-(ℓ v)/T))
      ≤ Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hjensen
    rw [Real.log_exp] at h1
    exact h1
  -- линейная сборка
  have hsplit : (∑ v, ρ₀ v * (-(ℓ v)/T))
      = -(∑ v, ρ₀ v * ℓ v)/T := by
    have hterm : ∀ v : V, ρ₀ v * (-(ℓ v)/T)
        = -(ρ₀ v * ℓ v)/T := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v),
      ← Finset.sum_neg_distrib, ← Finset.sum_div]
  rw [hsplit] at hlogj
  -- финал: ⟨γ,ℓ⟩ ≤ F(γ) = −T log Z ≤ ⟨ρ₀,ℓ⟩
  have hTKL : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) :=
    mul_nonneg (le_of_lt hT) hkl
  have h1 : (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      ≤ (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    linarith
  have h2 : ((∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)))
      = -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) :=
    hatt
  rw [h2] at h1
  -- −T·logZ ≤ ⟨ρ₀,ℓ⟩ из hlogj (умножение на T > 0)
  have h3 : -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T))
      ≤ ∑ v, ρ₀ v * ℓ v := by
    have h4 := (mul_le_mul_of_nonneg_left hlogj (le_of_lt hT))
    -- T·(−⟨ρ₀,ℓ⟩/T) ≤ T·logZ ; T·(−X/T) = −X
    have h5 : T * (-(∑ v, ρ₀ v * ℓ v)/T)
        = -(∑ v, ρ₀ v * ℓ v) := by
      field_simp
    rw [h5] at h4
    linarith
  linarith [hkl, hT]

/-- МОНОТОННОСТЬ ЭНЕРГИИ ВДОЛЬ ТРАЕКТОРИИ: при фиксированных
потерях ℓ повторные зеркальные шаги монотонно не поднимают
ожидаемую энергию: ⟨w_n, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩ для всех n —
итерированный hedge сходится по энергии (индукция из
mirror_energy_decrease). -/
theorem mirrorIterate_energy_monotone {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ (∑ v, ρ₀ v * ℓ v) := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ (fun _ => ℓ) T 0 = ρ₀ := rfl
      rw [h0]
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (m+1)
          = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T :=
        by simp only [mirrorIterate]
      rw [hdef]
      have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T m v :=
        mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ m
      have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T m v = 1 :=
        mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 m
      have hstep := mirror_energy_decrease
        (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T hT hpos h1
      linarith

/-- СХОДИМОСТЬ ЭНЕРГИИ ИТЕРАЦИЙ: при фиксированных потерях ℓ
с нижней границей C последовательность энергий
e_n = ⟨w_n, ℓ⟩ убывает шаг за шагом и ограничена снизу,
поэтому входит в ε-коридор над своим инфимумом L:
∀n≥N: L ≤ e_n ≤ L + ε — итерированный hedge сходится по
энергии (полнота ℝ + монотонность). -/
theorem mirrorIterate_energy_converges {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (C : ℝ) (hC : ∀ v, C ≤ ℓ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (sInf (Set.range (fun k =>
          ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v)))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (sInf (Set.range (fun k =>
            ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v))) + ε := by
  set e : ℕ → ℝ := fun k =>
    ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v with he
  -- соседняя монотонность: e_{n+1} ≤ e_n
  have hstep : ∀ n : ℕ, e (n+1) ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (n+1)
        = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T :=
      by simp only [mirrorIterate]
    have hdec := mirror_energy_decrease
      (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T hT hpos h1
    rw [he]
    show (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T (n+1) v * ℓ v)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
    rw [hdef]
    exact hdec
  -- цепная монотонность: m ≤ n → e_n ≤ e_m
  have hchain : ∀ n m : ℕ, m ≤ n → e n ≤ e m := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have h0 : m = 0 := Nat.le_zero.mp hm
        subst h0
        exact le_refl _
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_ge m (k+1) with hlt | hge
        · have hk : m ≤ k := Nat.lt_succ_iff.mp hlt
          have a := hstep k
          have b := ih m hk
          linarith
        · have h0 : m = k+1 := Nat.le_antisymm hm hge
          subst h0
          exact le_refl _
  -- ограниченность снизу: C ≤ e_n
  have hbdd : ∀ n : ℕ, C ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hle : ∀ v : V, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hC v) (le_of_lt (hpos v))
    have hsplit : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) :=
      Finset.sum_le_sum fun v _ => hle v
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C) = C := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) C),
        ← Finset.mul_sum, h1, mul_one]
    rw [he]
    linarith
  -- инфимум L и его свойства
  set L := sInf (Set.range e) with hL
  have hrng : (Set.range e).Nonempty := ⟨e 0, Set.mem_range_self 0⟩
  have hbddBelow : BddBelow (Set.range e) :=
    ⟨C, fun y hy => by
      obtain ⟨n, hn⟩ := Set.mem_range.mp hy
      rw [← hn]
      exact hbdd n⟩
  have hleL : ∀ n : ℕ, L ≤ e n :=
    fun n => csInf_le hbddBelow (Set.mem_range_self n)
  -- ∃ N: e N ≤ L + ε (иначе L+ε — меньшая нижняя граница)
  have hex : ∃ N : ℕ, e N ≤ L + ε := by
    by_contra hcon
    push_neg at hcon
    have hle' : L + ε ≤ L :=
      le_csInf hrng (fun y hy => by
        obtain ⟨n, hn⟩ := Set.mem_range.mp hy
        rw [← hn]
        exact le_of_lt (hcon n))
    linarith
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ⟨hleL n, ?_⟩⟩
  have h1 := hchain n N hn
  linarith

/-- NERNST-ПРЕДЕЛ ИТЕРАЦИЙ HEDGE: при фиксированных потерях ℓ
повторные зеркальные шаги сходятся по энергии к минимуму
потерь: ∀ε>0 ∃N ∀n≥N: ℓmin ≤ ⟨w_n, ℓ⟩ ≤ ℓmin + ε.
Механизм: w_n = mirrorStep ρ₀ (n·ℓ) T (кумулятивность),
свободная энергия F_n ≤ n·ℓmin − T·log(min ρ₀)
(Z_n ≥ min ρ₀ · e^{−nℓmin/T}), и KL-слагаемое ≥ 0 —
итерированный hedge находит минимум (термодинамический
предел T/n → 0). -/
theorem mirrorIterate_energy_infimum {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty)) + ε := by
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  set m := Finset.min' (Finset.univ.image ℓ) hneℓ with hm
  set r := Finset.min' (Finset.univ.image ρ₀) hneρ with hr
  -- минимумы достижимы и ограничивают
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hrw : r = ρ₀ wt := hwt.2.symm
  have hrpos : (0:ℝ) < r := by rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun w _ => le_of_lt (hρ₀ w)) (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- кумулятивность: w_n = mirrorStep ρ₀ (n·ℓ) T
  have hsum : ∀ (n : ℕ) (v : V),
      (∑ k ∈ Finset.range n, ℓ v) = (n : ℝ) * ℓ v := by
    intro n v
    simp
  have hwn : ∀ n : ℕ, mirrorIterate ρ₀ (fun _ => ℓ) T n
      = mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T := by
    intro n
    rw [mirrorIterate_cumulative ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n]
    congr 1
    funext v
    rw [hsum n v]
  -- нижняя граница энергии: e_n ≥ m
  have hposn : ∀ (n : ℕ) (v : V),
      0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
    mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀
  have h1n : ∀ n : ℕ,
      ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
    mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1
  have hlower : ∀ n : ℕ, m ≤ (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) := by
    intro n
    have hle : ∀ v : V,
        mirrorIterate ρ₀ (fun _ => ℓ) T n v * m
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hmle v)
        (le_of_lt (hposn n v))
    have hsplit := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hle v)
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * m) = m := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) m),
        ← Finset.mul_sum, h1n n, mul_one]
    rw [hsumC] at hsplit
    exact hsplit
  -- верхняя граница: e_n ≤ m + (T/n)·(−log r)
  have hupper : ∀ n : ℕ, (0:ℕ) < n → (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ m + T * (-(Real.log r)) / (n : ℝ) := by
    intro n hn
    -- KL(w_n ‖ ρ₀) ≥ 0 и attainment для n·ℓ
    have hγpos : ∀ v, 0 < mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v :=
      mirrorStep_pos ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hγ1 : ∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v = 1 :=
      mirrorStep_sum_one ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hkl : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v
        * Real.log (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v / ρ₀ v)) :=
      mul_nonneg (le_of_lt hT)
        (finite_kl_nonneg (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T)
          ρ₀ hγpos hγ1 hρ₀ hρ₀1)
    -- attainment: ⟨γ, nℓ⟩ + T·KL = −T·log Z_n
    have hatt := mirror_descent_attainment ρ₀
      (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    -- нижняя оценка Z_n ≥ r · e^{−nm/T} через vt
    have hZge : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ ρ₀ vt * Real.exp (-((n : ℝ) * m)/T) := by
      have hterm := Finset.single_le_sum
        (f := fun w => ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        (fun w (_ : w ∈ Finset.univ) =>
          mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
        (Finset.mem_univ vt)
      rw [hvt.2] at hterm
      exact hterm
    have hrr : ρ₀ vt ≥ r := hrle vt
    have hZge2 : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ r * Real.exp (-((n : ℝ) * m)/T) := by
      nlinarith [hZge, hrr, (Real.exp_pos
        (-((n : ℝ) * m)/T))]
    -- log-монотонность
    have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T) := by
      have h0 : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
        mul_pos hrpos (Real.exp_pos _)
      linarith
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have hlog : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        ≤ Real.log (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)) :=
      Real.log_le_log hrpos' hZge2
    -- log(r·e^{−nm/T}) = log r − nm/T
    have hlogsplit : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        = Real.log r + (-((n : ℝ) * m)/T) := by
      rw [Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogsplit] at hlog
    -- собираем: e_n = ⟨γ, ℓ⟩ и ⟨γ, nℓ⟩ = n·e_n
    rw [hwn n]
    have hmul : (∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
        * ((n : ℝ) * ℓ v))
        = (n : ℝ) * (∑ v, mirrorStep ρ₀
            (fun v => (n : ℝ) * ℓ v) T v * ℓ v) := by
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) =>
        show mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
            * ((n : ℝ) * ℓ v)
          = (n : ℝ) * (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
              * ℓ v) from by ring)]
      exact (Finset.mul_sum _ _ _).symm
    -- финальная арифметика
    have hnne : ((n : ℝ)) ≠ 0 := by
      have : (0:ℕ) < n := hn
      exact_mod_cast this.ne'
    rw [hmul] at hatt
    -- hlog, умноженный на T: T·log r − n·m ≤ T·logZ
    have hDTneg : T * (-(((n : ℝ) * m)/T))
        = -((n : ℝ) * m) := by
      have hDT : T * (((n : ℝ) * m)/T) = (n : ℝ) * m := by
        field_simp
      have hsplit : T * (-(((n : ℝ) * m)/T))
          = -(T * (((n : ℝ) * m)/T)) := by ring
      rw [hsplit, hDT]
    have hlog' : T * (Real.log r + -(((n : ℝ) * m)/T))
        ≤ T * Real.log (∑ w, ρ₀ w
          * Real.exp (-((n : ℝ) * ℓ w)/T)) := by
      have h := mul_le_mul_of_nonneg_left
        (show Real.log r + -((n : ℝ) * m)/T
            ≤ Real.log (∑ w, ρ₀ w
              * Real.exp (-((n : ℝ) * ℓ w)/T)) from hlog)
        (le_of_lt hT)
      have hnorm : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * (Real.log r + -((n : ℝ) * m)/T) := by
        congr 1
        congr 1
        field_simp
      rw [hnorm]
      exact h
    have hsplit : T * (Real.log r + -(((n : ℝ) * m)/T))
        = T * Real.log r - (n : ℝ) * m := by
      rw [mul_add, hDTneg]
      ring
    rw [hsplit] at hlog'
    -- hlog' : T·log r − n·m ≤ T·logZ
    -- n·e_n ≤ n·m − T·log r
    have hkey : ((n : ℝ)) * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v)
        ≤ (n : ℝ) * m + T * (-(Real.log r)) := by
      linarith [hatt, hkl, hlog']
    -- деление на n > 0
    have hnposR : (0:ℝ) < (n : ℝ) := by
      have := hn; exact_mod_cast this
    have hkey' : ((n : ℝ)) * ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey]
    have hmuln : ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m) * (n : ℝ)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey']
    have hdiv : (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m
        ≤ T * (-(Real.log r)) / (n : ℝ) :=
      (le_div_iff₀ hnposR).mpr hmuln
    linarith
  -- выбор N: T·(−log r)/ε ≤ N
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      T * (-(Real.log r)) / ε ≤ N :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N + 1, fun n hn => ⟨hlower n, ?_⟩⟩
  have hnpos : (0:ℕ) < n := by omega
  have hbound := hupper n hnpos
  -- (T/n)(−log r) ≤ ε при n ≥ N+1 > N ≥ T(−log r)/ε
  have hnN : ((N : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hNge : T * (-(Real.log r)) ≤ (N : ℝ) * ε :=
    (div_le_iff₀ hε).mp hN
  have hnnz : ((n : ℝ)) ≠ 0 := by
    have : (0:ℕ) < n := hnpos
    exact_mod_cast this.ne'
  have hfin : T * (-(Real.log r)) / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ (show (0:ℝ) < (n : ℝ) by
      have := hnpos; exact_mod_cast this)]
    -- T(−log r) ≤ n·ε ⟸ N·ε ≤ n·ε и T(−log r) ≤ N·ε
    nlinarith [hNge, hnN, hε]
  linarith

/-- Пошаговая нормировка зеркального шага: Z(ρ₀,ℓ,T) =
Σ ρ₀·e^{−ℓ/T} — коэффициент перенормировки весов. -/
noncomputable def stepNorm {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) : ℝ :=
  ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)

/-- НОРМИРОВКИ ПЕРЕМНОЖАЮТСЯ: нормировка двух
последовательных шагов равна нормировке одного шага с
суммарными потерями: Z(γ₁,ℓ₂)·Z(ρ₀,ℓ₁) = Z(ρ₀,ℓ₁+ℓ₂) —
двойник полугруппового закона на уровне нормировок
(свидетельство: hedge-капитал телескопирует). -/
theorem stepNorm_compose {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    stepNorm (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T * stepNorm ρ₀ ℓ₁ T
      = stepNorm ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have he : ∀ w : V, Real.exp (-(ℓ₁ w)/T)
      * Real.exp (-(ℓ₂ w)/T)
      = Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    rw [← Real.exp_add]
    congr 1
    ring
  -- почленно: γ₁(w)·e^{−ℓ₂/T}·Z₁ = ρ₀(w)·e^{−(ℓ₁+ℓ₂)/T}
  have hterm : ∀ w : V, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T)
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    unfold mirrorStep
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZ₁.ne',
      show ρ₀ w * Real.exp (-(ℓ₁ w)/T)
          * Real.exp (-(ℓ₂ w)/T)
        = ρ₀ w * (Real.exp (-(ℓ₁ w)/T)
            * Real.exp (-(ℓ₂ w)/T)) from by ring, he w]
  -- суммирование
  unfold stepNorm
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun w _ => hterm w)

/-- КАПИТАЛ HEDGE ТЕЛЕСКОПИРУЕТ: произведение пошаговых
нормировок траектории равно кумулятивной нормировке:
∏_{k<n} Z(w_k, ℓ_k, T) = Z(ρ₀, Σ_{k<n} ℓ_k, T) —
потенциал-функция MWU/Hedge в замкнутой форме. -/
theorem hedge_wealth_product {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    (∏ k ∈ Finset.range n,
        stepNorm (mirrorIterate ρ₀ ℓs T k) (ℓs k) T)
      = stepNorm ρ₀ (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      show (1:ℝ) = stepNorm ρ₀
        (fun v => ∑ k ∈ Finset.range 0, ℓs k v) T
      simp only [Finset.range_zero, Finset.sum_empty, neg_zero,
        div_zero, Real.exp_zero, mul_one, stepNorm, zero_div]
      exact hρ₀1.symm
  | succ m ih =>
      -- кумулятивность: w_m = mirrorStep ρ₀ (Σ_{<m}) T
      have hcum : mirrorIterate ρ₀ ℓs T m
          = mirrorStep ρ₀ (fun v => ∑ k ∈ Finset.range m, ℓs k v) T :=
        mirrorIterate_cumulative ρ₀ ℓs T hT hρ₀ hρ₀1 m
      -- композиция нормировок на уровне ρ₀
      have hcomp := stepNorm_compose ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀
      -- кумулятивная сумма range (m+1)
      have hsum : (fun v => ∑ k ∈ Finset.range (m+1), ℓs k v)
          = (fun v => (∑ k ∈ Finset.range m, ℓs k v) + ℓs m v) := by
        funext v
        rw [Finset.sum_range_succ]
      rw [Finset.prod_range_succ, hsum, ih, hcum, mul_comm,
        ← hcomp]

/-- НЕРНСТ-СЭНДВИЧ КАПИТАЛА HEDGE: логарифм капитала
(произведения пошаговых нормировок) зажат:
n·ℓmin − T·log|V| ≤ −T·log(∏ Z_k) ≤ n·ℓmin − T·log(min ρ₀).
Низ: каждый член ≤ e^{−nℓmin/T}, сумма ≤ |V|·e^{−nm/T};
верх: Z ≥ (min ρ₀)·e^{−nℓmin/T} — кумулятивная свободная
энергия итераций зажата энтропийным запасом и минимальным
априорным весом (термодинамический предел капитала). -/
theorem hedge_wealth_nernst {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    ((n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Fintype.card V : ℝ)
      ≤ -T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    ∧ (-T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
      ≤ (n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Finset.min' (Finset.univ.image ρ₀)
          (Finset.image_nonempty.2 Finset.univ_nonempty))) := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  have hrpos : (0:ℝ) < r := by
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  -- капитал = кумулятивная нормировка
  have hwealth := hedge_wealth_product ρ₀ (fun _ => ℓ) T hT hρ₀
    hρ₀1 n
  set Z : ℝ := stepNorm ρ₀
    (fun v => ∑ k ∈ Finset.range n, ℓ v) T with hZ
  have hZn : Z = ∑ w, ρ₀ w
      * Real.exp (-((n : ℝ) * ℓ w)/T) := by
    rw [hZ]
    refine Finset.sum_congr rfl fun w _ => ?_
    show ρ₀ w * Real.exp ((-∑ k ∈ Finset.range n, ℓ w)/T)
      = ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Z ≥ r·e^{−nm/T}
  have hZge : r * Real.exp (-((n : ℝ) * m)/T) ≤ Z := by
    rw [hZn]
    have hterm := Finset.single_le_sum
      (f := fun w => ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T))
      (fun w (_ : w ∈ Finset.univ) =>
        mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
      (Finset.mem_univ vt)
    rw [hvt.2] at hterm
    nlinarith [hterm, hrle vt, Real.exp_pos
      (-((n : ℝ) * m)/T)]
  -- Z ≤ |V|·e^{−nm/T}
  have hZle : Z ≤ (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) := by
    rw [hZn]
    have hterm : ∀ w : V, ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T)
        ≤ Real.exp (-((n : ℝ) * m)/T) := by
      intro w
      have h1 : ρ₀ w ≤ 1 := by
        have hs := Finset.single_le_sum
          (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
          (Finset.mem_univ w)
        rw [hρ₀1] at hs
        exact hs
      have h2 : Real.exp (-((n : ℝ) * ℓ w)/T)
          ≤ Real.exp (-((n : ℝ) * m)/T) := by
        refine Real.exp_le_exp.mpr ?_
        have hnle : ((n : ℝ)) * m ≤ (n : ℝ) * ℓ w :=
          mul_le_mul_of_nonneg_left (hmle w)
            (Nat.cast_nonneg n)
        have hnegr : -((n : ℝ) * ℓ w)
            ≤ -((n : ℝ) * m) := by
          have h1 : -((n : ℝ) * ℓ w) ≤ -((n : ℝ) * m) :=
            neg_le_neg hnle
          exact h1
        exact (div_le_div_iff_of_pos_right (show (0:ℝ) < T by
          exact hT)).mpr hnegr
      exact (mul_le_mul h1 h2 (Real.exp_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    calc (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≤ ∑ w : V, Real.exp (-((n : ℝ) * m)/T) :=
          Finset.sum_le_sum (fun w _ => hterm w)
      _ = (Fintype.card V : ℝ)
          * Real.exp (-((n : ℝ) * m)/T) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- позитивность Z
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  -- логарифмический сэндвич
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcpos : (0:ℝ) < (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) :=
    mul_pos hcardpos (Real.exp_pos _)
  -- card·e^{−nm/T} = e^{log card − nm/T}
  have hEqC : (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hcardpos,
      div_eq_mul_inv (Fintype.card V : ℝ)
        (Real.exp (((n : ℝ) * m)/T)), ← Real.exp_neg]
    congr 1
    ring
  -- log Z ≤ log card − nm/T
  have hlogZle : Real.log Z
      ≤ Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T := by
    have h1 := Real.log_le_log hZpos hZle
    rw [hEqC, Real.log_exp] at h1
    exact h1
  -- log r − nm/T ≤ log Z
  -- r·e^{−nm/T} = e^{log r − nm/T}
  have hEqR : r * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log r - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hrpos,
      div_eq_mul_inv r (Real.exp (((n : ℝ) * m)/T)),
      ← Real.exp_neg]
    congr 1
    ring
  -- log r − nm/T ≤ log Z
  have hlogZge : Real.log r - ((n : ℝ) * m)/T ≤ Real.log Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have h1 := Real.log_le_log hrpos' hZge
    rw [hEqR, Real.log_exp] at h1
    exact h1
  -- финальные умножения на −T < 0
  have hTnn : (0:ℝ) ≤ T := le_of_lt hT
  constructor
  · -- nm − T·log card ≤ −T·log Z
    rw [hwealth]
    have hmul := mul_le_mul_of_nonneg_left hlogZle hTnn
    have hsplit : T * (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T)
        = T * Real.log (Fintype.card V : ℝ) - (n : ℝ) * m := by
      rw [mul_sub, mul_div_assoc',
        mul_div_cancel_left₀ _ (ne_of_gt hT)]
    rw [hsplit] at hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith
  · -- −T·log Z ≤ nm − T·log r
    rw [hwealth]
    have hlogZge' : Real.log r + (-(((n : ℝ) * m)/T))
        ≤ Real.log Z := by
      have := hlogZge
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogZge' hTnn
    have hkey : T * Real.log r - (n : ℝ) * m ≤ T * Real.log Z := by
      have hTdiv : T * (((n : ℝ) * m)/T) = (n : ℝ) * m :=
        mul_div_cancel₀ _ (ne_of_gt hT)
      have hexp : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * Real.log r - T * (((n : ℝ) * m)/T) := by ring
      rw [hexp, hTdiv] at hmul
      exact hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith

/-- СРЕДНИЙ ЛОГ-КАПИТАЛ СХОДИТСЯ К МИНИМУМУ: из
Нернст-сэндвича капитала: −T·log(∏Z_k)/n → ℓmin при
n → ∞ — средняя свободная энергия на шаг итерированного
hedge стремится к минимальным потерям (скорость —
T·log|V|/n сверху и T·log(min ρ₀)/n снизу). -/
theorem hedge_wealth_rate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      abs ((-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
        / (n : ℝ)
        - (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty))) ≤ ε := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hsand : ∀ n : ℕ,
      ((n : ℝ) * m - T * Real.log (Fintype.card V : ℝ)
        ≤ -T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
      ∧ (-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
        ≤ (n : ℝ) * m - T * Real.log r) :=
    fun n => hedge_wealth_nernst ρ₀ ℓ T hT hρ₀ hρ₀1 n
  -- границы смещения на шаг n
  set E := fun n : ℕ => (-T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    / (n : ℝ) with hE
  -- |E n − m| ≤ max(T·log card, −T·log r)/n ≤ ε при больших n
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hrpos : (0:ℝ) < r := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
      (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- обе границы отклонения: T·log card / n и T·(−log r)/n
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ,
      T * Real.log (Fintype.card V : ℝ) / ε ≤ N1 :=
    exists_nat_ge (T * Real.log (Fintype.card V : ℝ) / ε)
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ,
      T * (-(Real.log r)) / ε ≤ N2 :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N1 + N2 + 1, fun n hn => ?_⟩
  have hnpos : (0:ℕ) < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by
    have := hnpos; exact_mod_cast this
  obtain ⟨hlo_n, hhi_n⟩ := hsand n
  set W := -T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T) with hWdef
  rw [hWdef] at hlo_n hhi_n
  -- пороги: A := T·log|V| ≥ 0, B := −T·log r ≥ 0
  have hcard1 : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
    have := Fintype.card_pos (α := V)
    exact_mod_cast this
  have hA : (0:ℝ) ≤ T * Real.log (Fintype.card V : ℝ) :=
    mul_nonneg (le_of_lt hT) (Real.log_nonneg hcard1)
  have hB : (0:ℝ) ≤ T * (-(Real.log r)) :=
    mul_nonneg (le_of_lt hT) (neg_nonneg.mpr hlogr)
  -- W/n − m = (W − n·m)/n
  rw [div_sub' hnR.ne', abs_le]
  constructor
  · -- −ε ≤ (W − nm)/n ⟸ nm − A ≤ W и A ≤ n·ε
    rw [le_div_iff₀ hnR]
    -- цель: −ε·n ≤ W − n·m
    have hN1le : (N1 : ℝ) ≤ (n : ℝ) := by
      have : (N1 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN1e : T * Real.log (Fintype.card V : ℝ) ≤ (N1 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN1
    nlinarith [hN1e, hN1le, hε, hlo_n]
  · -- (W − nm)/n ≤ ε ⟸ W ≤ nm + B и B ≤ n·ε
    rw [div_le_iff₀ hnR]
    have hN2le : (N2 : ℝ) ≤ (n : ℝ) := by
      have : (N2 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN2e : T * (-(Real.log r)) ≤ (N2 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN2
    nlinarith [hN2e, hN2le, hε, hhi_n]


/-! ### Источник №70 (arXiv 2609.15897): вариационный шаг как спуск
JKO-подобная схема: каждое экспоненциальное обновление —
минимизация свободной энергии F(q) = ⟨q,ℓ⟩ + T·KL(q‖ρ₀).
Отсюда НЕВОЗРАСТАНИЕ F вдоль итераций при том же ландшафте ℓ
(частный случай: конкурент q = ρ₀ с KL = 0). -/

/-- ВАРИАЦИОННЫЙ СПУСК ЗЕРКАЛЬНОГО ШАГА: γ = mirrorStep ρ₀ ℓ T
даёт F(γ) := ⟨γ,ℓ⟩ + T·KL(γ‖ρ₀) ≤ ⟨ρ₀,ℓ⟩ = F(ρ₀) — каждое
экспоненциальное обновление НЕ УВЕЛИЧИВАЕТ свободную энергию
(конкурент ρ₀ имеет нулевой KL-штраф; частный случай
вариационного принципа источника №70, arXiv 2609.15897). -/
theorem mirror_step_variational_descent {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      + T * (∑ v, mirrorStep ρ₀ ℓ T v
          * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v))
      ≤ ∑ v, ρ₀ v * ℓ v := by
  -- достижимость: F(γ) = −T·log Z ...
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- ... и пол с конкурентом ρ₀ (KL(ρ₀‖ρ₀) = 0):
  --   −T·log Z ≤ ⟨ρ₀,ℓ⟩ + T·KL(ρ₀‖ρ₀) = ⟨ρ₀,ℓ⟩
  have hself : (∑ v, ρ₀ v * Real.log (ρ₀ v / ρ₀ v)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    rw [div_self (hρ₀ v).ne', Real.log_one, mul_zero]
  have hfloor := mirror_descent_floor ρ₀ ℓ T hT hρ₀ ρ₀ hρ₀ hρ1
  rw [hself, mul_zero] at hfloor
  linarith

/-- ИТЕРАЦИОННАЯ МОНОТОННОСТЬ (№70): при фиксированном
ландшафте ℓ частная свободная энергия шага не возрастает
вдоль траектории mirrorIterate: F_{k+1} ≤ F_k, где
F_k = ⟨ρ_k,ℓ⟩ (KL-штраф относительно ρ_k обнуляется на
следующем шаге). Кумулятивный аналог убывания свободной
энергии в JKO-схеме. -/
theorem mirrorIterate_partial_mono {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1)
    (ℓs : ℕ → V → ℝ) (k : ℕ) (hls : ℓs k = ℓ) :
    ∑ v, (mirrorIterate ρ₀ ℓs T (k+1)) v * ℓ v
      ≤ ∑ v, (mirrorIterate ρ₀ ℓs T k) v * ℓ v := by
  have hpos : ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ k
  have hsum : ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ1 k
  have hstep : mirrorIterate ρ₀ ℓs T (k+1)
      = mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T := rfl
  rw [hls] at hstep
  rw [hstep]
  -- KL-штраф ≥ 0, поэтому вариационный спуск даёт ⟨γ,ℓ⟩ ≤ F(γ) ≤ ⟨ρ_k,ℓ⟩
  have hd := mirror_step_variational_descent
    (mirrorIterate ρ₀ ℓs T k) ℓ T hT hpos hsum
  have hKL0 : (0:ℝ) ≤ T * (∑ v, mirrorStep
      (mirrorIterate ρ₀ ℓs T k) ℓ T v
      * Real.log (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        / mirrorIterate ρ₀ ℓs T k v)) := by
    have hγpos : ∀ v, 0 < mirrorStep
        (mirrorIterate ρ₀ ℓs T k) ℓ T v :=
      mirrorStep_pos _ ℓ T hT hpos
    have hγ1 : ∑ v, mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        = 1 := mirrorStep_sum_one _ ℓ T hT hpos
    have := finite_kl_nonneg (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T)
      (mirrorIterate ρ₀ ℓs T k) hγpos hγ1 hpos hsum
    exact mul_nonneg hT.le this
  linarith

end Hagi.Optimization

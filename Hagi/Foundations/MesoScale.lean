import Mathlib

/-!
# Закон эмерджентности: максимум каузальной силы на мезо-масштабе

Источник №10: Liang Chen (arXiv 2508.12016), "A Law of
Emergence: Maximum Causal Power at the Mesoscale".

Middle-Scale Peak Theorem: Effective Information EI(ℓ) на
масштабе ℓ не монотонен — максимум на мезо-масштабе как
следствие трейд-оффа: усреднение шума растёт с ℓ
(статистическая устойчивость блоков), локальность
взаимодействий режет отклик на больших ℓ. Формализовано
абстрактное ядро: EI(ℓ) = A(ℓ)·L(ℓ), A — фактор усреднения
(рост ≤ a₀ℓ^p), L — фактор локальности (спад ≤ L₀ℓ^{-q}):
при q > p каузальная сила исчезает на макро-масштабах
(EI(ℓ) → 0 при ℓ → ∞) — эмерджентность не живёт на
макро-масштабе, её носитель — мезо-масштаб.
-/

namespace Hagi.Foundations.MesoScale

open Real Filter

/-- ВСПОМОГАТЕЛЬНАЯ: ℓ^r → 0 при r < 0, ℓ → ∞. -/
theorem rpow_tendsto_zero (r : ℝ) (hr : r < 0) :
    Tendsto (fun ℓ : ℝ => ℓ ^ r) atTop (nhds 0) := by
  have hpt : 0 < -r := by nlinarith
  have hinv : Tendsto (fun ℓ : ℝ => ℓ ^ (-r)) atTop atTop :=
    tendsto_rpow_atTop hpt
  have heq : ∀ ℓ : ℝ, 0 < ℓ → ℓ ^ r = (ℓ ^ (-r))⁻¹ := by
    intro ℓ hℓ
    have h := Real.rpow_neg hℓ.le r
    exact (inv_inv (ℓ ^ r)).symm.trans (congrArg (fun x => x⁻¹) h.symm)
  have hev : ∀ᶠ ℓ : ℝ in atTop, ℓ ^ r = (ℓ ^ (-r))⁻¹ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ℓ hℓ
    exact heq ℓ hℓ
  rw [tendsto_congr' hev]
  exact tendsto_inv_atTop_zero.comp hinv

/-- МАКРО-КОЛЛАПС: фактор усреднения растёт не быстрее
степени p, фактор локальности спадает не медленнее степени
q > p — тогда каузальная сила EI(ℓ) = A(ℓ)·L(ℓ) → 0 на
бесконечности: эмерджентность исчезает на макро-масштабе
(ядро Middle-Scale Peak Theorem). -/
theorem macro_collapse (A L : ℝ → ℝ) (a0 L0 : ℝ) (p q : ℝ)
    (ha0 : 0 ≤ a0) (hL0 : 0 ≤ L0)
    (hA : ∀ ℓ, 0 < ℓ → A ℓ ≤ a0 * ℓ ^ p)
    (hAnn : ∀ ℓ, 0 < ℓ → 0 ≤ A ℓ)
    (hL : ∀ ℓ, 0 < ℓ → L ℓ ≤ L0 * ℓ ^ (-q))
    (hLnn : ∀ ℓ, 0 < ℓ → 0 ≤ L ℓ)
    (hpq : p < q) :
    Tendsto (fun ℓ => A ℓ * L ℓ) atTop (nhds 0) := by
  have hbound : ∀ ℓ : ℝ, 0 < ℓ →
      A ℓ * L ℓ ≤ a0 * L0 * ℓ ^ (p - q) := by
    intro ℓ hℓ
    have h1 := hA ℓ hℓ
    have h2 := hL ℓ hℓ
    have hL0q : 0 ≤ L0 * ℓ ^ (-q) :=
      mul_nonneg hL0 (Real.rpow_nonneg hℓ.le _)
    calc A ℓ * L ℓ ≤ A ℓ * (L0 * ℓ ^ (-q)) :=
        mul_le_mul_of_nonneg_left h2 (hAnn ℓ hℓ)
      _ ≤ (a0 * ℓ ^ p) * (L0 * ℓ ^ (-q)) :=
        mul_le_mul h1 le_rfl hL0q
          (mul_nonneg ha0 (Real.rpow_nonneg hℓ.le _))
      _ = a0 * L0 * ℓ ^ (p - q) := by
          conv_rhs => rw [sub_eq_add_neg p q,
            Real.rpow_add hℓ p (-q)]
          ring
  -- сжатие: 0 ≤ EI ≤ C·ℓ^{p−q} → 0
  have hlim : Tendsto (fun ℓ => a0 * L0 * ℓ ^ (p - q))
      atTop (nhds 0) :=
    by simpa using (rpow_tendsto_zero (p - q) (by nlinarith)).const_mul (a0 * L0)
  have hf : ∀ᶠ ℓ : ℝ in atTop, 0 ≤ A ℓ * L ℓ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ℓ hℓ
    exact mul_nonneg (hAnn ℓ hℓ) (hLnn ℓ hℓ)
  have hg : ∀ᶠ ℓ : ℝ in atTop, A ℓ * L ℓ ≤ a0 * L0 * ℓ ^ (p - q) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ℓ hℓ
    exact hbound ℓ hℓ
  exact squeeze_zero' hf hg hlim

open Real Filter Set

/-- МИКРО-КОЛЛАПС: фактор усреднения растёт со скейлом
(ℓ^p, p > 0) — каузальная сила исчезает при ℓ → 0⁺:
эмерджентность не живёт и в микромасштабе (шум). -/
theorem micro_collapse (A L : ℝ → ℝ) (a0 L0 : ℝ) (p : ℝ)
    (ha0 : 0 ≤ a0) (hL0 : 0 ≤ L0)
    (hA : ∀ ℓ, 0 < ℓ → A ℓ ≤ a0 * ℓ ^ p)
    (hAnn : ∀ ℓ, 0 < ℓ → 0 ≤ A ℓ)
    (hL : ∀ ℓ, 0 < ℓ → L ℓ ≤ L0)
    (hLnn : ∀ ℓ, 0 < ℓ → 0 ≤ L ℓ)
    (hp : 0 < p) :
    Tendsto (fun ℓ => A ℓ * L ℓ) (nhdsWithin 0 (Ioi (0:ℝ))) (nhds 0) := by
  have hbound : ∀ ℓ : ℝ, 0 < ℓ →
      A ℓ * L ℓ ≤ a0 * L0 * ℓ ^ p := by
    intro ℓ hℓ
    calc A ℓ * L ℓ ≤ A ℓ * L0 :=
        mul_le_mul_of_nonneg_left (hL ℓ hℓ) (hAnn ℓ hℓ)
      _ ≤ (a0 * ℓ ^ p) * L0 :=
        mul_le_mul (hA ℓ hℓ) le_rfl hL0
          (mul_nonneg ha0 (Real.rpow_nonneg hℓ.le _))
      _ = a0 * L0 * ℓ ^ p := by ring
  have hf : ∀ᶠ ℓ : ℝ in nhdsWithin 0 (Ioi (0:ℝ)), 0 ≤ A ℓ * L ℓ :=
    eventually_nhdsWithin_of_forall (fun ℓ hℓ =>
      mul_nonneg (hAnn ℓ hℓ) (hLnn ℓ hℓ))
  have hg : ∀ᶠ ℓ : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),
      A ℓ * L ℓ ≤ a0 * L0 * ℓ ^ p :=
    eventually_nhdsWithin_of_forall (fun ℓ hℓ => hbound ℓ hℓ)
  have hlim : Tendsto (fun ℓ => a0 * L0 * ℓ ^ p)
      (nhdsWithin 0 (Ioi (0:ℝ))) (nhds 0) := by
    have h1 : Tendsto (fun ℓ : ℝ => (ℓ⁻¹) ^ p)
        (nhdsWithin 0 (Ioi (0:ℝ))) atTop :=
      (tendsto_rpow_atTop hp).comp tendsto_inv_nhdsGT_zero
    have hev : ∀ᶠ ℓ : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),
        ℓ ^ p = (((ℓ⁻¹) ^ p)⁻¹) := by
      filter_upwards [eventually_nhdsWithin_of_forall
        (fun ℓ (hℓ : ℓ ∈ Ioi (0:ℝ)) => hℓ)] with ℓ hℓ
      have hir := Real.inv_rpow hℓ.le p
      rw [hir, inv_inv]
    have hz : Tendsto (fun ℓ : ℝ => ℓ ^ p)
        (nhdsWithin 0 (Ioi (0:ℝ))) (nhds 0) := by
      rw [tendsto_congr' hev]
      exact tendsto_inv_atTop_zero.comp h1
    simpa using hz.const_mul (a0 * L0)
  exact squeeze_zero' hf hg hlim

end Hagi.Foundations.MesoScale

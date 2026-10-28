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

open Real Filter Set

/-- СУЩЕСТВОВАНИЕ МЕЗО-ПИКА (capstone источника №10):
каузальная сила EI непрерывна на (0,∞), неотрицательна,
положительна в ℓ₀ и исчезает на обоих концах шкалы —
глобальный максимум ДОСТИГАЕТСЯ: ∃ lstar, ∀ℓ>0, EI ℓ ≤ EI lstar.
Носитель эмерджентности — мезо-масштаб. -/
theorem meso_peak_exists (EI : ℝ → ℝ)
    (hcont : ContinuousOn EI (Ioi (0:ℝ)))
    (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀) (hpos : 0 < EI ℓ₀)
    (hmacro : Tendsto EI atTop (nhds 0))
    (hmicro : Tendsto EI (nhdsWithin 0 (Ioi (0:ℝ))) (nhds 0)) :
    ∃ lstar, ∀ ℓ, 0 < ℓ → EI ℓ ≤ EI lstar := by
  set c0 := EI ℓ₀ with hc0
  -- макро-хвост: ∃M, ∀ℓ≥M, EI ℓ < c0
  have hM : ∃ M : ℝ, ℓ₀ ≤ M ∧ ∀ ℓ, M ≤ ℓ → EI ℓ < c0 := by
    have hmem : (Iio c0) ∈ nhds (0:ℝ) := Iio_mem_nhds (by nlinarith)
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hmacro hmem)
    refine ⟨max M ℓ₀, le_max_right _ _, fun ℓ hℓ => ?_⟩
    exact hM ℓ (le_trans (le_max_left M ℓ₀) hℓ)
  obtain ⟨M, hℓ₀M, hM⟩ := hM
  -- микро-хвост: ∃ε>0, ε≤ℓ₀, ∀ℓ∈(0,ε], EI ℓ < c0
  have hε : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ℓ₀ ∧ ∀ ℓ, 0 < ℓ → ℓ ≤ ε → EI ℓ < c0 := by
    have hmem : (Iio c0) ∈ nhds (0:ℝ) := Iio_mem_nhds (by nlinarith)
    have hev : (EI ⁻¹' (Iio c0)) ∈ nhdsWithin 0 (Ioi (0:ℝ)) := hmicro hmem
    rw [mem_nhdsWithin] at hev
    obtain ⟨U, hU, hU0, hUp⟩ := hev
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 hU0
    refine ⟨min (δ/2) ℓ₀, lt_min (by nlinarith) hℓ₀, min_le_right _ _, fun ℓ hℓ hℓε => ?_⟩
    have h1 : ℓ ∈ U := hball (show ℓ ∈ Metric.ball 0 δ by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ ℓ - 0)]
      calc ℓ - 0 = ℓ := sub_zero ℓ
        _ ≤ min (δ/2) ℓ₀ := hℓε
        _ < δ := by nlinarith [min_le_left (δ/2) ℓ₀])
    exact hUp ⟨h1, hℓ⟩
  obtain ⟨ε, hεpos, hεℓ₀, hε⟩ := hε
  -- максимум на компакте [ε, M]
  have hsub : Icc ε M ⊆ Ioi (0:ℝ) :=
    fun ℓ hℓ => hεpos.trans_le hℓ.1
  have hcc : ContinuousOn EI (Icc ε M) := hcont.mono hsub
  obtain ⟨lstar, hlmem, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨ℓ₀, hεℓ₀, hℓ₀M⟩ hcc
  refine ⟨lstar, fun ℓ hℓ => ?_⟩
  by_cases hℓM : ℓ ≤ M
  · by_cases hℓε : ε ≤ ℓ
    · exact hmax ⟨hℓε, hℓM⟩
    · -- ℓ < ε: из микро-хвоста EI ℓ < c0 ≤ EI lstar
      have hlt : ℓ ≤ ε := by nlinarith
      have := hε ℓ hℓ hlt
      have hstar : c0 ≤ EI lstar :=
        hmax ⟨hεℓ₀, hℓ₀M⟩
      linarith
  · -- ℓ > M: из макро-хвоста
    have hge : M ≤ ℓ := by nlinarith
    have := hM ℓ hge
    have hstar : c0 ≤ EI lstar := hmax ⟨hεℓ₀, hℓ₀M⟩
    linarith

end Hagi.Foundations.MesoScale

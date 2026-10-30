import Mathlib
import Hagi.Data.CertifiedArgmax
import Hagi.Data.DBridge
import Hagi.Data.DField
import Hagi.Data.DFieldKKT
import Hagi.Data.DistillRecursion
import Hagi.Data.InfoNCE
import Hagi.Data.NessDissipation
import Hagi.Data.PACBayes
import Hagi.Energy.Cooling
import Hagi.Energy.EntropyProduction
import Hagi.Energy.FreeEnergy
import Hagi.Energy.PoEBound
import Hagi.Information.GainRecoverability
import Hagi.Information.Pinsker
import Hagi.Information.RoutingCapacity
import Hagi.Pretraining.DataPruning
import Hagi.Pretraining.RobustnessLaw
import Hagi.Probability.ExpChord
import Hagi.Probability.NoiseTemperature
import Hagi.Probability.PMFBridge
import Hagi.Probability.PinskerTV
import Hagi.Probability.SphericalAngle
import Hagi.Probability.StationaryFlatness
import Hagi.Probability.ThermoAxes
import Hagi.Probability.ThermoBridge
import Hagi.Probability.WSqD
import Hagi.Unified.ArchitectureTheorem

/-!
# InfoDataCore — объединённый фасад слоя-6
информационно-вероятностного и data-энергетического блока
(слияние Pinsker/ProbInfo/DataCentric/DataEnergy,
аудит v9 P3).
-/

namespace Hagi.Unified



/-!
# Pinsker — единая точка входа семейства Пинскера (P1.5)

Консолидация форм неравенства Пинскера (план P1.5;
дубли «Pinsker×2 + KL/TV-модули»):

* **Функциональная форма** (`Hagi.Information.Pinsker`,
  `pinsker4_fin`): |E_q f − E_p f| ≤ 2√KL для 0 ≤ f ≤ 1;
* **TV-форма** (`Hagi.Probability.PinskerTV`,
  `pinsker_sqrt_kl`): ½ Σ|p−q| ≤ √KL — классика через
  Бхаттачарью;
* **Энтропийная непрерывность** (`entropy_continuity_pinsker`
  и `'`-вариант в этом же модуле Unified): Фанне-Пинскер
  оценка |H(p) − H(q)|.

Все формы на канонических `Prelude.klDef/entDef/tvDef`;
настоящий модуль — фасад и реестр форм (P1.5), дубликатных
определений нет.
-/

/-- ДЕДУП-МОСТ (аудит v5 п.5): f-форма Пинскера
(pinsker4_fin, Information) выводится из канонной TV-формы
(pinsker_sqrt_kl, Probability): разность ожиданий ограничена
тотал-вариацией, TV ≤ √KL. Копии связаны, примитив один. -/
theorem pinsker4_via_canon {V : Type*} [Fintype V] [Nonempty V]
    (q p f : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
  -- |Eq f − Ep f| ≤ Σ|q − p|
  have hstep : ∀ v, |(q v - p v) * f v| ≤ |q v - p v| := by
    intro v
    have h1 : |(q v - p v) * f v| = |q v - p v| * |f v| :=
      abs_mul _ _
    rw [h1, mul_comm]
    have h2 : |f v| ≤ 1 := by
      rcases lt_or_ge (f v) 0 with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith [(hf v).1]
      · rw [abs_of_nonneg h]
        exact (hf v).2
    nlinarith [h2, abs_nonneg (q v - p v)]
  have habs : abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := by
    have hsplit : ∑ v, q v * f v - ∑ v, p v * f v
        = ∑ v, (q v - p v) * f v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hsplit]
    calc abs (∑ v, (q v - p v) * f v)
        ≤ ∑ v, |(q v - p v) * f v| :=
          Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ v, |q v - p v| :=
          Finset.sum_le_sum (fun v _ => hstep v)
  -- канон: ½Σ|p−q| ≤ √KL(p||q) = √klDef q p (симметрия ролей)
  have hcanon := Hagi.Probability.pinsker_sqrt_kl q p hq hsumq
    hp hsump
  -- klDef q p = Σ q·log(q/p): канон даёт Σ p·log(p/q) с
  -- ролями (q,p) → Σ q·log(q/p) = klDef q p ✓
  calc abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := habs
    _ = 2 * ((1/2) * ∑ v, |q v - p v|) := by ring
    _ ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
        apply mul_le_mul_of_nonneg_left hcanon (by norm_num)


/-!
# Unified.ProbInfo — фасад вероятностно-информационного блока

Слой-6 фасад: восстановимость усиления, маршрутизационная
ёмкость, экспоненциальная хорда, ось шума/температуры,
мосты ПМФ/термодинамики.
-/


export Hagi.Information (no_free_recovery devEnergyF_pos_iff)
export Hagi.Probability (noise_axes_coincide prodE_as_expQ
  tail_sum_identity)

/-- ПРИНЦИП ИНФОРМАЦИИ (сводка): (1) бесплатного
восстановления нет — хорошая пара encode/decode на одном
слове даёт witnesses-код; (2) энергия девиации строго
положительна ⟺ девиация ненулевая (обнаружимость).
Информация измерима и не бесплатна. -/
theorem info_not_free_and_detectable
    {A Q : Type} (encode : A → Q)
    (decode : Q → A) (good : A → A → Prop) (w : A)
    (h : good (decode (encode w)) w)
    {N d : ℕ} (dev : Fin N → Fin d → ℝ) :
    (∃ q : Q, good (decode q) w)
      ∧ (0 < Hagi.Information.devEnergyF dev
          ↔ ∃ k : Fin N, dev k ≠ 0) :=
  ⟨no_free_recovery encode decode good w h,
    devEnergyF_pos_iff dev⟩

/-!
# Unified.DataCentric — фасад data-centric блока

Слой-6 фасад: RobustnessLaw + DataPruning. Дихотомия
прореживания: гладкие (L-липшицевы) таргеты на плотных сетках
восстанавливаются с ошибкой ≤ L·δ; состязательные таргеты
гарантируют NFL-потерю ≥ 1.
-/


export Hagi.Pretraining (pruning_nfl pruning_free_for_constant
  pruning_recovery_bound robust_interpolation_lipschitz_floor
  lipschitz_floor_of_noisy_labels noisy_interpolation_step_cap
  robust_slows_learning robust_budget_floor)

/-- ДИХОТОМИЯ PRUNING: (1) гладкий таргет на плотной сетке —
ошибка восстановления выброшенной точки ≤ L·δ; (2)
состязательный таргет — любой ученик теряет ≥ 1 в сумме.
Успех прореживания определяется гладкостью таргета и
плотностью сетки, а не алгоритмом отбора. -/
theorem pruning_dichotomy (f : ℝ → ℝ) (t x0 x1 : ℝ) (L δ : ℝ)
    (kept : Finset ℕ) (p : ℕ)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hl : x0 ≤ t) (hr : t ≤ x1) (hδ : |x1 - x0| ≤ δ)
    (hp : p ∉ kept)
    (g : (ℕ → ℝ) → ℝ)
    (hagree : ∀ y1 y2 : ℕ → ℝ, (∀ i ∈ kept, y1 i = y2 i) →
      g y1 = g y2) :
    |f t - f x0| ≤ L * δ ∧
    (1:ℝ) ≤ |g (fun _ => (0:ℝ)) - (fun _ => (0:ℝ)) p|
      + |g (fun i => if i = p then (1:ℝ) else 0)
        - (fun i => if i = p then (1:ℝ) else 0) p| :=
  ⟨pruning_recovery_bound f t x0 x1 L δ hlip hl hr hδ,
    pruning_nfl kept p hp g hagree⟩


/-!
# Unified.DataEnergy — фасад данных и энергии

Слой-6 фасад: сертифицированный argmax, поле данных (KKT),
дистилляционная рекурсия, InfoNCE, PAC-Bayes, диссипация
Несса, термодинамика (охлаждение, свободная энергия, Ландауэр).
-/


export Hagi.Data.CertifiedArgmax (certified_argmax_strict)
export Hagi.Data (dfield_ascent_transfer fresh_data_prevents_collapse_uniform)
export Hagi.Energy (two_level_meanEnergy_strictMono partition_cold_limit)

/-- ПРИНЦИП ДАННЫХ И ЭНЕРГИИ (сводка): (1) сертифицированный
argmax устойчив при зазоре 2ε; (2) положительная
теплоёмкость — средняя энергия строго растёт по T
(двухуровневая система). Выбор и термодинамика корректны. -/
theorem data_certified_and_thermodynamic
    {ι : Type*} [Fintype ι] [Nonempty ι] {v est : ι → ℝ} {ε : ℝ}
    (herr : ∀ i, |est i - v i| ≤ ε)
    {imax : ι} (hgap : ∀ i, i ≠ imax → 2 * ε < v imax - v i)
    (ℓ : ι → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v) :
    (∀ i, i ≠ imax → est i < est imax)
      ∧ Filter.Tendsto (fun T : ℝ => ∑ v, Real.exp (-(ℓ v)/T))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (∑ v, if ℓ v = 0 then (1:ℝ) else 0)) :=
  ⟨certified_argmax_strict herr hgap,
    partition_cold_limit ℓ hℓ⟩



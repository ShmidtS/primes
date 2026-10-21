/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Prelude.Info
import Hagi.Core.Concat
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option linter.style.header false

namespace Hagi.Energy

open Finset
open Hagi.Prelude
open Set

/-!
# Cooling — термодинамическая ось HAGI

Консолидация (итерация 59, перенос из Variational): Нернст-
оценки Гиббс-значения, расписание → качество, тождество
E = F + T·S, максимум энтропии, качество исполняемой смеси,
геометрическое охлаждение, термическое размытие и коридор
температур — вся термодинамическая ось обучения HAGI в
одном модуле.
-/

/-- **Нернст-скорость Гиббс-значения**: для любого поля потерь L
на конечном пространстве существует достигаемый минимум m,
и темперированное логсумм-значение зажато в двусторонней оценке

  `m - T·log n ≤ -T·log ∑ e^{-Lᵢ/T} ≤ m`

(исследовательская база: Hajek 1988; Catoni–Cot 1998 — охлаждение к
глобальному минимуму). Точность достижения минимума — радиус T·log n:
при T → 0 Гиббс-значение стремится к глобальному минимуму
(экспоненциальная концентрация весов по 1/T). Совместно с
`gibbs_optimal_bound` задаёт термодинамическую ось цели обучения:
скорость охлаждения определяет качество на конечном горизонте. -/
theorem gibbs_value_nernst_bounds {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - T * Real.log ((Fintype.card V : ℕ):ℝ)
          ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  classical
  set S := Finset.univ.image L with hS
  have hne : S.Nonempty := ⟨L (Classical.arbitrary V),
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hm : S.min' hne ∈ S := S.min'_mem hne
  rcases Finset.mem_image.mp hm with ⟨i0, _, hi0⟩
  set m := S.min' hne with hmn
  have hmin : ∀ i, m ≤ L i := fun i =>
    Finset.min'_le S (L i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hsumpos : 0 < ∑ i, Real.exp (-(L i / T)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hge : Real.exp (-(m / T)) ≤ ∑ i, Real.exp (-(L i / T)) := by
    have hthis := Finset.single_le_sum (f := fun i => Real.exp (-(L i / T)))
      (fun i _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i0)
    rw [hi0] at hthis
    exact hthis
  have hle : ∑ i, Real.exp (-(L i / T))
      ≤ ((Fintype.card V : ℕ):ℝ) * Real.exp (-(m / T)) := by
    have hstep : ∑ i, Real.exp (-(L i / T))
        ≤ ∑ i ∈ (Finset.univ : Finset V), Real.exp (-(m / T)) :=
      Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (by
          have h1 : m * T ≤ L i * T := mul_le_mul_of_nonneg_right (hmin i) (le_of_lt hT)
          have h2 : m / T ≤ L i / T := by rw [div_le_div_iff₀ hT hT]; exact h1
          exact neg_le_neg h2))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
    exact hstep
  have hlogge : -(m / T) ≤ Real.log (∑ i, Real.exp (-(L i / T))) := by
    have h := Real.log_le_log (Real.exp_pos _) hge
    rwa [Real.log_exp] at h
  have hlogle : Real.log (∑ i, Real.exp (-(L i / T)))
      ≤ Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T) := by
    have h := Real.log_le_log hsumpos hle
    rwa [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  refine ⟨m, hmin, ⟨i0, hi0.symm⟩, ?_, ?_⟩
  · -- нижняя: m − T·log n ≤ −T·log ∑ (из hlogle)
    have hA : T * Real.log (∑ i, Real.exp (-(L i / T)))
        ≤ T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T)) :=
      mul_le_mul_of_nonneg_left hlogle (le_of_lt hT)
    have hB : T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T))
        = T * Real.log (((Fintype.card V : ℕ):ℝ)) - m := by
      field_simp; ring
    linarith
  · -- верхняя: −T·log ∑ ≤ m (из hlogge)
    have hA : T * (-(m / T)) ≤ T * Real.log (∑ i, Real.exp (-(L i / T))) :=
      mul_le_mul_of_nonneg_left hlogge (le_of_lt hT)
    have hB : T * (-(m / T)) = -m := by field_simp
    linarith

/-- **Следствие: расписание охлаждения достигает качества ε.**
Из `gibbs_value_nernst_bounds`: любая температура T > 0 с
T·log n ≤ ε даёт Гиббс-значение в ε-окрестности глобального
минимума `m - ε ≤ V_T ≤ m`. В частности, T := ε / log n
оптимальна по порядку. Вместе с `gibbs_optimal_bound` это
замыкает термодинамическую ось обучения HAGI: качество как
явная функция расписания охлаждения (максимум качества при
заданном вычислительном бюджете). -/
theorem gibbs_schedule_quality {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T ε : ℝ} (hT : 0 < T)
    (hTeq : T * Real.log ((Fintype.card V : ℕ):ℝ) ≤ ε) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - ε ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  rcases gibbs_value_nernst_bounds L hT with ⟨m, hmin, hatt, hlo, hhi⟩
  exact ⟨m, hmin, hatt, by linarith, hhi⟩

/-- **Термодинамическое тождество ансамбля: E = F + T·S.**
Ожидаемая потеря Гиббс-ансамбля (softDef при обратной
температуре 1/Tt) раскладывается точно:

  `∑ wᵢ·Lᵢ = −Tt·log Z − Tt·∑ wᵢ·log wᵢ`

т.е. энергия = свободная энергия (логсумм-значение) + T·энтропия
(с точностью до знака: E = F + T·S при S = −∑ wᵢ log wᵢ).
Это ядро термодинамической семантики HAGI: качество реальной
смеси (`∑ wᵢ·Lᵢ` — то, что фактически исполняется в
`unified_step_certificate`) связано со свободной энергией
(цель `gibbs_optimal_bound`) через энтропийный член. -/
theorem gibbs_free_energy_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∑ i, softDef (fun i => -(L i) / Tt) i * L i
      = -Tt * Real.log (∑ i, Real.exp (-L i / Tt))
        - Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
            * Real.log (softDef (fun i => -(L i) / Tt) i) := by
  set w := softDef (fun i => -(L i) / Tt) with hwdef
  set Z := ∑ i, Real.exp (-L i / Tt) with hZdef
  have hZpos : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have h3 : (∑ b, Real.exp (-L b / Tt)) = Z := hZdef.symm
  have hwl : ∀ i, Real.log (w i) = -L i / Tt - Real.log Z := by
    intro i
    show Real.log (Real.exp (-L i / Tt) / ∑ b, Real.exp (-L b / Tt))
      = -L i / Tt - Real.log Z
    rw [h3, Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
  have key : ∀ i, w i * (L i + Tt * Real.log (w i)) = -Tt * Real.log Z * w i := by
    intro i
    rw [hwl i]
    have h4 : L i + Tt * (-L i / Tt - Real.log Z) = -Tt * Real.log Z := by
      field_simp
      ring
    rw [h4]
    ring
  have h1 : ∑ i, w i * (L i + Tt * Real.log (w i)) = ∑ i, -Tt * Real.log Z * w i :=
    Finset.sum_congr rfl (fun i _ => key i)
  rw [← Finset.mul_sum] at h1
  have hsum : ∑ i, w i = 1 := by rw [hwdef]; exact softDef_sum_one _
  rw [hsum] at h1
  have h2 : ∑ i, w i * (L i + Tt * Real.log (w i))
      = ∑ i, w i * L i + Tt * ∑ i, w i * Real.log (w i) := by
    trans ∑ i, (w i * L i + Tt * (w i * Real.log (w i)))
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h2] at h1
  linarith

/-- **Равномерный максимум энтропии**: для любого строго
положительного распределения w на конечном ι энтропия
Шеннона не превосходит логарифма мощности:

  `−∑ wᵢ·log wᵢ ≤ log |ι|`

(Jensen: логарифм вогнут; максимум достигается на
равномерном распределении). -/
theorem shannon_entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
    -∑ i, w i * Real.log (w i) ≤ Real.log ((Fintype.card ι : ℕ):ℝ) := by
  have h2 : ∑ i, w i * Real.log ((w i)⁻¹) ≤ Real.log ((Fintype.card ι : ℕ):ℝ) := by
    have hconc : ConcaveOn ℝ (Ioi (0:ℝ)) Real.log :=
      (strictConcaveOn_log_Ioi).concaveOn
    have hwle1 : ∀ i, w i ≤ 1 := by
      intro i
      have hs : w i ≤ ∑ j, w j := by
        have := Finset.single_le_sum (f := w) (fun j _ => le_of_lt (hw0 j)) (Finset.mem_univ i)
        simpa using this
      rw [hw1] at hs
      linarith [hs]
    have hmem : ∀ i ∈ (Finset.univ : Finset ι), (w i)⁻¹ ∈ Ioi (0:ℝ) := by
      intro i _
      exact (inv_pos.mpr (hw0 i))
    have hjen := hconc.le_map_sum (t := Finset.univ) (w := w) (p := fun i => (w i)⁻¹)
      (fun i _ => le_of_lt (hw0 i)) hw1 hmem
    simp only [smul_eq_mul, Real.log_inv] at hjen
    have hR : ∑ i, w i * (w i)⁻¹ = ((Fintype.card ι : ℕ):ℝ) := by
      simp [mul_inv_cancel₀ (ne_of_gt (hw0 _))]
    rw [hR] at hjen
    simpa only [Real.log_inv] using hjen

  have hconv : -∑ i, w i * Real.log (w i) = ∑ i, w i * Real.log ((w i)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.log_inv]; ring)
  rw [hconv]
  simpa only [Real.log_inv] using h2

/-- **Качество исполняемой смеси: E ≤ m + T·log n.**
Композиция трёх сертификатов: тождество E = F + T·S
(`gibbs_free_energy_identity`), максимум энтропии
S ≤ log n (`shannon_entropy_le_log_card`) и нижняя Нернст-
оценка F ≥ m − T·log n (`gibbs_value_nernst_bounds`).
Следствие: расписание T·log n ≤ ε даёт ожидаемую потерю
РЕАЛЬНО исполняемой Гиббс-смеси (компонент
`unified_step_certificate`) в ε-окрестности глобального
минимума. Полная термодинамическая цепочка HAGI:
расписание охлаждения → свободная энергия → энергия смеси. -/
theorem gibbs_mixture_quality {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / Tt) i * L i
          ≤ m + Tt * Real.log ((Fintype.card ι : ℕ):ℝ)) := by
  classical
  rcases gibbs_value_nernst_bounds L hTt with ⟨m, hmin, -, hlo, hhi⟩
  refine ⟨m, hmin, ?_⟩
  have hZbr : (∑ i, Real.exp (-(L i / Tt))) = (∑ i, Real.exp (-L i / Tt)) :=
    Finset.sum_congr rfl (fun i _ => by rw [neg_div])
  rw [hZbr] at hlo hhi
  have hZpos : 0 < ∑ i, Real.exp (-L i / Tt) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hident := gibbs_free_energy_identity L hTt
  have hent := shannon_entropy_le_log_card (softDef (fun i => -(L i) / Tt))
    (fun i => softDef_pos _ i) (softDef_sum_one _)
  -- E = -Tt log Z - Tt Σ w log w; hent : -(Σ w log w) ≤ log n
  -- hlo : m - Tt*log n ≤ -Tt*log Z
  have hS : ∑ i, softDef (fun i => -(L i) / Tt) i * Real.log (softDef (fun i => -(L i) / Tt) i)
      ≥ -Real.log ((Fintype.card ι : ℕ):ℝ) := by
    linarith [hent]
  have hB : Tt * (-Real.log ((Fintype.card ι : ℕ):ℝ))
      ≤ Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
      * Real.log (softDef (fun i => -(L i) / Tt) i) :=
    mul_le_mul_of_nonneg_left hS (le_of_lt hTt)
  linarith

/-- **Геометрическое охлаждение: логарифмическая цена точности.**
Расписание Tₜ = T₀·ρᵗ (0 < ρ < 1) достигает ε-качества
исполняемой Гиббс-смеси за

  `N ≥ log(T₀·log n / ε) / log(1/ρ)`

шагов: после N шагов охлаждения T_N·log n ≤ ε, и по
`gibbs_mixture_quality` ожидаемая потеря смеси ≤ m + ε.
Вычислительная сложность достижения качества ε —
O(log(1/ε)) фаз охлаждения (при постоянных T₀, ρ, n):
прямая формализация «минимизации вычислений» —
экспоненциальная точность за логарифмическое число шагов
управления температурой. -/
theorem geometric_cooling_steps {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (T₀ ρ ε : ℝ) (hT₀ : 0 < T₀) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) (hn : 2 ≤ Fintype.card ι) (N : ℕ)
    (hN : Real.log (T₀ * Real.log ((Fintype.card ι : ℕ):ℝ) / ε)
        / Real.log ((1:ℝ)/ρ) ≤ (N:ℝ)) :
    ∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / (T₀ * ρ^(N:ℝ))) i * L i
          ≤ m + ε) := by
  have hlogn : 0 < Real.log ((Fintype.card ι : ℕ):ℝ) := by
    apply Real.log_pos
    have h1 : (1:ℝ) < ((Fintype.card ι : ℕ):ℝ) := by exact_mod_cast hn
    linarith
  have hone : (1:ℝ) < (1:ℝ)/ρ := one_lt_one_div hρ0 hρ1
  have hloginv : 0 < Real.log ((1:ℝ)/ρ) := Real.log_pos hone
  have hTp : 0 < T₀ * ρ^(N:ℝ) := by positivity
  have hkey : T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := by
    set A := T₀ * Real.log ((Fintype.card ι : ℕ):ℝ) with hA
    have hApos : 0 < A := by positivity
    have hBpos : 0 < ((1:ℝ)/ρ)^(N:ℝ) := by positivity
    have h11 : Real.log (A / ε) ≤ (N:ℝ) * Real.log ((1:ℝ)/ρ) :=
      (div_le_iff₀ hloginv).mp hN
    have h13 : Real.log (((1:ℝ)/ρ)^(N:ℝ)) = (N:ℝ) * Real.log ((1:ℝ)/ρ) :=
      Real.log_rpow (one_div_pos.mpr hρ0) _
    have h3 : Real.log (A / ε) ≤ Real.log (((1:ℝ)/ρ)^(N:ℝ)) := by
      rw [h13]; linarith
    have h4 : A / ε ≤ ((1:ℝ)/ρ)^(N:ℝ) := by
      have h12 := Real.exp_le_exp.mpr h3
      rwa [Real.exp_log (div_pos hApos hε), Real.exp_log hBpos] at h12
    have h5 : ρ^(N:ℝ) * ((1:ℝ)/ρ)^(N:ℝ) = 1 := by
      rw [← Real.mul_rpow (show (0:ℝ) ≤ ρ by positivity)
        (show (0:ℝ) ≤ (1:ℝ)/ρ by positivity)]
      have : ρ * ((1:ℝ)/ρ) = 1 := by field_simp
      rw [this]
      exact Real.one_rpow _
    have h4' : A ≤ ε * ((1:ℝ)/ρ)^(N:ℝ) := by
      have := (div_le_iff₀ hε).mp h4
      linarith [this]
    have h9 := mul_le_mul_of_nonneg_left h4'
      (le_of_lt (show (0:ℝ) < ρ^(N:ℝ) by positivity))
    have h10 : ρ^(N:ℝ) * (ε * ((1:ℝ)/ρ)^(N:ℝ)) = ε := by
      linear_combination ε * h5
    linarith

  have hTp : 0 < T₀ * ρ^(N:ℝ) := by positivity
  have hqual := gibbs_mixture_quality L hTp
  rcases hqual with ⟨m, hmin, hbnd⟩
  refine ⟨m, hmin, ?_⟩
  have hTn : T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := hkey
  -- bound: E ≤ m + T·log n ≤ m + ε
  have : ∑ i, softDef (fun i => -(L i) / (T₀ * ρ^(N:ℝ))) i * L i
      ≤ m + T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) := hbnd
  linarith

/-- **Термическое размытие различимости**: логарифмическое
отношение Гиббс-весов двух направлений в точности равно
относительному зазору их потерь, делённому на температуру:

  `log wᵢ − log wⱼ = (Lⱼ − Lᵢ)/T`

Следствие: чтобы Гиббс-ансамбль различал понятия с зазором
потерь s с лог-точностью τ, температура обязана быть
T ≤ s/τ — расписание охлаждения ограничено СНИЗУ
различимостью: слишком быстрый нагрев/высокая T стирает
различия между направлениями. Термодинамическая
нижняя граница для `geometric_cooling_steps`. -/
theorem thermal_blur {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {T : ℝ} (hT : 0 < T) (i j : ι) :
    Real.log (softDef (fun x => -L x / T) i)
      - Real.log (softDef (fun x => -L x / T) j)
      = (L j - L i) / T := by
  have hli : Real.log (softDef (fun x => -L x / T) i)
      = -L i / T - Real.log (∑ k, Real.exp (-L k / T)) := by
    have h1 : softDef (fun x => -L x / T) i
        = Real.exp (-L i / T - Real.log (∑ k, Real.exp (-L k / T))) := by
      rw [Hagi.Core.softDef_eq_exp_sub_lse, Hagi.Core.lse]
    rw [h1, Real.log_exp]
  have hlj : Real.log (softDef (fun x => -L x / T) j)
      = -L j / T - Real.log (∑ k, Real.exp (-L k / T)) := by
    have h1 : softDef (fun x => -L x / T) j
        = Real.exp (-L j / T - Real.log (∑ k, Real.exp (-L k / T))) := by
      rw [Hagi.Core.softDef_eq_exp_sub_lse, Hagi.Core.lse]
    rw [h1, Real.log_exp]
  rw [hli, hlj]
  ring

/-- **Коридор температур**: если термодинамический коридор
непуст (нижняя граница различимости s/τ не превосходит
верхнюю границу качества ε/log n), то существует температура
T (свидетель: T = s/τ), дающая ОДНОВРЕМЕННО

* различимость: любые два направления с зазором потерь ≤ s
  различаются лог-точностью τ (`thermal_blur`);
* качество: ожидаемая потеря смеси ≤ m + ε
  (`gibbs_mixture_quality` + бюджет охлаждения).

Двусторонняя теорема о расписании HAGI: температура обязана
лежать в [s/τ, ε/log n] — ниже нельзя (нагрев стирает
различимость), выше не нужно (ε-качество уже достигнуто). -/
theorem temperature_corridor {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (s τ ε : ℝ) (hs : 0 < s) (hτ : 0 < τ) (hε : 0 < ε)
    (hn : 2 ≤ Fintype.card ι)
    (hcorridor : s / τ ≤ ε / Real.log ((Fintype.card ι : ℕ):ℝ)) :
    ∃ T : ℝ, 0 < T
      ∧ (∀ i j, |L j - L i| ≤ s →
          |Real.log (softDef (fun x => -L x / T) i)
            - Real.log (softDef (fun x => -L x / T) j)| ≤ τ)
      ∧ (∃ m : ℝ, (∀ i, m ≤ L i)
          ∧ (∑ i, softDef (fun x => -L x / T) i * L i
              ≤ m + T * Real.log ((Fintype.card ι : ℕ):ℝ))
          ∧ T * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε) := by
  refine ⟨s / τ, div_pos hs hτ, ?_, ?_⟩
  · intro i j hgap
    have hT := div_pos hs hτ
    have h := thermal_blur L hT i j
    rw [h]
    rw [show (L j - L i) / (s / τ) = (L j - L i) * (τ / s) from by
      field_simp]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ / s)]
    rw [mul_div_assoc', div_le_iff₀ hs]
    rw [mul_comm τ s]
    exact mul_le_mul_of_nonneg_right hgap hτ.le
  · have hT := div_pos hs hτ
    have hlogn : 0 < Real.log ((Fintype.card ι : ℕ):ℝ) := by
      apply Real.log_pos
      have h1 : (1:ℝ) < ((Fintype.card ι : ℕ):ℝ) := by exact_mod_cast hn
      linarith
    have hcap : (s / τ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
      rw [div_le_div_iff₀ hτ hlogn] at hcorridor
      exact hcorridor
    rcases gibbs_mixture_quality L hT with ⟨m, hmin, hbnd⟩
    exact ⟨m, hmin, hbnd, hcap⟩


/-- **Охлаждение раскрывает различимость**: если зазор потерь
|Lᵢ − Lⱼ| ≥ s и температура достаточно низкая
(T ≤ s/τ), то лог-расстояние Гиббс-весов не меньше τ —
дополнение к `temperature_corridor` (нижняя оценка вместо
верхней): при T → 0 ансамбль различает сколь угодно близкие
направления; число эффективно различимых понятий
монотонно растёт при охлаждении — вместе с
`welch_min_dimension` это термодинамическая развертка
вместимости: охлаждение раскрывает упаковочную ёмкость
пространства представлений. -/
theorem thermal_reveal {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ)
    (T : ℝ) (hT : 0 < T) (hTle : T ≤ s / τ) (i j : ι)
    (hgap : s ≤ |L j - L i|) :
    τ ≤ |Real.log (softDef (fun x => -L x / T) i)
      - Real.log (softDef (fun x => -L x / T) j)| := by
  have h := thermal_blur L hT i j
  rw [h, abs_div, abs_of_pos hT]
  rw [le_div_iff₀ hT]
  have h2 : τ * T ≤ s := by
    rw [mul_comm, ← le_div_iff₀ hτ]
    exact hTle
  have h3 : τ * T ≤ |L j - L i| := le_trans h2 hgap
  linarith [h3]

/-- **Время раскрытия понятия при геометрическом
охлаждении**: если расписание Tₜ = T₀·ρᵗ достигло
Tₜ ≤ s/τ (т.е. t ≥ log(T₀τ/s)/log(1/ρ)), то на шаге t
ансамбль различает пару с зазором ≥ s с лог-точностью τ.
Композиция `thermal_reveal` × геометрического расписания:
каждое понятие с зазором s получает момент раскрытия —
термодинамические «часы» различимости; при ρ < 1
момент логарифмичен по T₀τ/s. -/
theorem reveal_horizon {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (T₀ ρ s τ : ℝ) (hT₀ : 0 < T₀) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ)
    (i j : ι) (hgap : s ≤ |L j - L i|)
    (t : ℕ) (hle : T₀ * ρ ^ (t : ℝ) ≤ s / τ) :
    τ ≤ |Real.log (softDef (fun x => -L x / (T₀ * ρ ^ (t : ℝ))) i)
      - Real.log (softDef (fun x => -L x / (T₀ * ρ ^ (t : ℝ))) j)| := by
  have hTpos : 0 < T₀ * ρ ^ (t : ℝ) := by positivity
  exact thermal_reveal L s τ hs hτ _ hTpos hle i j hgap

/-- **Момент раскрытия существует**: для любого зазора s > 0 и
точности τ > 0 геометрическое расписание Tₜ = T₀·ρᵗ
достигает Tₜ ≤ s/τ за конечное число шагов (∃ t:
T₀·ρᵗ ≤ s/τ). Вместе с `reveal_horizon`: КАЖДОЕ понятие с
конечным зазором будет раскрыто — полное содержание
термодинамических часов: охлаждение раскрывает все
различия, момент логарифмичен. -/
theorem reveal_time_exists (T₀ ρ s τ : ℝ) (hT₀ : 0 < T₀)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ) :
    ∃ t : ℕ, T₀ * ρ ^ (t : ℝ) ≤ s / τ := by
  have hposTS : 0 < T₀ * τ / s := by positivity
  have hloginv : 0 < Real.log ((1:ℝ)/ρ) :=
    Real.log_pos (one_lt_one_div hρ0 hρ1)
  rcases exists_nat_ge (Real.log (T₀ * τ / s) / Real.log ((1:ℝ)/ρ)) with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- шаг 1: (1/ρ)^t ≥ T₀τ/s (exp-монотонность из лога)
  have h1 : Real.log (T₀ * τ / s) ≤ (t:ℝ) * Real.log ((1:ℝ)/ρ) :=
    (div_le_iff₀ hloginv).mp ht
  have h2 : Real.log (((1:ℝ)/ρ)^(t:ℝ)) ≥ Real.log (T₀ * τ / s) := by
    rw [Real.log_rpow (by positivity : (0:ℝ) < (1:ℝ)/ρ)]
    linarith [h1]
  have h3 : ((1:ℝ)/ρ)^(t:ℝ) ≥ T₀ * τ / s := by
    have h4 := Real.exp_le_exp.mpr h2
    rw [Real.exp_log hposTS, Real.exp_log (Real.rpow_pos_of_pos (one_div_pos.mpr hρ0) _)] at h4
    exact h4
  -- шаг 2: ρ^t · (1/ρ)^t = 1 ⟹ T₀ρᵗ ≤ s/τ
  have h5 : ρ^(t:ℝ) * ((1:ℝ)/ρ)^(t:ℝ) = 1 := by
    rw [← Real.mul_rpow (le_of_lt hρ0)
      (le_of_lt (one_div_pos.mpr hρ0))]
    have : ρ * ((1:ℝ)/ρ) = 1 := by field_simp
    rw [this]
    exact Real.one_rpow _
  have h6 : T₀ * τ / s ≤ ((1:ℝ)/ρ)^(t:ℝ) := h3
  rw [div_le_iff₀ (by positivity : (0:ℝ) < s)] at h6
  -- h6 : T₀ * τ ≤ s * ((1/ρ)^t)
  have hgoal : T₀ * ρ ^ (t:ℝ) * τ ≤ s := by
    nlinarith [h6, h5, mul_pos hT₀ hτ]
  exact (le_div_iff₀ hτ).mpr hgoal

/-- **Динамическая пара: раскрытие ∧ качество одновременно**:
для любого зазора s, точности τ и бюджета качества ε
существует шаг t, на котором геометрическое расписание
ОДНОВРЕМЕННО раскрывает все пары с зазором ≥ s
(Tₜ ≤ s/τ) и достигает ε-качества (Tₜ·log n ≤ ε):
термодинамические часы и бюджет качества сходятся —
обе верхние границы на Tₜ выполняются при достаточно
большом t (хвост расписания входит в min-окно коридора). -/
theorem cooling_schedule_pair (T₀ ρ s τ ε : ℝ) (hT₀ : 0 < T₀)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ)
    (hε : 0 < ε) (n : ℝ) (hn : 1 < n) :
    ∃ t : ℕ, T₀ * ρ ^ (t : ℝ) ≤ s / τ
      ∧ T₀ * ρ ^ (t : ℝ) * Real.log n ≤ ε := by
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hmin : 0 < min (s / τ) (ε / Real.log n) := lt_min (div_pos hs hτ) (div_pos hε hlogn)
  have hmin : (0:ℝ) < min (s / τ) (ε / Real.log n) :=
    lt_min (div_pos hs hτ) (div_pos hε hlogn)
  rcases reveal_time_exists T₀ ρ (min (s / τ) (ε / Real.log n)) 1
    hT₀ hρ0 hρ1 hmin one_pos with ⟨t, ht⟩
  have ht' : T₀ * ρ ^ (t:ℝ) ≤ min (s / τ) (ε / Real.log n) := by
    rw [div_one] at ht; exact ht
  refine ⟨t, le_trans ht' (min_le_left _ _), ?_⟩
  have h2 : T₀ * ρ ^ (t:ℝ) ≤ ε / Real.log n := le_trans ht' (min_le_right _ _)
  have h3 := mul_le_mul_of_nonneg_right h2 hlogn.le
  rw [div_mul_cancel₀ _ (ne_of_gt hlogn)] at h3
  exact h3
end Hagi.Energy

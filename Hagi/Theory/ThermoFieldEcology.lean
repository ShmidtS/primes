/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.BlockAdmission
import Hagi.Theory.MDLPrune

/-!
# ThermoFieldEcology — полевая экология частиц поверх замороженного ствола

Бесградиентный слой над предвычисленным стволом. Популяция из `N` частиц
читает выход ствола и общее поле памяти `F ∈ ℝ^C`, пишет только в поле и в
остаток логитов. Энергия частицы — снижение CE на отложенном срезе минус
налог за память и вычисления; частица с неположительной энергией удаляется,
выжившие реплицируются. Всё конечно и безусловно.

* «Солнечный свет» — остаточный сюрприз: где база уверена, света нет.
* Поле затухает и ограничено (`field_bound`).
* Readout — ковариация активности с остатком через Gram-матрицу остатков.
* Смерть от налога за конечное число поколений (`starvation_generations`).
* Отбор не хуже полного состава (`selection_dominates`).
* Органоид допускается только через LCB-гейт (`organoid_admission_improves`).
-/

namespace Hagi.Theory.ThermoFieldEcology

open Finset Filter

/-! ### Солнечный свет: остаточный сюрприз -/

/-- Свет в позиции: превышение сюрприза базы над порогом; `0`, где база уверена. -/
noncomputable def sunlight (τ p : ℝ) : ℝ := max 0 (-Real.log p - τ)

theorem sunlight_nonneg (τ p : ℝ) : 0 ≤ sunlight τ p := le_max_left _ _

/-- Где база уверена (`p = 1`), света нет. -/
theorem sunlight_eq_zero (τ : ℝ) (hτ : 0 ≤ τ) : sunlight τ 1 = 0 := by
  have : -Real.log (1:ℝ) - τ = -τ := by simp
  rw [sunlight, this, max_eq_left (by linarith)]

/-- Порог только срезает: на вероятностях суммарный свет не больше суммы сюрпризов. -/
theorem sunlight_sum_le {n : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (p : Fin n → ℝ) (hp : ∀ t, 0 < p t ∧ p t ≤ 1) :
    ∑ t, sunlight τ (p t) ≤ ∑ t, -Real.log (p t) := by
  refine Finset.sum_le_sum fun t _ => ?_
  have hpos := (hp t).1
  have hlog : 0 ≤ -Real.log (p t) := by
    have : Real.log (p t) ≤ 0 := Real.log_nonpos hpos.le (hp t).2
    linarith
  rw [sunlight, max_le_iff]
  exact ⟨hlog, by linarith⟩

/-! ### Поле памяти и его ограниченность -/

/-- Шаг поля в канале `c`: затухание плюс запись частиц. -/
noncomputable def fieldStep {C N : ℕ} (α : Fin C → ℝ) (w : Fin N → Fin C → ℝ)
    (a : Fin N → ℝ) (F : Fin C → ℝ) (c : Fin C) : ℝ := α c * F c + ∑ i, a i * w i c
noncomputable def field {C N : ℕ} (α : Fin C → ℝ) (w : Fin N → Fin C → ℝ)
    (a : ℕ → Fin N → ℝ) (F₀ : Fin C → ℝ) : ℕ → Fin C → ℝ
  | 0 => F₀
  | g + 1 => fun c => fieldStep α w (a g) (field α w a F₀ g) c

/-- Поле ограничено: при `0 ≤ α₀ < 1`, `|α| ≤ α₀`, `|a| ≤ A`, `|w| ≤ W` канал поля не
превышает `α₀^g·|F₀ c| + A·W·N/(1 − α₀)` — записанная без пользы масса
затухает, а не накапливается. -/
theorem field_bound {C N : ℕ} (α : Fin C → ℝ) (w : Fin N → Fin C → ℝ)
    (a : ℕ → Fin N → ℝ) (F₀ : Fin C → ℝ) (c : Fin C) (α₀ A W : ℝ)
    (hα0 : 0 ≤ α₀) (hα1 : α₀ < 1) (hα : ∀ c', |α c'| ≤ α₀)
    (hA0 : 0 ≤ A) (hW0 : 0 ≤ W) (hA : ∀ g i, |a g i| ≤ A) (hW : ∀ i c', |w i c'| ≤ W) (g : ℕ) :
    |field α w a F₀ g c| ≤ α₀ ^ g * |F₀ c| + A * W * N / (1 - α₀) := by
  induction g with
  | zero =>
      rw [field]
      simp only [pow_zero, one_mul, le_add_iff_nonneg_right]
      positivity
  | succ g ih =>
      show |α c * field α w a F₀ g c + ∑ i, a g i * w i c| ≤ _
      have h1 : |α c * field α w a F₀ g c| ≤ α₀ * |field α w a F₀ g c| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hα c) (abs_nonneg _)
      have h2 : ∑ i, |a g i * w i c| ≤ A * W * N := by
        calc ∑ i, |a g i * w i c| ≤ ∑ i, A * W := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              exact mul_le_mul (hA g i) (hW i c) (abs_nonneg _) hA0
          _ = A * W * N := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have h3 : |α c * field α w a F₀ g c + ∑ i, a g i * w i c| ≤
          |α c * field α w a F₀ g c| + ∑ i, |a g i * w i c| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
      have h4 := h3.trans (add_le_add h1 h2)
      have h5 : A * W * N ≤ α₀ * (A * W * N / (1 - α₀)) + A * W * N := by
        have : (0:ℝ) ≤ α₀ * (A * W * N / (1 - α₀)) := by positivity
        linarith
      have h6 : α₀ * (α₀ ^ g * |F₀ c| + A * W * N / (1 - α₀)) + A * W * N =
          α₀ ^ (g + 1) * |F₀ c| + A * W * N / (1 - α₀) := by
        rw [pow_succ]
        have : (1 - α₀) ≠ (0:ℝ) := by linarith
        field_simp
        ring
      calc |α c * field α w a F₀ g c + ∑ i, a g i * w i c|
          ≤ α₀ * |field α w a F₀ g c| + A * W * N := h4
        _ ≤ α₀ * (α₀ ^ g * |F₀ c| + A * W * N / (1 - α₀)) + A * W * N :=
            add_le_add (mul_le_mul_of_nonneg_left ih hα0) (le_refl _)
        _ = _ := h6


/-! ### Ковариационный readout -/

/-- Остаточная ошибка ствола: one-hot цели минус предсказание базы. -/
noncomputable def trunkResidual {n : ℕ} (y : ℕ → Fin n) (p : ℕ → Fin n → ℝ) (t : ℕ) (c : Fin n) : ℝ :=
  (if y t = c then 1 else 0) - p t c
noncomputable def readout {n N : ℕ} (y : ℕ → Fin n) (p : ℕ → Fin n → ℝ) (T : ℕ)
    (a : Fin N → ℕ → ℝ) (i : Fin N) (c : Fin n) : ℝ :=
  ∑ t ∈ Finset.range T, a i t * trunkResidual y p t c

/-- Readout — взвешенная сумма остатков; свёртка двух readout — билинейная
форма активностей через Gram-матрицу остатков. -/
theorem readout_inner_eq_gram {n N : ℕ} (y : ℕ → Fin n) (p : ℕ → Fin n → ℝ) (T : ℕ)
    (a : Fin N → ℕ → ℝ) (i j : Fin N) :
    ∑ c, readout y p T a i c * readout y p T a j c =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, a i t * a j s *
        ∑ c, trunkResidual y p t c * trunkResidual y p s c := by

  -- canonical form on both sides: Σ_c Σ_t Σ_s (a i t r_t c) (a j s r_s c)
  have L : ∑ c, readout y p T a i c * readout y p T a j c =
      ∑ c, ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
        a i t * trunkResidual y p t c * (a j s * trunkResidual y p s c) := by
    simp only [readout, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have R : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, a i t * a j s *
        ∑ c, trunkResidual y p t c * trunkResidual y p s c =
      ∑ c, ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
        a i t * trunkResidual y p t c * (a j s * trunkResidual y p s c) := by
    have h1 : ∀ t s, a i t * a j s * ∑ c, trunkResidual y p t c * trunkResidual y p s c =
        ∑ c, a i t * trunkResidual y p t c * (a j s * trunkResidual y p s c) := by
      intro t s
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [h1]
    -- Σ_t Σ_s Σ_c → Σ_c Σ_t Σ_s
    have e1 : ∀ t, (∑ s ∈ Finset.range T, ∑ c, a i t * trunkResidual y p t c * (a j s * trunkResidual y p s c)) =
        ∑ c, ∑ s ∈ Finset.range T, a i t * trunkResidual y p t c * (a j s * trunkResidual y p s c) :=
      fun t => Finset.sum_comm
    simp only [e1]
    rw [Finset.sum_comm]
  rw [L, R]

/-- Самосвёртка readout неотрицательна: энергия направленного отклика. -/
theorem readout_self_nonneg {n N : ℕ} (y : ℕ → Fin n) (p : ℕ → Fin n → ℝ) (T : ℕ)
    (a : Fin N → ℕ → ℝ) (i : Fin N) :
    0 ≤ ∑ c, readout y p T a i c * readout y p T a i c :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-! ### Энергия, метаболизм, смерть -/

/-- Энергия частицы: `E g+1 = γ·E g + ΔCE g − tax`. -/
noncomputable def energy (γ : ℝ) (ΔCE : ℕ → ℝ) (tax E₀ : ℝ) : ℕ → ℝ
  | 0 => E₀
  | g + 1 => γ * energy γ ΔCE tax E₀ g + ΔCE g - tax

theorem energy_zero (γ : ℝ) (ΔCE : ℕ → ℝ) (tax E₀ : ℝ) : energy γ ΔCE tax E₀ 0 = E₀ := rfl

/-- Сдвиг геометрической суммы: `1 + γ·Σ_{k<g} γ^k = Σ_{k<g+1} γ^k`. -/
theorem geom_shift (γ : ℝ) (g : ℕ) : 1 + γ * ∑ k ∈ Finset.range g, γ ^ k = ∑ k ∈ Finset.range (g + 1), γ ^ k := by
  rw [Finset.sum_range_succ]
  have key : (1 - γ) * ∑ k ∈ Finset.range g, γ ^ k = 1 - γ ^ g := by
    by_cases h : γ = 1
    · subst h; simp
    · have := geom_sum_eq (x := γ) h g
      rw [this]; field_simp; ring
  have : 1 + γ * ∑ k ∈ Finset.range g, γ ^ k - (∑ k ∈ Finset.range g, γ ^ k + γ ^ g) = 0 := by
    have := key
    nlinarith [this]
  linarith [this]


/-- Без света энергия не выше геометрически затухающего старта минус накопленный налог. -/
theorem energy_le_of_no_light (γ : ℝ) (ΔCE : ℕ → ℝ) (tax E₀ : ℝ) (hγ : 0 ≤ γ)
    (hCE : ∀ g, ΔCE g ≤ 0) (g : ℕ) :
    energy γ ΔCE tax E₀ g ≤ γ ^ g * E₀ - tax * ∑ k ∈ Finset.range g, γ ^ k := by
  induction g with
  | zero => simp [energy]
  | succ g ih =>
      have h := mul_le_mul_of_nonneg_left ih hγ
      rw [energy, ← geom_shift]
      have e1 : γ * (γ ^ g * E₀ - tax * ∑ k ∈ Finset.range g, γ ^ k) - tax =
          γ * γ ^ g * E₀ - tax * (1 + γ * ∑ k ∈ Finset.range g, γ ^ k) := by ring
      calc γ * energy γ ΔCE tax E₀ g + ΔCE g - tax
          ≤ γ * (γ ^ g * E₀ - tax * ∑ k ∈ Finset.range g, γ ^ k) + ΔCE g - tax :=
            sub_le_sub (add_le_add h (le_refl _)) (le_refl _)
        _ ≤ γ * (γ ^ g * E₀ - tax * ∑ k ∈ Finset.range g, γ ^ k) - tax := by linarith [hCE g]
        _ = γ ^ (g + 1) * E₀ - tax * (1 + γ * ∑ k ∈ Finset.range g, γ ^ k) := by
            have hp : γ ^ (g + 1) = γ * γ ^ g := by rw [pow_succ]; ring
            rw [hp]
            ring

/-- Затухающий множитель сколь угодно мал: `γ^g < δ` для некоторого `g`. -/
theorem pow_eventually_lt (γ δ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hδ : 0 < δ) :
    ∃ g, γ ^ g < δ := by
  have hpow : Tendsto (fun g : ℕ => γ ^ g) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
  obtain ⟨g, hg⟩ := Filter.Eventually.exists (hpow.eventually (gt_mem_nhds hδ))
  exact ⟨g, hg⟩

/-- Частица голодает за конечное число поколений: `γ < 1`, свет неположителен,
налог положителен ⇒ энергия становится неположительной. -/
theorem starvation_generations (γ : ℝ) (ΔCE : ℕ → ℝ) (tax E₀ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hCE : ∀ g, ΔCE g ≤ 0) (htax : 0 < tax) :
    ∃ g, energy γ ΔCE tax E₀ g ≤ 0 := by
  by_cases hE : E₀ ≤ 0
  · exact ⟨0, by simpa [energy_zero] using hE⟩
  have h1 : (0:ℝ) < 1 - γ := by linarith
  have hden : (0:ℝ) < tax + E₀ * (1 - γ) :=
    add_pos_of_pos_of_nonneg htax (mul_nonneg (lt_of_not_ge hE).le h1.le)
  obtain ⟨g, hg⟩ := pow_eventually_lt γ (tax / (tax + E₀ * (1 - γ))) hγ0 hγ1 (div_pos htax hden)
  have hgeo : ∑ k ∈ Finset.range g, γ ^ k = (1 - γ ^ g) / (1 - γ) := by
    have hγ : γ ≠ 1 := by linarith
    rw [geom_sum_eq (x := γ) hγ]
    field_simp
    ring
  have hbound : energy γ ΔCE tax E₀ g ≤ γ ^ g * E₀ - tax * ((1 - γ ^ g) / (1 - γ)) := by
    have := energy_le_of_no_light γ ΔCE tax E₀ hγ0 hCE g
    rwa [hgeo] at this
  have hg' : γ ^ g * (tax + E₀ * (1 - γ)) < tax := (lt_div_iff₀ hden).1 hg
  have hnonneg : (0:ℝ) ≤ γ ^ g := pow_nonneg hγ0 g
  have hkey : γ ^ g * E₀ * (1 - γ) ≤ tax * (1 - γ ^ g) := by
    have := mul_lt_mul_of_pos_left hg' h1
    nlinarith
  exact ⟨g, hbound.trans (by
    rw [sub_nonpos, ← mul_div_assoc, le_div_iff₀ h1]
    exact hkey)⟩

/-! ### Отбор -/

/-- Вклад частицы: поглощённый свет минус налог. -/
noncomputable def particleGain (ΔCE tax : ℝ) : ℝ := ΔCE - tax

/-- Отбор не хуже: удаление частицы с отрицательным вкладом строго улучшает сумму. -/
theorem selection_dominates {N : ℕ} (g : Fin N → ℝ) {s : Finset (Fin N)} {i : Fin N}
    (hi : i ∈ s) (hg : g i < 0) :
    ∑ j ∈ s, g j < ∑ j ∈ s.erase i, g j :=
  Hagi.Growth.positive_selection_dominates g s i hi hg

/-- Дубликат в занятой нише (нулевой свет, положительный налог) имеет
отрицательный вклад и потому удаляется отбором. -/
theorem duplicate_pruned (tax : ℝ) (htax : 0 < tax) : particleGain 0 tax < 0 := by
  unfold particleGain; linarith

/-! ### Адмиссия органоида -/

/-- Гейт адмиссии: цена памяти и риска плюс зазор сертификации окупаются
LCB-приростом CE (`ΔCE ≥ 0` — снижение). -/
def organoidAdmission (lamM Δbytes lamR Δrisk ε ΔCE : ℝ) : Prop :=
  lamM * Δbytes + lamR * Δrisk + ε ≤ ΔCE

/-- Допущенный органоид улучшает трёхвалютную цель `J3 = L_pred + λ_M·C_state + λ_R·R_prot`
не менее чем на `ε`: `L_pred` падает на `ΔCE`, цена и риск входят с их весами. -/
theorem organoid_admission_improves (lamM Δbytes lamR Δrisk ε ΔCE L : ℝ)
    (h : organoidAdmission lamM Δbytes lamR Δrisk ε ΔCE) :
    Hagi.Step.J3 (L - ΔCE) (Δbytes) (Δrisk) lamM lamR ≤ Hagi.Step.J3 L 0 0 lamM lamR - ε := by
  unfold Hagi.Step.J3
  unfold organoidAdmission at h
  simp only [mul_zero, add_zero]
  linarith

end Hagi.Theory.ThermoFieldEcology

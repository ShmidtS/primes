/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Telescope

set_option linter.style.header false

/-!
# WarmupSchedule — почему растущий LR ускоряет сходимость

Формализация ядра Theorem 1 из «Theoretical Analysis on how
Learning Rate Warmup Accelerates Convergence»
(arXiv:2509.07972, Liu–Ge–Pan–Kang–Zhang):

- функция (ρ, K₀, K_ρ)-гладкая: ‖∇²f(w)‖ ≤ K₀ +
  K_ρ·(f(w)−f*)^ρ — локальная гладкость падает с
  субоптимальностью (Definition 1 статьи);
- адаптивный тёплый шаг η_t = c·min{1/K₀, Δ_t^{−ρ}/(3^ρ·K_ρ)}
  — РАСТУЩИЙ по мере убывания Δ;
- телескоп дескента: Δ_{t+1} ≤ Δ_t − (η_t/2)·‖∇f(w_t)‖²
  (Lemma-2-интеграция гессиана — здесь ИЗМЕРЯЕМАЯ посылка
  шага, h_emp_-контракт);
- итог: ∃ t < T: ‖∇f(w_t)‖²·(Ση) ≤ 2Δ₀.

Доказано:
* `warmup_eta_monotone`: убывание Δ ⟹ неубывание η_t
  (тёплый график РАСТЁТ — структурное следствие
  (ρ,K₀,K_ρ)-гладкости, ноль эмпирики);
* `warmup_telescope_bound`: телескоп дескента ⟹
  min-градиентная граница через Ση_t (прямой аргумент:
  минимум ≤ взвешенное среднее);
* `warmup_beats_constant`: при неубывающем η
  T·η₀ ≤ Ση_t — тёплая граница 2Δ₀/Ση не хуже
  постоянной 2Δ₀/(T·η₀); ускорение whenever K_ρ значим
  (локальная гладость реально зависит от субоптимальности).

Честная граница: дескент-посылка шага (интегральная форма
Lemma 2) не выводится здесь — (ρ,K₀,K_ρ)-гладкость —
h_emp_-гипотеза на ландшафт; доказаны арифметика графика,
монотонность и сравнение границ.
-/

open Finset

namespace Hagi.WarmupSchedule

/-- Тёплый (адаптивно растущий) learning rate: η_t =
c·min{1/K₀, Δ_t^{−ρ}/(3^ρ·K_ρ)}. -/
noncomputable def warmupEta (c K0 Krho rho : ℝ) (Δ : ℝ) : ℝ :=
  c * min (1 / K0) (Δ ^ (-rho) / (3 ^ rho * Krho))

/-- Структурная монотонность: при убывании субоптимальности
шаг η_t РАСТЁТ (ρ > 0, c ≥ 0, Δ' > 0) — тёплый график —
следствие (ρ,K₀,K_ρ)-гладкости, не отдельное предположение. -/
theorem warmup_eta_monotone (c K0 Krho rho Δ Δ' : ℝ)
    (hc : 0 ≤ c) (hle : Δ' ≤ Δ) (hΔ' : 0 < Δ')
    (hrho : 0 < rho) (hKr : 0 < Krho) :
    warmupEta c K0 Krho rho Δ
      ≤ warmupEta c K0 Krho rho Δ' := by
  have hΔ : 0 < Δ := lt_of_lt_of_le hΔ' hle
  have hden : (0:ℝ) < 3 ^ rho * Krho := by
    have h3 : (0:ℝ) < 3 ^ rho := by
      have : (3:ℝ) ^ rho = Real.rpow 3 rho := by
        rw [Real.rpow_eq_pow]
      rw [this]
      exact Real.rpow_pos_of_pos (by norm_num) rho
    exact mul_pos h3 hKr
  have h1 : Δ' ^ rho ≤ Δ ^ rho :=
    Real.rpow_le_rpow hΔ'.le hle hrho.le
  have hinv : (Δ ^ rho)⁻¹ ≤ (Δ' ^ rho)⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hΔ rho)
      (Real.rpow_pos_of_pos hΔ' rho)).mpr h1
  have hneg : Δ ^ (-rho) ≤ Δ' ^ (-rho) := by
    rw [Real.rpow_neg hΔ.le, Real.rpow_neg hΔ'.le]
    exact hinv
  have hnegdiv : Δ ^ (-rho) / (3 ^ rho * Krho)
      ≤ Δ' ^ (-rho) / (3 ^ rho * Krho) :=
    (div_le_div_iff_of_pos_right hden).mpr hneg
  unfold warmupEta
  exact mul_le_mul_of_nonneg_left
    (min_le_min (le_refl _) hnegdiv) hc

/-- Телескоп дескента ⟹ градиентная граница: если каждый шаг
удовлетворяет Δ_{t+1} ≤ Δ_t − (η_t/2)·g_t² с η_t ≥ 0 и
субоптимальности неотрицательны, то НАЙДЁТСЯ шаг с
g_t²·(Ση_t) ≤ 2Δ₀ (min-форма Theorem 1: минимум ≤
взвешенное среднее). -/
theorem warmup_telescope_bound (T : ℕ) (Δ g eta : ℕ → ℝ)
    (hT : 0 < T) (hΔpos : ∀ t, 0 ≤ Δ t)
    (heta : ∀ t, 0 ≤ eta t)
    (hstep : ∀ t < T, Δ (t + 1)
      ≤ Δ t - eta t / 2 * g t ^ 2) :
    ∃ t < T, g t ^ 2 * (∑ i ∈ Finset.range T, eta i)
      ≤ 2 * Δ 0 := by
  -- Δ не возрастает (вычитается неотрицательное)
  have hΔmono : ∀ n ≤ T, Δ n ≤ Δ 0 := by
    intro n
    induction n with
    | zero => intro _; exact le_refl (Δ 0)
    | succ m ih =>
      intro hm
      have hs := hstep m (by omega)
      have hg0 : 0 ≤ eta m / 2 * g m ^ 2 :=
        mul_nonneg (by linarith [heta m]) (sq_nonneg _)
      exact le_trans (by linarith) (ih (by omega))
  -- усиленный инвариант: Σ_{t<n} (η_t/2)g_t² ≤ Δ₀ − Δ_n
  have hstrong : ∀ n ≤ T,
      ∑ i ∈ Finset.range n, eta i / 2 * g i ^ 2
        ≤ Δ 0 - Δ n := by
    intro n hn
    induction n with
    | zero => simp
    | succ m ih =>
      have hstepm := hstep m (by omega)
      have hrec := ih (by omega)
      have hg0 : 0 ≤ eta m / 2 * g m ^ 2 :=
        mul_nonneg (by linarith [heta m]) (sq_nonneg _)
      rw [Finset.sum_range_succ]
      have : Δ m ≤ Δ 0 := hΔmono m (by omega)
      linarith [hstepm, hrec, hΔpos (m + 1)]
  -- минимум ≤ взвешенное среднее: argmin по диапазону
  obtain ⟨m, hmMin⟩ :=
    (Finset.range T).exists_min_image (fun t => g t ^ 2)
      ⟨0, Finset.mem_range.mpr hT⟩
  have hm : m < T := Finset.mem_range.mp hmMin.1
  refine ⟨m, hm, ?_⟩
  -- Σ η_t g_t² ≥ Σ η_t g_m² = g_m²·Ση
  have havg : g m ^ 2 * (∑ i ∈ Finset.range T, eta i)
      ≤ ∑ i ∈ Finset.range T, eta i * g i ^ 2 := by
    calc g m ^ 2 * (∑ i ∈ Finset.range T, eta i)
        = ∑ i ∈ Finset.range T, eta i * g m ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ ≤ ∑ i ∈ Finset.range T, eta i * g i ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hmMin.2 i hi)
              (heta i)
  -- Σ (η/2)g² ≤ Δ₀
  have hS : ∑ i ∈ Finset.range T, eta i / 2 * g i ^ 2
      ≤ Δ 0 := by
    have := hstrong T (le_refl _)
    have h2 : ∑ i ∈ Finset.range T, eta i / 2 * g i ^ 2
        = (∑ i ∈ Finset.range T, eta i * g i ^ 2) / 2 := by
      simp only [div_mul_eq_mul_div]
      rw [Finset.sum_div]
    have hΔT : 0 ≤ Δ T := hΔpos T
    rw [h2] at this
    linarith
  -- сведение: (Σ η g²)/2 ≤ Δ₀ и g_m²·Ση ≤ Ση g²
  have hsplit : ∑ i ∈ Finset.range T, eta i / 2 * g i ^ 2
      = (∑ i ∈ Finset.range T, eta i * g i ^ 2) / 2 := by
    simp only [div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [hsplit] at hS
  have := havg
  linarith

/-- Тёплая граница НЕ ХУЖЕ постоянной: при неубывающем η
каждый член суммы ≥ η₀, поэтому T·η₀ ≤ Ση_t. -/
theorem warmup_beats_constant (T : ℕ) (eta : ℕ → ℝ)
    (hmono : ∀ t < T, eta t ≤ eta (t + 1)) :
    (T : ℝ) * eta 0
      ≤ ∑ i ∈ Finset.range T, eta i := by
  have hge : ∀ i, i < T → eta 0 ≤ eta i := by
    intro i
    induction i with
    | zero => intro _; exact le_refl _
    | succ j ij =>
      intro _
      exact le_trans (ij (by omega)) (hmono j (by omega))
  calc (T : ℝ) * eta 0
      = ∑ _i ∈ Finset.range T, eta 0 := by
        simp
    _ ≤ ∑ i ∈ Finset.range T, eta i :=
        Finset.sum_le_sum fun i hi =>
          hge i (Finset.mem_range.mp hi)

end Hagi.WarmupSchedule

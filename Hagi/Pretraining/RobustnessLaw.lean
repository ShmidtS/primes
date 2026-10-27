import Mathlib

/-!
# RobustnessLaw — универсальный закон робастности (ядро)

Формализация дискретного ядра Universal Law of Robustness
(Bubeck–Li–Sellke, arXiv 2110.06401; обобщение Wu–Huang–Zhang,
arXiv 2202.11592): любой L-липшицев интерполятор данных
удовлетворяет АРХИТЕКТУРНО-НЕЗАВИСИМОЙ нижней границе
L ≥ максимальный уклон |Δy|/|Δx| между соседними точками.
Следствие: гладкая интерполяция «зашумлённых» данных требует
сверхпараметризации (p ≳ n/ε² в оригинале) — без неё
Lipschitz-константа обязана быть большой.
-/

namespace Hagi.Pretraining

/-- Основной закон: липшицевость интерполятора ограничена
снизу уклонами данных — независимо от числа параметров и
архитектуры. -/
theorem robust_interpolation_lipschitz_floor
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) (L : ℝ)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    ∀ i, i + 1 < n →
      |y (i + 1) - y i| ≤ L * |x (i + 1) - x i| := by
  intro i hi
  have h1 := hinter i (by omega)
  have h2 := hinter (i + 1) (by omega)
  have h := hlip (x i) (x (i + 1))
  rw [h1, h2, abs_sub_comm, abs_sub_comm (x i) (x (i + 1))] at h
  simpa using h

/-- РАЗРЫВ СГЛАЖИВАНИЯ: если соседние данные имеют уклон
slope > L·spacing, то НИКАКОЙ L-липшицев интерполятор не
существует — робастная интерполяция невозможна без
достаточной свободы модели (overparametrization). -/
theorem no_lipschitz_interpolator_of_steep
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L : ℝ)
    (hi : i + 1 < n)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hsteep : L * |x (i + 1) - x i|
      < |y (i + 1) - y i|) :
    False := by
  have h := robust_interpolation_lipschitz_floor f x y n L
    hinter hlip i hi
  exact absurd hsteep (by linarith [h])

/-- ПЛОТНАЯ ВЫБОРКА ОГРАНИЧИВАЕТ КОЛЕБАНИЯ: если f —
L-липшицев интерполятор и соседние точки разнесены не
более чем на δ, то уклоны данных ограничены L·δ. -/
theorem robust_spacing_bound
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) (L δ : ℝ)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hspace : ∀ i, i + 1 < n → |x (i + 1) - x i| ≤ δ) :
    ∀ i, i + 1 < n →
      |y (i + 1) - y i| ≤ L * δ := by
  intro i hi
  have h := robust_interpolation_lipschitz_floor f x y n L
    hinter hlip i hi
  have hs := hspace i hi
  calc |y (i + 1) - y i| ≤ L * |x (i + 1) - x i| := h
    _ ≤ L * δ := mul_le_mul_of_nonneg_left hs hL

/-- КОЛИЧЕСТВЕННАЯ ГРАНИЦА: шумные метки (размах ≥ σ между
соседями) при плотной выборке (шаг ≤ δ > 0) требуют
L ≥ σ/δ — количественное ядро Universal Law of Robustness. -/
theorem lipschitz_floor_of_noisy_labels
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L σ δ : ℝ)
    (hi : i + 1 < n) (hσ : 0 ≤ σ) (hδ : 0 < δ)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hnoise : σ ≤ |y (i + 1) - y i|)
    (hspace : |x (i + 1) - x i| ≤ δ) :
    σ / δ ≤ L := by
  have h := robust_interpolation_lipschitz_floor f x y n L
    hinter hlip i hi
  have habs : |x (i + 1) - x i| ≤ δ := hspace
  have hLnn : 0 ≤ L := by
    have h1 : |f 0 - f 1| ≤ L := by simpa using hlip 0 1
    have h2 : (0:ℝ) ≤ |f 0 - f 1| := abs_nonneg _
    linarith
  have hmono : L * |x (i + 1) - x i| ≤ L * δ :=
    mul_le_mul_of_nonneg_left habs hLnn
  have key : σ ≤ L * δ := by linarith
  exact (div_le_iff₀ hδ).mpr key

/-- МОСТ К ОБУЧЕНИЮ: шумная интерполяция требует
L ≥ σ/δ, а стабильность градиентного шага требует η·L ≤ 1 —
вместе они КАПИРУЮТ learning rate: η ≤ δ/σ. Робастность
данных напрямую ограничивает скорость обучения. -/
theorem noisy_interpolation_step_cap
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L σ δ η : ℝ)
    (hi : i + 1 < n) (hσ : 0 < σ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hnoise : σ ≤ |y (i + 1) - y i|)
    (hspace : |x (i + 1) - x i| ≤ δ)
    (hstab : η * L ≤ 1) :
    η ≤ δ / σ := by
  have hfloor : σ / δ ≤ L :=
    lipschitz_floor_of_noisy_labels f x y n i L σ δ hi
      (le_of_lt hσ) hδ hinter hlip hnoise hspace
  rw [le_div_iff₀ hσ]
  have hσL : σ ≤ L * δ := (div_le_iff₀ hδ).mp hfloor
  have hησ : η * σ ≤ η * (L * δ) :=
    mul_le_mul_of_nonneg_left hσL hη
  have : η * (L * δ) ≤ δ := by
    rw [← mul_assoc] at hησ ⊢
    calc η * L * δ ≤ 1 * δ := by
          exact mul_le_mul_of_nonneg_right hstab (le_of_lt hδ)
      _ = δ := by ring
  linarith [hησ]

/-- РОБАСТНОСТЬ ЗАМЕДЛЯЕТ ОБУЧЕНИЕ (количественно):
если (1) данные требуют L ≥ σ/δ (шумная интерполяция),
(2) стабильный шаг ограничен η·L ≤ 1, (3) шаг двигает
не далее η·G (градиентная граница G), то для смещения на
расстояние D нужно НЕ МЕНЕЕ D·σ/(δ·G) шагов. -/
theorem robust_slows_learning
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L σ δ η G D T : ℝ)
    (hi : i + 1 < n) (hσ : 0 < σ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hG : 0 < G) (hT : 0 ≤ T)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hnoise : σ ≤ |y (i + 1) - y i|)
    (hspace : |x (i + 1) - x i| ≤ δ)
    (hstab : η * L ≤ 1)
    (hprogress : D ≤ T * (η * G)) :
    D * σ / (δ * G) ≤ T := by
  have hcap : η ≤ δ / σ :=
    noisy_interpolation_step_cap f x y n i L σ δ η hi hσ hδ hη
      hinter hlip hnoise hspace hstab
  have hησ : η * σ ≤ δ := by
    have h2 : δ / σ * σ = δ := div_mul_cancel₀ δ (ne_of_gt hσ)
    calc η * σ ≤ (δ / σ) * σ :=
          mul_le_mul_of_nonneg_right hcap (le_of_lt hσ)
      _ = δ := h2
  -- D ≤ T·η·G и η·σ ≤ δ ⟹ T ≥ D·σ/(δ·G)
  have key : D * σ ≤ T * (δ * G) := by
    calc D * σ ≤ (T * (η * G)) * σ := by
          exact mul_le_mul_of_nonneg_right hprogress (le_of_lt hσ)
      _ = T * ((η * σ) * G) := by ring
      _ ≤ T * (δ * G) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hησ (le_of_lt hG)) hT
  exact (div_le_iff₀ (mul_pos hδ hG)).mpr key

/-- БЮДЖЕТНАЯ ГРАНИЦА РОБАСТНОСТИ: обучение на шумных
данных требует T ≥ D·σ/(δ·G) шагов по c единиц бюджета —
итоговая нижняя граница B ≥ c·D·σ/(δ·G). Мост к
бюджетному капстоуну HAGI (budget_capability_ceiling). -/
theorem robust_budget_floor
    (f : ℝ → ℝ) (x y : ℕ → ℝ) (n i : ℕ) (L σ δ η G D T c B : ℝ)
    (hi : i + 1 < n) (hσ : 0 < σ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hG : 0 < G) (hc : 0 ≤ c) (hT0 : 0 ≤ T)
    (hinter : ∀ i < n, f (x i) = y i)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hnoise : σ ≤ |y (i + 1) - y i|)
    (hspace : |x (i + 1) - x i| ≤ δ)
    (hstab : η * L ≤ 1)
    (hprogress : D ≤ T * (η * G))
    (hbudget : T * c ≤ B) :
    c * (D * σ / (δ * G)) ≤ B := by
  have hT : D * σ / (δ * G) ≤ T :=
    robust_slows_learning f x y n i L σ δ η G D T hi hσ hδ hη
      hG hT0 hinter hlip hnoise hspace hstab hprogress
  calc c * (D * σ / (δ * G)) ≤ c * T :=
        mul_le_mul_of_nonneg_left hT hc
    _ = T * c := by ring
    _ ≤ B := hbudget

end Hagi.Pretraining

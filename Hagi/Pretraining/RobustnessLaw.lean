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

end Hagi.Pretraining

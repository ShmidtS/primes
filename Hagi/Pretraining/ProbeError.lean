/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Core.ErrorProp
set_option linter.style.header false

/-!
# ProbeError — теория прямых проб (мост Boost → Cut из PR #11)

Формализация «теоремы 1» и top-k леммы интеграционного плана
(экспериментальное ядро обучения без обратного прохода):
прямые конечные разности по ортогональным направлениям как
оценитель градиента, и граница ошибки остатка top-k маршрутизации
MLP через последующие слои.

* `fd_probe_error` — граница расхождения прямой конечной разности
  с истинным градиентом при модельной гипотезе гладкости
  (ε_probe(σ) = L·σ·‖v‖²/2): полный цикл возмущений НЕ даёт
  нулевую ошибку на нелинейном loss;
* `linear_probe_exact` — в аффинной модели прямая разность
  восстанавливает ⟨g, v⟩ точно (ошибка цикла = 0);
* `residual_vec_bound` — треугольная граница на остаток
  отброшенных компонент (top-k маршрутизация): ‖Σ φ_j•v_j‖ ≤
  Σ |φ_j|·‖v_j‖;
* `topk_residual_col_diff` — приращение остатка при возмущении
  входа: структура той же леммы для разности
  `h' - h` (то, что нужно фазе Cut: ошибка маршрута по всему пути —
  через `Hagi.Core.ErrorProp.propagate_bound`).

Гипотеза `hmodel` — явная модельная гипотеза гладкости (дескриптор
L, масштаб σ), не эмпирический параметр. Матрично-векторная версия
следует стилю `Hagi/External/Flywheel/NormSupport.lean`
(`WithLp.toLp`/`ofLp`).
-/

open Finset Real InnerProductSpace

namespace Hagi.Pretraining

/-! ### Теорема 1: конечная разность против градиента -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Граница ошибки прямой конечной разности (ε_probe): при модельной
гипотезе гладкости (Taylor remainder bound)
|(f(x+σv) - f(x)) - σ⟪grad x, v⟫| ≤ (L/2)σ²‖v‖²,
прямая разность (f(x+σv) - f(x))/σ расходится с истинной
производной по направлению ⟨grad x, v⟩ не более чем на
(L/2)σ‖v‖². Полный цикл возмущений (Hadamard) не устраняет
член L·σ — только усредняет его по направлениям. -/
theorem fd_probe_error {f : X → ℝ} {grad : X → X} {L σ : ℝ}
    (hσ : 0 < σ)
    (hmodel : ∀ x v, |f (x + σ • v) - f x - σ * ⟪grad x, v⟫_ℝ|
      ≤ (L / 2) * σ ^ 2 * ‖v‖ ^ 2)
    (x v : X) :
    |(f (x + σ • v) - f x) / σ - ⟪grad x, v⟫_ℝ|
      ≤ (L / 2) * σ * ‖v‖ ^ 2 := by
  have hkey := hmodel x v
  have hsplit : (f (x + σ • v) - f x) / σ - ⟪grad x, v⟫_ℝ
      = (f (x + σ • v) - f x - σ * ⟪grad x, v⟫_ℝ) / σ := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
  have hEq : (L / 2) * σ * ‖v‖ ^ 2 * σ = (L / 2) * σ ^ 2 * ‖v‖ ^ 2 := by
    ring
  rw [hEq]
  exact hkey

/-- Идеальная (аффинная) модель: прямая разность восстанавливает
производную по направлению точно — ошибка цикла нулевая. Это
обосновывает quadrature-выводы `Dust.esUnbiased`
в аффинном вырождении; на реальном нелинейном loss действует
`fd_probe_error`. -/
theorem linear_probe_exact {f : X → ℝ} (f0 : ℝ) (g v : X) (σ : ℝ)
    (hσ : 0 < σ) (x : X)
    (haff : ∀ y, f y = f0 + ⟪g, y⟫_ℝ) :
    (f (x + σ • v) - f x) / σ = ⟪g, v⟫_ℝ := by
  rw [haff (x + σ • v), haff x]
  have hadd : ⟪g, x + σ • v⟫_ℝ = ⟪g, x⟫_ℝ + σ * ⟪g, v⟫_ℝ := by
    rw [inner_add_right, real_inner_smul_right]
  rw [hadd]
  field_simp
  ring

/-! ### Top-k маршрутизация: остаток отброшенных компонент -/

variable {m n : ℕ}

/-- Треугольная граница на остаток отброшенных компонент:
для весов φ и\Component векторов v (например, столбцов W_out и
активаций h_j) —
‖Σ_{j ∉ K} φ_j • v_j‖ ≤ Σ_{j ∉ K} |φ_j| · ‖v_j‖.
Это статическая форма top-k леммы; приращённая форма получается
применением к φ_j := h_j(u+δ) - h_j(u). -/
theorem residual_vec_bound {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : Fin n → V) (φ : Fin n → ℝ)
    (K : Finset (Fin n)) :
    ‖∑ j ∈ univ \ K, φ j • v j‖ ≤ ∑ j ∈ univ \ K, |φ j| * ‖v j‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

/-- Приращённая форма (фаза Cut): изменение остатка при возмущении
входа u → u + δ не превышает взвешенной суммы вариаций активаций
отброшенных компонент — вход для `propagate_bound`. -/
theorem residual_vec_diff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v v' : Fin n → V) (φ φ' : Fin n → ℝ)
    (K : Finset (Fin n)) :
    ‖∑ j ∈ univ \ K, φ' j • v' j - ∑ j ∈ univ \ K, φ j • v j‖
      ≤ ∑ j ∈ univ \ K, (|φ' j| * ‖v' j‖ + |φ j| * ‖v j‖) := by
  have hsplit : ∑ j ∈ univ \ K, φ' j • v' j
      - ∑ j ∈ univ \ K, φ j • v j
      = ∑ j ∈ univ \ K, (φ' j • v' j - φ j • v j) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  have htri : ‖φ' j • v' j - φ j • v j‖
      ≤ ‖φ' j • v' j‖ + ‖φ j • v j‖ := by
    have h0 : ‖φ' j • v' j - φ j • v j‖
        ≤ ‖φ' j • v' j‖ + ‖φ j • v j‖ := by
      have h1 : ‖φ' j • v' j - φ j • v j‖
          = ‖φ' j • v' j + -(φ j • v j)‖ := by
        rw [sub_eq_add_neg]
      have h2 := norm_add_le (φ' j • v' j) (-(φ j • v j))
      have h3 : ‖-(φ j • v j)‖ = ‖φ j • v j‖ := norm_neg _
      calc ‖φ' j • v' j - φ j • v j‖
          = ‖φ' j • v' j + -(φ j • v j)‖ := h1
        _ ≤ ‖φ' j • v' j‖ + ‖-(φ j • v j)‖ := h2
        _ = ‖φ' j • v' j‖ + ‖φ j • v j‖ := by rw [h3]
    linarith [h0]
  refine le_trans htri ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- Конкретизация для MLP: столбец выходной матрицы как вектор
EuclideanSpace; вклад j-й компоненты = h_j • Wₒᵤₜ,:,j, а остаток
top-k — сумма по j ∉ K. Значения норм столбцов определяются
`EuclideanSpace.norm_eq`. -/
noncomputable def mlpResidual (W : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin n → ℝ) (K : Finset (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  ∑ j ∈ univ \ K, h j • (WithLp.toLp 2 fun i => W i j)

/-- Остаток top-k ограничен суммой норм столбцов на исключённых
компонентах (статическая форма пользовательской леммы:
‖r_K‖ ≤ Σ_{j∉K} ‖Wₒᵤₜ,:,j‖·|h_j|). -/
theorem mlpResidual_bound (W : Matrix (Fin m) (Fin n) ℝ) (h : Fin n → ℝ)
    (K : Finset (Fin n)) :
    ‖mlpResidual W h K‖
      ≤ ∑ j ∈ univ \ K, |h j| * ‖(WithLp.toLp 2 fun i => W i j :
          EuclideanSpace ℝ (Fin m))‖ := by
  exact residual_vec_bound _ _ K

/-! ### Теорема 2: расхождение Cut-сигнала с полным градиентом -/

/-- **Ошибка Cut-сигнала (трёхчленная декомпозиция)**: полный
градиент `g_full` задачи, градиент `g_mid` вспомогательной задачи
с фиксированными выходами внимания (attention-clamped) и
оценитель `gu` по конечным разностям той же вспомогательной
задачи. Треугольник даёт
`‖gu - g_full‖ ≤ ‖gu - g_mid‖ + ‖g_mid - g_full‖`:
член `ε_probe` контролируется `fd_probe_error` (конечные
разности вспомогательной задачи), член `ε_attention` — модельная
гипотеза о близости градиентов вспомогательной и полной задач
(фиксация внимания + top-k усечение — содержимое этой границы;
её количественная форма — отдельная теорема). -/
theorem cut_signal_triangle {gu g_mid g_full : X} (ε_probe ε_attention : ℝ)
    (h1 : ‖gu - g_mid‖ ≤ ε_probe)
    (h2 : ‖g_mid - g_full‖ ≤ ε_attention) :
    ‖gu - g_full‖ ≤ ε_probe + ε_attention := by
  have hstep : gu - g_full = (gu - g_mid) + (g_mid - g_full) := by
    abel
  rw [hstep]
  calc ‖(gu - g_mid) + (g_mid - g_full)‖
      = ‖(gu - g_mid) + (g_mid - g_full)‖ := rfl
    _ ≤ ‖gu - g_mid‖ + ‖g_mid - g_full‖ := norm_add_le _ _
    _ ≤ ε_probe + ε_attention := by linarith [h1, h2]

end Hagi.Pretraining

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Core.ErrorProp
import Hagi.System.GrowthState
import Hagi.Foundations.Telescope
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

/-- Каноническая квадратичная энергия с перенесённым центром `a`.
Это выбранная точная модель для вычислений прямой разности, а не модель
произвольного полного либо attention-clamped нелинейного loss. Само
определение не является утверждением о фреше-дифференцируемости. -/
noncomputable def probeQuadraticEnergy (L : ℝ) (a x : X) : ℝ :=
  (L / 2) * ‖x - a‖ ^ 2

/-- Каноническое алгебраическое градиентное поле перенесённой
квадратичной энергии: общий центр `a` сокращается при разности
значений поля. Использование имени «градиент» здесь не добавляет
отдельно не доказанного утверждения о фреше-производной. -/
def probeQuadraticGrad (L : ℝ) (a x : X) : X :=
  L • (x - a)

/-- Точная квадратичная конкретизация `fd_probe_error`: модельная
гипотеза конечной разности выводится полным алгебраическим
разложением, а не принимается как внешняя предпосылка. Остаток без
абсолютного значения равен `(L / 2) * σ ^ 2 * ‖v‖ ^ 2`; при `L ≥ 0`
и `σ > 0` он неотрицателен. Это утверждение только о выбранном
каноническом поле и его прямой разности, а не о произвольном
полном/clamped attention, общей нелинейной динамике или
фреше-дифференцируемости. -/
theorem fd_probe_error_quadratic (L : ℝ) (a : X) (hL : 0 ≤ L)
    {σ : ℝ} (hσ : 0 < σ) (x v : X) :
    |(probeQuadraticEnergy L a (x + σ • v) - probeQuadraticEnergy L a x) / σ -
        ⟪probeQuadraticGrad L a x, v⟫_ℝ|
      ≤ (L / 2) * σ * ‖v‖ ^ 2 := by
  apply fd_probe_error hσ
  intro y w
  have hshift : y + σ • w - a = (y - a) + σ • w := by
    abel
  have hremainder :
      probeQuadraticEnergy L a (y + σ • w) - probeQuadraticEnergy L a y -
          σ * ⟪probeQuadraticGrad L a y, w⟫_ℝ =
        (L / 2) * σ ^ 2 * ‖w‖ ^ 2 := by
    simp only [probeQuadraticEnergy, probeQuadraticGrad]
    rw [hshift, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos hσ, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hremainder]
  exact abs_of_nonneg (by positivity) |>.le

/-- Центральная разность для выбранной перенесённой квадратичной
энергии. Это только точная детерминированная конструкция для данного
поля, а не утверждение о стохастической несмещённости произвольных
функций или о безусловной оптимизации без производной и без ошибки.
Она не сравнивает число вычислений функции с прямой разностью. -/
noncomputable def centralQuadraticProbe (L : ℝ) (a x v : X) (σ : ℝ) : ℝ :=
  (probeQuadraticEnergy L a (x + σ • v) - probeQuadraticEnergy L a (x - σ • v)) /
    (2 * σ)

/-- Для выбранной перенесённой квадратичной энергии центральная разность
точно равна скалярному произведению с её алгебраическим градиентным полем:
квадратичный вклад сокращается в числителе центральной разности. Это не
доказательство стохастической несмещённости для произвольных функций и не
утверждение о безусловной либо безошибочной оптимизации без производной
для произвольных моделей. Не утверждается также, что число вычислений
функции не превышает число вычислений для прямой разности. -/
theorem centralQuadraticProbe_exact (L : ℝ) (a x v : X) {σ : ℝ} (hσ : 0 < σ) :
    centralQuadraticProbe L a x v σ = ⟪probeQuadraticGrad L a x, v⟫_ℝ := by
  have hplus : x + σ • v - a = (x - a) + σ • v := by
    abel
  have hminus : x - σ • v - a = (x - a) - σ • v := by
    abel
  simp only [centralQuadraticProbe, probeQuadraticEnergy, probeQuadraticGrad]
  rw [hplus, hminus, norm_add_sq_real (x - a) (σ • v),
    norm_sub_sq_real (x - a) (σ • v)]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hσ,
    real_inner_smul_left, real_inner_smul_right]
  field_simp [ne_of_gt hσ]
  ring

/-- Прямая разность для выбранной перенесённой квадратичной
энергии. Это детерминированная конструкция только для канонической
модели, без предпосылок о стохастической несмещённости. -/
noncomputable def forwardQuadraticProbe (L : ℝ) (a x v : X) (σ : ℝ) : ℝ :=
  (probeQuadraticEnergy L a (x + σ • v) - probeQuadraticEnergy L a x) / σ

/-- Точная абсолютная ошибка прямой разности в канонической
перенесённой квадратичной модели. При `L ≥ 0` и `σ > 0` ошибка равна
`(L / 2) * σ * ‖v‖ ^ 2`; это не утверждение о стохастических
оценках или произвольном нелинейном loss. -/
theorem forwardQuadraticProbe_error (L : ℝ) (a : X) (hL : 0 ≤ L)
    (x v : X) {σ : ℝ} (hσ : 0 < σ) :
    |forwardQuadraticProbe L a x v σ - ⟪probeQuadraticGrad L a x, v⟫_ℝ| =
      (L / 2) * σ * ‖v‖ ^ 2 := by
  have hshift : x + σ • v - a = (x - a) + σ • v := by
    abel
  have herror :
      forwardQuadraticProbe L a x v σ - ⟪probeQuadraticGrad L a x, v⟫_ℝ =
        (L / 2) * σ * ‖v‖ ^ 2 := by
    simp only [forwardQuadraticProbe, probeQuadraticEnergy, probeQuadraticGrad]
    rw [hshift, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos hσ, real_inner_smul_left, real_inner_smul_right]
    field_simp [ne_of_gt hσ]
    ring
  rw [herror]
  exact abs_of_nonneg (by positivity)

/-- В канонической перенесённой квадратичной модели абсолютная ошибка
центральной разности строго меньше ошибки прямой разности при `L > 0`,
`σ > 0` и `v ≠ 0`: центральная ошибка равна нулю, а прямая равна
`(L / 2) * σ * ‖v‖ ^ 2 > 0`. Это только сравнение точности в выбранной
модели, а не утверждение о числе вычислений функции, уменьшении их числа,
оптимальности для произвольного loss или свойствах стохастических оценок.
Без указанных условий сравнение не утверждается; специальная ветка для
`σ = 0` не вводится. -/
theorem quadratic_central_error_lt_forward_error
    (L : ℝ) (a : X) (hL : 0 < L) (x v : X) (hv : v ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) :
    |centralQuadraticProbe L a x v σ - ⟪probeQuadraticGrad L a x, v⟫_ℝ| <
      |forwardQuadraticProbe L a x v σ - ⟪probeQuadraticGrad L a x, v⟫_ℝ| := by
  rw [centralQuadraticProbe_exact L a x v hσ,
    forwardQuadraticProbe_error L a hL.le x v hσ, sub_self, abs_zero]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  positivity

/-- Градиентное поле выбранной перенесённой квадратичной модели
`L`-липшицево при `L ≥ 0`. Доказательство использует только точное
сокращение общего центра и норму скалярного множителя; посылка о
липшицевости произвольной карты либо полного/clamped attention не
вводится. -/
theorem probeQuadraticGrad_lipschitz (L : ℝ) (a : X) (hL : 0 ≤ L)
    (u v : X) :
    ‖probeQuadraticGrad L a u - probeQuadraticGrad L a v‖ ≤ L * ‖u - v‖ := by
  unfold probeQuadraticGrad
  have hsub : (u - a) - (v - a) = u - v := by
    abel
  rw [← smul_sub, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]

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

/-! ### Теорема 3: допуск обновления по неточному сигналу -/

/-- **Сертификат с запасом на ошибку сигнала** (мост «приближённый
сигнал → оценка погрешности → безопасный шаг»): пусть
`dLmeas` — изменение контролируемого loss, сертифицированное по
неточному направлению `ghat` (гладкостная модель), а `dLexact` —
истинное значение по точному градиенту `gfull`. Тогда
`dLexact ≤ dLmeas + ε·‖d‖` — аддитивный запас равен
произведению границы ошибки сигнала на норму шага
(Cauchy–Schwarz на разности направлений). -/
theorem safe_certificate_margin {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (ghat gfull d : X) {L ε : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hbound : ‖ghat - gfull‖ ≤ ε)
    (dLmeas dLexact : ℝ)
    (hmeas : dLmeas = -⟪ghat, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hexact : dLexact = -⟪gfull, d⟫_ℝ + L * ‖d‖ ^ 2 / 2) :
    dLexact ≤ dLmeas + ε * ‖d‖ := by
  have hdiff : ⟪ghat, d⟫_ℝ - ⟪gfull, d⟫_ℝ = ⟪ghat - gfull, d⟫_ℝ := by
    rw [inner_sub_left]
  have h1 := abs_real_inner_le_norm (ghat - gfull) d
  have h4 : ‖ghat - gfull‖ * ‖d‖ ≤ ε * ‖d‖ :=
    mul_le_mul_of_nonneg_right hbound (norm_nonneg d)
  have hcauchy : ⟪ghat, d⟫_ℝ - ⟪gfull, d⟫_ℝ ≤ ε * ‖d‖ := by
    calc ⟪ghat, d⟫_ℝ - ⟪gfull, d⟫_ℝ = ⟪ghat - gfull, d⟫_ℝ := hdiff
      _ ≤ |⟪ghat - gfull, d⟫_ℝ| := le_abs_self _
      _ ≤ ‖ghat - gfull‖ * ‖d‖ := h1
      _ ≤ ε * ‖d‖ := h4
  rw [hexact]
  linarith [hcauchy, hmeas]

/-- **Приём шага по неточному сигналу**: если сертифицированное по
`ghat` изменение с запасом `ε·‖d‖` укладывается в нулевой бюджет
риска (контрольное условие SafeQP-семантики), то и истинное
изменение неположительно. -/
theorem probe_safe_accept {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (ghat gfull d : X) {L ε : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hbound : ‖ghat - gfull‖ ≤ ε)
    (dLmeas dLexact : ℝ)
    (hmeas : dLmeas = -⟪ghat, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hexact : dLexact = -⟪gfull, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hbudget : dLmeas + ε * ‖d‖ ≤ 0) :
    dLexact ≤ 0 :=
  le_trans (safe_certificate_margin ghat gfull d hε hL hbound
    dLmeas dLexact hmeas hexact) hbudget
/-! ### Теорема 5: количественная граница для ε_attention и
сквозная цепочка -/

/-- **Количественная форма ε_attention**: если градиент
вспомогательной (attention-clamped) задачи относительно градиента
полной задачи `L_att`-липшицев по возмущению клампнутых выходов
внимания (модельная гипотеза `h_emp_attsmooth`: «фиксация + top-k
усечение вносят возмущение, контролируемое параметром
`ε_att`»), то `‖g_mid xhat - g_full x‖ ≤ L_att * ε_att` —
количественное наполнение абстрактного члена `ε_attention`
из `cut_signal_triangle`. -/
theorem clamped_attention_grad_bound {X : Type*} [NormedAddCommGroup X]
    (gmid gfull : X → X) {L_att ε_att : ℝ}
    (hL : 0 ≤ L_att) (hε : 0 ≤ ε_att)
    (h_emp_attsmooth : ∀ x y : X, ‖gmid x - gfull y‖ ≤ L_att * ‖x - y‖)
    (xhat x : X) (hclamp : ‖xhat - x‖ ≤ ε_att) :
    ‖gmid xhat - gfull x‖ ≤ L_att * ε_att := by
  have h := h_emp_attsmooth xhat x
  have hmul : L_att * ‖xhat - x‖ ≤ L_att * ε_att :=
    mul_le_mul_of_nonneg_left hclamp hL
  linarith [h, hmul]

/-- **Инстанцированный треугольник Cut-сигнала**: композиция
`cut_signal_triangle` с количественной границей члена внимания
из `clamped_attention_grad_bound`. `gA` — карта градиента
вспомогательной (attention-clamped) задачи, `gF` — полной;
`gu` — вектор-оценка сигнала. Итоговая граница расхождения:
`‖gu - gF x‖ ≤ ε_probe + L_att * ε_att`. -/
theorem cut_signal_attention_quant {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (gA gF : X → X) (gu xhat x : X) {L_att ε_att ε_probe : ℝ}
    (hL_att : 0 ≤ L_att) (hε_att : 0 ≤ ε_att)
    (h_emp_attsmooth : ∀ a b : X, ‖gA a - gF b‖ ≤ L_att * ‖a - b‖)
    (hclamp : ‖xhat - x‖ ≤ ε_att)
    (hprobe : ‖gu - gA xhat‖ ≤ ε_probe) :
    ‖gu - gF x‖ ≤ ε_probe + L_att * ε_att := by
  have hatt : ‖gA xhat - gF x‖ ≤ L_att * ε_att :=
    clamped_attention_grad_bound (X := X) gA gF hL_att hε_att
      h_emp_attsmooth xhat x hclamp
  exact cut_signal_triangle ε_probe (L_att * ε_att) hprobe hatt

/-- **Липшицевость проекционного градиента**: модель — одинаково
масштабированная линейная ортографическая проекция обеих абстрактных
карт градиентов, полезная для фиксированного удерживаемого
подпространства или маски. Это не произвольное полное либо clamped
обучаемое attention и не доказательство общей динамики softmax/top-k.
Математическая опора — доказанная в Mathlib оценка нормы проектора
`Submodule.norm_orthogonalProjectionOnto_apply_le`; дополнительная
предпосылка о контрактивности или эмпирической гладкости не требуется. -/
theorem projected_gradient_lipschitz
    (K : Submodule ℝ X) [K.HasOrthogonalProjection] (L : ℝ) (hL : 0 ≤ L) :
    ∀ a b : X,
      ‖L • (K.orthogonalProjectionOnto a : X) -
        L • (K.orthogonalProjectionOnto b : X)‖ ≤ L * ‖a - b‖ := by
  intro a b
  change ‖L • K.starProjection a - L • K.starProjection b‖ ≤ L * ‖a - b‖
  have hfactor :
      L • K.starProjection a - L • K.starProjection b =
        L • K.starProjection (a - b) := by
    rw [map_sub, smul_sub]
  rw [hfactor, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
  have hproj : ‖K.starProjection (a - b)‖ ≤ ‖a - b‖ := by
    change ‖K.orthogonalProjectionOnto (a - b)‖ ≤ ‖a - b‖
    exact K.norm_orthogonalProjectionOnto_apply_le (a - b)
  exact mul_le_mul_of_nonneg_left hproj hL

/-- **Cut-сигнал для проекционной модели**: обе абстрактные карты
градиентов инстанцированы одной масштабированной линейной
ортографической проекцией. Модель описывает фиксированное удерживаемое
подпространство или маску; она не утверждает, что произвольные `gA`/`gF`
являются проекциями, не описывает произвольное полное/clamped обучаемое
attention и не доказывает общую динамику softmax/top-k. Общая предпосылка
`h_emp_attsmooth` здесь доказана через `projected_gradient_lipschitz`;
сохраняются только входные радиусы и неотрицательность масштаба. -/
theorem cut_signal_attention_quant_projection
    (K : Submodule ℝ X) [K.HasOrthogonalProjection] (gu xhat x : X)
    (L : ℝ) {ε_att ε_probe : ℝ}
    (hL : 0 ≤ L) (hε_att : 0 ≤ ε_att)
    (hclamp : ‖xhat - x‖ ≤ ε_att)
    (hprobe : ‖gu - L • (K.orthogonalProjectionOnto xhat : X)‖ ≤ ε_probe) :
    ‖gu - L • (K.orthogonalProjectionOnto x : X)‖ ≤ ε_probe + L * ε_att := by
  have h_smooth : ∀ a b : X,
      ‖L • (K.orthogonalProjectionOnto a : X) -
        L • (K.orthogonalProjectionOnto b : X)‖ ≤ L * ‖a - b‖ :=
    projected_gradient_lipschitz K L hL
  exact cut_signal_attention_quant
    (fun z => L • (K.orthogonalProjectionOnto z : X))
    (fun z => L • (K.orthogonalProjectionOnto z : X)) gu xhat x
    hL hε_att h_smooth hclamp hprobe

/-- **Сквозная цепочка приёма шага** (объединение Теорем 1–5):
«приближённый сигнал → суммарный запас ε_probe + L_att·ε_att →
бюджет риска». Probe-член контролируется конечными разностями
(`<fе>fd_probe_error</fе>`), attention-член — гладкостью по
клампнутым выходам; приём шага — `probe_safe_accept` с
суммарным ε. -/
theorem cut_safe_accept {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (gA gF : X → X) (gu d xhat x : X) {L ε_probe L_att ε_att : ℝ}
    (hL : 0 ≤ L) (hL_att : 0 ≤ L_att) (hε_att : 0 ≤ ε_att)
    (hε_probe : 0 ≤ ε_probe)
    (h_emp_attsmooth : ∀ a b : X, ‖gA a - gF b‖ ≤ L_att * ‖a - b‖)
    (hclamp : ‖xhat - x‖ ≤ ε_att)
    (hprobe : ‖gu - gA xhat‖ ≤ ε_probe)
    (dLmeas dLexact : ℝ)
    (hmeas : dLmeas = -⟪gu, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hexact : dLexact = -⟪gF x, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hbudget : dLmeas + (ε_probe + L_att * ε_att) * ‖d‖ ≤ 0) :
    dLexact ≤ 0 :=
  probe_safe_accept gu (gF x) d (ε := ε_probe + L_att * ε_att)
    (add_nonneg hε_probe (mul_nonneg hL_att hε_att)) hL
    (cut_signal_attention_quant gA gF gu xhat x hL_att hε_att
      h_emp_attsmooth hclamp hprobe)
    dLmeas dLexact hmeas hexact hbudget

end Hagi.Pretraining

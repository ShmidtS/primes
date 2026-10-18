/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Core.ErrorProp
import Hagi.System.GrowthState
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
/-! ### Теорема 4: от безопасного шага к измеримому приросту -/

/-- **Накопление измеримого выигрыша** (лимитная цепочка):
если на каждом шаге горизонта `k` принятый безопасный шаг дают
истинный спад `E (t+1) ≤ E t − gain` с одной и той же
измеримой величиной `gain > 0` (факт-лосс как ledger-энергия,
план §7), а энергия ограничена снизу `Emin`, то весь горизонт
ограничен бюджетом: `(k:ℝ) ≤ (E 0 − Emin)/gain`.
Делегирует базовому лиапуновскому закону
`Hagi.System.macro_termination_derived` (объединение с
Foundation-машиной: теорема не требует признака «назначенного
growGain» — спад измеряется фактически). -/
theorem measured_gain_horizon {E : ℕ → ℝ} (Emin gain : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hgen : ∀ t < k, E (t + 1) ≤ E t - gain)
    (hgain : 0 < gain) :
    (k : ℝ) ≤ (E 0 - Emin) / gain :=
  Hagi.System.macro_termination_derived Emin gain k hE hgen hgain

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

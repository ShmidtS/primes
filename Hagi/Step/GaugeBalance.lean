/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# GaugeBalance — некомпактные симметрии масштабирования и баланс норм

arXiv:2611.27889v1 (Portilheiro, Liebana, Orbanz, Saxe): при малой регуляризации
равновесие уходит вдоль gauge-орбиты на бесконечность, раздувая диапазон весов;
баланс норм (Sec. 5) выбирает представителя орбиты с минимальной суммой
квадратов норм. В HAGI это каждый ранг-1 фактор (LowRankAdapter, BigramSkip,
MLA, SwiGLU-пары); блоки роста стартуют в мёртвом множестве `W_down = 0`.

Три группы утверждений: инвариантность и баланс (`rank1_gauge`, `balance_key`,
`stock_balance_min/_attained`, `rank1_ntk_gauge_invariant`); мёртвое множество
(`dead_block_out_zero`, `dead_loss_const`, `pairGrad_u_*`, `asym_step_*`,
`dead_one_input_fraction`, `sign_assignments_card`); насыщение клипа при
фиксированной шкале (`clip_sat_tail`, `gauge_kills_sat_tail`). Границы
применимости — в докстрингах теорем; измерения на HAGI_v2 — PROPOSAL 25/27.
-/

namespace Hagi.Step.GaugeBalance
open Matrix
variable {m n h d : ℕ}

/-- Некомпактная масштабная симметрия ранг-`1` фактора (`LowRankAdapter B·A`,
`BigramSkip B_u·B_v`, `MLA`): `(c • B) * (c⁻¹ • A) = B * A` — калибровка не
меняет функцию. -/
theorem rank1_gauge (B : Matrix (Fin m) (Fin 1) ℝ) (A : Matrix (Fin 1) (Fin n) ℝ)
    (c : ℝ) (hc : c ≠ 0) : (c • B) * (c⁻¹ • A) = B * A := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul]
  rw [show c * B i 0 * (c⁻¹ * A 0 j) = (c * c⁻¹) * (B i 0 * A 0 j) by ring, mul_inv_cancel₀ hc, one_mul]
/-- Локальная лемма баланса в координатах `A, B ≥ 0`. -/
theorem balance_key (A B c : ℝ) (hc : 0 < c) :
    (c * A) ^ 2 + (B / c) ^ 2 ≥ 2 * A * B := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have key : (c * A) ^ 2 + (B / c) ^ 2 - 2 * A * B = (c * A - B / c) ^ 2 := by
    field_simp [hcne]; ring
  have h := sq_nonneg (c * A - B / c)
  have h' : (c * A - B / c) ^ 2 ≥ 0 := h
  rw [← key] at h'
  linarith
/-- Stock-balance (Sec. 5 arXiv:2611.27889): среди калибровок `(c·a, b/c)` сумма
квадратов норм минимальна при `c² = |b/a|`; минимум равен `2|a b|`. -/
theorem stock_balance_min (a b c : ℝ) (hc : 0 < c) :
    (c * a) ^ 2 + (b / c) ^ 2 ≥ 2 * |a * b| := by
  have h := balance_key |a| |b| c hc
  have ha2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have hca' : (c * a) ^ 2 = c ^ 2 * a ^ 2 := by ring
  rw [hca', ← ha2, div_pow, ← hb2, abs_mul,
    show c ^ 2 * |a| ^ 2 = (c * |a|) ^ 2 by ring, ← div_pow]
  simpa [mul_assoc] using h
/-- Точка баланса `c = sqrt(|b|/|a|)` достигает минимума `2|a b|` (при `a, b ≠ 0`). -/
theorem stock_balance_attained (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Real.sqrt (|b| / |a|) * a) ^ 2 + (b / Real.sqrt (|b| / |a|)) ^ 2 = 2 * |a * b| := by
  set c := Real.sqrt (|b| / |a|) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 (div_pos (abs_pos.2 hb) (abs_pos.2 ha))
  have hsq : c ^ 2 = |b| / |a| := Real.sq_sqrt (div_nonneg (abs_nonneg b) (abs_nonneg a))
  have hsq' : c ^ 2 * |a| = |b| := by rw [hsq]; field_simp [abs_ne_zero.2 ha]
  have ha2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have h1 : (c * a) ^ 2 = |a| * |b| := by
    have hca : (c * a) ^ 2 = c ^ 2 * a ^ 2 := by ring
    rw [hca, ← ha2]
    have : c ^ 2 * |a| ^ 2 = (c ^ 2 * |a|) * |a| := by ring
    rw [this, hsq', mul_comm]
  have h2 : (b / c) ^ 2 = |a| * |b| := by
    rw [div_pow, ← hb2]
    have hbb : |b| ^ 2 = (c ^ 2 * |a|) * |b| := by rw [hsq', sq]
    rw [hbb, mul_assoc]
    field_simp [ne_of_gt hcpos]
  rw [h1, h2, abs_mul]; ring
/-- Мёртвое множество `D` для блока роста: `W_down = 0` ⇒ выход блока — ноль. -/
theorem dead_block_out_zero (W_up : Matrix (Fin h) (Fin d) ℝ) (x : Fin d → ℝ) :
    (0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W_up x) = 0 := by
  simp
/-- Функция потерь по `W_up` при `W_down = 0` постоянна (не зависит от `W_up`):
градиент по верхней матрице нулевой — она заморожена, пока `W_down` не выйдет
из мёртвого множества. -/
theorem dead_loss_const (obj : (Fin d → ℝ) → ℝ) (W₁ W₂ : Matrix (Fin h) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    obj ((0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W₁ x))
      = obj ((0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W₂ x)) := by
  congr 1
  simp

/-- Насыщение хвостов (satTail): клип тритов на `-7, 8` при шкале `s` даёт
ошибку `|x| - 7s` при `|x| > 7s`. После калибровки `x/c` с `c ≥ |x|/(7s)` —
ошибка клипа ноль. Баланс норм убирает переполнение, не меняя функцию. -/
theorem clip_sat_tail (x s : ℝ) (hs : 0 < s) (hx : 7 * s < |x|) :
    |x - if x < 0 then -7 * s else 7 * s| = |x| - 7 * s := by
  rcases lt_or_ge x 0 with hneg | hpos
  · rw [if_pos hneg, abs_of_neg (by rw [abs_of_neg hneg] at hx; linarith), abs_of_neg hneg]
    linarith
  · rw [if_neg (show ¬ x < 0 by linarith), abs_of_pos (by rw [abs_of_nonneg hpos] at hx; linarith),
      abs_of_nonneg hpos]
/-- После калибровки `x/c`, `c ≥ |x|/(7s)`: `|x/c| ≤ 7s` — клип не активен. -/
theorem gauge_kills_sat_tail (x s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (h : |x| / (7 * s) ≤ c) : |x / c| ≤ 7 * s := by
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |x| ≤ c * (7 * s) := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * s)).1 h
    _ = 7 * s * c := mul_comm _ _

/-- Скалярная пара `(d, u)`, выход `d·u·x`, потеря `½(d·u·x − y)²`. -/
noncomputable def pairLoss (d u x y : ℝ) : ℝ := ((d * u * x - y) ^ 2) / 2
/-- Симметричная (нулевая) инициализация `d = 0`: градиент по `u` нулевой —
блок заморожен (`dead_loss_const`). -/
theorem pairGrad_u_zero_at_d0 (u x y : ℝ) :
    HasDerivAt (fun u => pairLoss 0 u x y) 0 u := by
  have : (fun u => pairLoss 0 u x y) = fun _ => y ^ 2 / 2 := by
    funext u; unfold pairLoss; ring
  rw [this]; exact hasDerivAt_const _ _
/-- Асимметричная инициализация `d = ε ≠ 0` (Lu–Shin–Su 2020): градиент по `u`
равен `ε·x·(ε·u·x − y)`; при `u = 0` — `−ε·x·y`, ненулевой, если
`ε·x·y ≠ 0`: верхняя матрица обучается с первого шага. -/
theorem pairGrad_u_at_eps (d u x y : ℝ) :
    HasDerivAt (fun u => pairLoss d u x y) (d * x * (d * u * x - y)) u := by
  unfold pairLoss
  have hd : HasDerivAt (fun u : ℝ => d * u * x - y) (d * x) u := by
    have h0 : HasDerivAt id 1 u := hasDerivAt_id u
    have h1 : HasDerivAt (fun u => d * id u) d u := by simpa using HasDerivAt.const_mul d h0
    have h2 : HasDerivAt (fun u => d * id u * x) (d * x) u := HasDerivAt.mul_const h1 x
    have h3 : HasDerivAt (fun u => d * u * x) (d * x) u := by simpa using h2
    exact h3.sub_const y
  have h4 := (HasDerivAt.pow hd 2).div_const 2
  convert h4 using 1 <;> simp only [pow_succ, Nat.cast_ofNat] <;> ring

/-- Один градиентный шаг по `u` с `u₀ = 0`, `d = ε`: `u₁ = η·ε·x·y`; выход блока
`d·u₁·x = η·ε²·x²·y` — вред квадратичен по `ε`, тогда как градиент (польза)
линеен. Малое `ε` почти бесплатно делает блок обучаемым. -/
theorem asym_step_output_quad (η ε x y : ℝ) :
    ε * (0 - η * (ε * x * (ε * 0 * x - y))) * x = η * ε ^ 2 * x ^ 2 * y := by
  ring
theorem asym_step_nonzero (η ε x y : ℝ) (h : η * ε * (x * y) ≠ 0) :
    0 - η * (ε * x * (ε * 0 * x - y)) ≠ 0 := by
  have h' : η * ε * (x * y) ≠ 0 := h
  intro heq
  have : η * ε * (x * y) = 0 := by nlinarith [heq]
  exact h' this

/-- Ранг-1 NTK-слагаемое линейного фактора `x ↦ (b·a)·x` (скалярная пара): матрица
Грама `K = (b·a)²·(x xᵀ)` на входе `x`; `trace K = (b·a)²·‖x‖²` и `det₊ K` —
инварианты калибровки `(c·b, a/c)` (rank1_gauge), тогда как сумма квадратов
норм факторов — нет и минимизируется балансом (`stock_balance_attained`).
Баланс норм меняет только шум квантования (`clip_sat_tail`), не ядро. -/
theorem rank1_ntk_gauge_invariant (a b c x : ℝ) (hc : c ≠ 0) :
    ((c * b) * (a / c)) ^ 2 * x ^ 2 = (b * a) ^ 2 * x ^ 2 := by
  have h : (c * b) * (a / c) = b * a := by
    field_simp [hc]
  rw [h]

/-- Мёртвое множество в знаковой модели (Lu–Shin–Su 2020, Rister–Rubin 2020):
нейрон с одним входом `x > 0` и случайным знаковым весом мёртв ровно при
отрицательном знаке — доля `1/2`. Независимые знаки на `L` слоях дают `2^L`
равновероятных назначений и лишь одно «все положительные»: доля выживших по
каждому пути `2^{-L}` — вероятность не-мёртвой инициализации падает
экспоненциально с глубиной (нижняя граница Rister–Rubin). -/
theorem dead_one_input_fraction (x : ℝ) (hx : 0 < x) :
    (Finset.univ.filter fun s : Bool => (if s then (1:ℝ) else -1) * x ≤ 0).card = 1 := by
  classical
  refine Finset.card_eq_one.2 ⟨false, Finset.ext ?_⟩
  intro s
  simp only [Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_singleton]
  cases s <;> simp [hx, hx.le]
theorem sign_assignments_card (L : ℕ) :
    (Finset.univ : Finset (Fin L → Bool)).card = 2 ^ L := by
  simp

end Hagi.Step.GaugeBalance

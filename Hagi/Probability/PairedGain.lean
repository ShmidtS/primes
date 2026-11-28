/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.EmpiricalBernstein

/-!
# PairedGain — сертифицированный гейт парного выигрыша адаптера

`paired_gain(before, after)` (selfdev/unified.py): `gain = mean(before − after)`,
нижняя граница `gain − 2.4·SE`, приём при `lower > ADAPTER_MIN_GAIN = 0.005`
на не более чем `ADAPTER_VAL_WINDOWS = 4096` окнах.

* `diffX` — парная разность CE «до − после» как приращение;
* `diffX_sum` — сумма по выборке равна сумме разностей;
* `admit_false_le` — если истинный выигрыш нулевой (`∑ q·D = 0`), разности
  ограничены `b` и имеют дисперсию ≤ `sig`, то с вероятностью ≥ `1 − α` гейт
  НЕ принимает: EB-радиус `radius` заменяет эвристику `2.4·SE`.

Правило кода `2.4·SE` — асимптотическая нормальная аппроксимация;
`radius` даёт конечную выборку гарантию при любом `n`.

* `centX`, `centX_sum` — центрированная разность `D − μ`, `μ = ∑ q·D`;
* `admit_false_le_shifted` — общий случай: истинный выигрыш `μ ≤ g₀` ⇒ приём
  с вероятностью ≤ `α` (гейт `FIBER_MIN_GAIN = 0.01` и адаптерный `0.005`);
* `radius_anti`, `radius_quarter_add`, `radius_quarter_sqrt` — радиус убывает
  по `n`: при `n → 4n` аддитивный член меньше в 4, корневой — в 2 раза;
* `admit_false_union_le` — union bound по раундам ремонта: за `m` раундов
  вероятность хоть одного ложного приёма ≤ `m·α` (код: `paired_margin_eb`
  с `n_states` в `_repair_forgetting`);
* `clip`, `clip_abs_le`, `clip_sub_abs_le_tail`, `mean_clip_bias_le` —
  клиппинг разностей до `c` сужает диапазон `b` (радиус меньше), а смещение
  среднего не превышает среднего хвоста `(|d| − c)₊`;
* `n_suffices` — достаточное число окон: `2σ̂²L/n ≤ (g − g₀ − 2bL/n)²` и
  `2bL/n ≤ g − g₀` дают `radius ≤ g − g₀` — выигрыш `g` проходит гейт;
* `max_gain_le` — winner's curse ограничен: если каждый кандидат в своём
  радиусе (`gain k ≤ μ k + r k`), то `max gain ≤ max μ + max r` — выбор
  максимума не добавляет фактора (совместно с union bound по `K`);
* `short_domain_radius_ge` — цена независимости: при `k ≤ n < 256·k` окно
  `n/k < 256` и радиус не меньше, чем у полной сетки (`radius_anti`);
* `radius_eventually_le` — радиус → 0: при `n ≥ N(ε)` радиус ≤ ε, любой
  фиксированный выигрыш сертификатуем на длинном домене;
* `radiusT sig b α t = √(2σL)·t + 2bL·t²` — радиус в `t = 1/√n`, строго
  возрастает (`radiusT_strict_mono`); `radius_eq_radiusT` — связь;
* `radius_le_iff_root` — точный порог: если `radiusT t* = ε`, то
  `radius(n) ≤ ε ↔ 1/√n ≤ t*` (корень квадратного уравнения, заменяет
  достаточную оценку `N(ε)` из proposal 20 необходимой и достаточной);
* `rootT sig b α ε = (−√(2σL) + √(2σL + 8bLε))/(4bL)` — замкнутая форма
  корня (`rootT_is_root`, `rootT_nonneg`);
* `radius_le_iff_ge_root` — `radius(n) ≤ ε ↔ 1/√n ≤ rootT`: точный порог
  числа окон `n* = ⌈1/rootT²⌉`;
* `prodPq_union_le_sum` — union bound с индивидуальными бюджетами `∑ α r`;
* `delta_budget_scaled` — `δ₀/M` на каждую из `M` проверок на одном holdout
  даёт совокупно `≤ δ₀` (PROPOSAL 21: масштабировать `delta` по числу
  проверок на текущем holdout);
* `radius_delta_cost_le` — цена масштабирования: уровень `α/M` вместо `α`
  увеличивает радиус не более чем на `√(2σ·log M/n) + 2b·log M/n`
  (логарифмическая цена union bound по траектории).
-/

namespace Hagi.Probability.PairedGain
open Hagi.Probability
variable {V : Type} [Fintype V] [Nonempty V]

open Classical in
/-- Гейт адаптера: принять, если нижняя граница парного выигрыша выше `g₀`. -/
def admit (gain r g₀ : ℝ) : Prop := gain - r > g₀
/-- EB-радиус для `n` парных разностей с диапазоном `b` и дисперсией `sig`. -/
noncomputable def radius (sig b n α : ℝ) : ℝ :=
  Real.sqrt (2 * sig * Real.log (2 / α) / n) + 2 * b * Real.log (2 / α) / n
/-- Приращение на шаге `t+1` — парная разность CE «до − после» на окне. -/
def diffX (D : V → ℝ) : ∀ t, (Fin t → V) → ℝ
  | 0, _ => 0
  | t+1, p => D (p (Fin.last t))
omit [Fintype V] [Nonempty V] in
/-- Сумма парных разностей по выборке — то, что измеряет гейт. -/
theorem diffX_sum (D : V → ℝ) (n : ℕ) (ω : Fin n → V) :
    azumaSum (diffX D) n ω = ∑ i, D (ω i) := by
  induction n with
  | zero => simp [azumaSum]
  | succ k ih =>
    rw [azumaSum, ih]
    simp only [diffX]
    rw [Fin.sum_univ_castSucc]
/-- Гейт адаптера с EB-границей: при нулевой гипотезе (средняя разность 0)
вероятность ложного приёма не выше `α`. -/
theorem admit_false_le (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : V → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |D v| ≤ b)
    (sig : ℝ) (hsig : 0 < sig) (hmean : ∑ v, q v * D v = 0)
    (hvar : ∑ v, q v * D v ^ 2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hα2 : α < 1) (g₀ : ℝ) (hg₀ : 0 ≤ g₀) :
    prodPq (fun _ : Fin n => q)
      (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀)) ≥ 1 - α := by
  have hXb : ∀ t pref, |diffX D t pref| ≤ b := by
    intro t pref
    match t, pref with
    | 0, _ => simp [diffX]; exact hb
    | k+1, p => simp [diffX, hbnd]
  have hXm : ∀ t pref, ∑ v, q v * diffX D (t+1) (Fin.snoc pref v) = 0 := by
    intro t pref; simp [diffX, Fin.snoc_last, hmean]
  have hXv : ∀ t pref, ∑ v, q v * diffX D (t+1) (Fin.snoc pref v) ^ 2 ≤ sig := by
    intro t pref; simp [diffX, Fin.snoc_last, hvar]
  have h := empirical_bernstein_mean_bound q hq0 hq1 (diffX D) b hb hXb sig hsig hXm hXv n hn α hα hα2
  simp only [diffX_sum, radius] at h ⊢
  have hmono := prodPq_mono (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩)
    (fun ω => |(∑ i, D (ω i)) / n| < radius sig b n α)
    (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀)) (by
      intro ω habs hgt
      have hle := (abs_lt.1 habs).2
      linarith)
  exact h.trans hmono

/-- Центрированная парная разность: `D − μ`, `μ = ∑ q·D`. -/
def centX (q : V → ℝ) (D : V → ℝ) : ∀ t, (Fin t → V) → ℝ
  | 0, _ => 0
  | t+1, p => D (p (Fin.last t)) - ∑ v, q v * D v
theorem centX_sum (q : V → ℝ) (D : V → ℝ) (n : ℕ) (ω : Fin n → V) :
    azumaSum (centX q D) n ω = (∑ i, D (ω i)) - n * ∑ v, q v * D v := by
  induction n with
  | zero => simp [azumaSum]
  | succ k ih =>
    rw [azumaSum, ih]
    simp only [centX]
    rw [Fin.sum_univ_castSucc]
    push_cast
    ring
/-- Общий гейт: истинный выигрыш ≤ `g₀` ⇒ приём (среднее − радиус > `g₀`) с вероятностью ≤ `α`. -/
theorem admit_false_le_shifted (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (D : V → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |D v - ∑ v', q v' * D v'| ≤ b)
    (sig : ℝ) (hsig : 0 < sig) (hvar : ∑ v, q v * (D v - ∑ v', q v' * D v')^2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (hα : 0 < α) (hα2 : α < 1) (g₀ : ℝ)
    (hμ : ∑ v, q v * D v ≤ g₀) :
    prodPq (fun _ : Fin n => q)
      (fun ω => ¬ ((∑ i, D (ω i)) / n - radius sig b n α > g₀)) ≥ 1 - α := by
  have hXb : ∀ t pref, |centX q D t pref| ≤ b := by
    intro t pref
    match t, pref with
    | 0, _ => simp [centX]; exact hb
    | k+1, p => simp [centX, hbnd]
  have hXm : ∀ t pref, ∑ v, q v * centX q D (t+1) (Fin.snoc pref v) = 0 := by
    intro t pref
    simp only [centX, Fin.snoc_last, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hq1, one_mul, sub_self]
  have hXv : ∀ t pref, ∑ v, q v * centX q D (t+1) (Fin.snoc pref v) ^ 2 ≤ sig := by
    intro t pref; simp only [centX, Fin.snoc_last]; exact hvar
  have h := empirical_bernstein_mean_bound q hq0 hq1 (centX q D) b hb hXb sig hsig hXm hXv n hn α hα hα2
  simp only [centX_sum, radius] at h ⊢
  have hmono := prodPq_mono (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩)
    (fun ω => |((∑ i, D (ω i)) - n * ∑ v, q v * D v) / n| <
      Real.sqrt (2 * sig * Real.log (2 / α) / n) + 2 * b * Real.log (2 / α) / n)
    (fun ω => ¬ ((∑ i, D (ω i)) / n - (Real.sqrt (2 * sig * Real.log (2 / α) / n) +
      2 * b * Real.log (2 / α) / n) > g₀)) (by
      intro ω habs hgt
      have hle := (abs_lt.1 habs).2
      have hdiv : ((∑ i, D (ω i)) - n * ∑ v, q v * D v) / n = (∑ i, D (ω i)) / n - ∑ v, q v * D v := by
        field_simp
      rw [hdiv] at hle
      linarith [hμ])
  exact h.trans hmono

/-- EB-радиус убывает по `n`: больше окон — уже граница. -/
theorem radius_anti (sig b α : ℝ) (hα : 0 < α) (hα2 : α < 1) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (hsig : 0 ≤ sig) (hb : 0 ≤ b) :
    radius sig b m α ≤ radius sig b n α := by
  have hL : 0 ≤ Real.log (2 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα]; linarith [hα2])
  unfold radius
  gcongr <;> omega
/-- При `m = 4n` аддитивный член меньше в 4 раза, корневой — в 2. -/
theorem radius_quarter_add (b α : ℝ) (n : ℕ) (hn : 0 < n) :
    2 * b * Real.log (2 / α) / (4 * n) = (2 * b * Real.log (2 / α) / n) / 4 := by
  field_simp
theorem radius_quarter_sqrt (sig α : ℝ) (hsig : 0 ≤ sig) (hα : 0 < α) (hα2 : α < 1)
    (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * sig * Real.log (2 / α) / (4 * n)) = Real.sqrt (2 * sig * Real.log (2 / α) / n) / 2 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (((4:ℝ)) * (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (show 0 ≤ (4:ℝ) by norm_num)]; norm_num
  have hL : 0 ≤ Real.log (2 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα]; linarith)
  have hnn : 0 ≤ 2 * sig * Real.log (2 / α) := by positivity
  push_cast
  rw [Real.sqrt_div hnn, Real.sqrt_div hnn, hsqrt, div_div, mul_comm (Real.sqrt (n : ℝ)) ((2:ℝ))]

variable {n : ℕ}
open Finset
open Classical in
/-- Union bound over repair rounds: each round `r < m` tests its own paired
sample `ω` with EB radius at level `α`; the probability that SOME round falsely
admits is at most `m·α`. (The code's paired_margin_eb passes n_states to do
the same via α/n_states.) -/
theorem admit_false_union_le {n : ℕ} (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (α : ℝ) (m : ℕ) (A : Fin m → (Fin n → V) → Prop)
    (hA : ∀ r : Fin m, prodPq (fun _ : Fin n => q) (A r) ≤ α) :
    prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω) ≤ m * α := by
  classical
  have hu := prodPq_union_finset (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩) univ A
  have heq : prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω)
      = prodPq (fun _ : Fin n => q) (fun ω => ∃ i ∈ univ, A i ω) :=
    prodPq_iff _ _ _ (fun ω => ⟨fun ⟨r, hr⟩ => ⟨r, Finset.mem_univ r, hr⟩,
      fun ⟨r, _, hr⟩ => ⟨r, hr⟩⟩)
  rw [heq]
  calc prodPq (fun _ : Fin n => q) (fun ω => ∃ i ∈ univ, A i ω)
      ≤ ∑ r : Fin m, prodPq (fun _ : Fin n => q) (A r) := by
        convert hu using 1 <;> congr 1 <;> exact Subsingleton.elim _ _
    _ ≤ ∑ _r : Fin m, α := Finset.sum_le_sum fun r _ => hA r
    _ = m * α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]

/-- Клиппинг разности в `[-c, c]`. -/
noncomputable def clip (c x : ℝ) : ℝ := max (-c) (min c x)
theorem clip_abs_le (c x : ℝ) (hc : 0 ≤ c) : |clip c x| ≤ c := by
  unfold clip
  rw [abs_le]
  exact ⟨by linarith [le_max_left (-c) (min c x)], max_le (by linarith) (min_le_left _ _)⟩
/-- Клиппинг меняет `x` только за пределами `[-c, c]`, на расстояние ≤ хвост. -/
theorem clip_sub_abs_le_tail (c x : ℝ) (hc : 0 ≤ c) : |clip c x - x| ≤ max 0 (|x| - c) := by
  unfold clip
  rcases lt_or_ge x (-c) with hx | hx
  · have hxc : x ≤ c := by linarith
    rw [min_eq_right hxc, max_eq_left hx.le]
    rw [abs_of_pos (by linarith [hx]), abs_of_neg (by linarith [hx])]
    have hpos : 0 < -x - c := by linarith [hx]
    rw [max_eq_right hpos.le]
    linarith
  · rcases le_or_gt x c with hxc | hxc
    · rw [min_eq_right hxc, max_eq_right hx]
      simp
    · rw [min_eq_left hxc.le, show max (-c) c = c from max_eq_right (by linarith [hc])]
      rw [abs_of_neg (sub_neg.2 hxc), abs_of_pos (by linarith [hxc, hc])]
      rw [max_eq_right (sub_nonneg.2 hxc.le)]
      linarith
/-- Смещение среднего от клиппинга ≤ средний хвост `(|d_i| − c)₊`. -/
theorem mean_clip_bias_le (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (d : Fin n → ℝ) :
    |(∑ i, d i) / n - (∑ i, clip c (d i)) / n| ≤ (∑ i, max 0 (|d i| - c)) / n := by
  have h : ∀ i, |clip c (d i) - d i| ≤ max 0 (|d i| - c) := fun i => clip_sub_abs_le_tail c (d i) hc
  have hs : |(∑ i, d i) - (∑ i, clip c (d i))| ≤ ∑ i, max 0 (|d i| - c) := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ i, (d i - clip c (d i))| ≤ ∑ i, |d i - clip c (d i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |clip c (d i) - d i| := Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
      _ ≤ ∑ i, max 0 (|d i| - c) := Finset.sum_le_sum fun i _ => h i
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show (∑ i, d i) / (n:ℝ) - (∑ i, clip c (d i)) / (n:ℝ)
        = ((∑ i, d i) - (∑ i, clip c (d i))) / (n:ℝ) by ring, abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right hs hnpos.le

/-- Достаточное число окон: если наблюдаемый выигрыш `g` и `n` таковы, что
радиус ≤ `g − g₀`, гейт (`mean − r > g₀`) срабатывает. -/
theorem n_suffices (sig b α g g₀ : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 ≤ sig)
    (hb : 0 ≤ b) (hg : 0 < g - g₀) (n : ℕ) (hn : 0 < n)
    (hsq : 2 * sig * Real.log (2 / α) / n ≤ (g - g₀ - 2 * b * Real.log (2 / α) / n) ^ 2)
    (hadd : 2 * b * Real.log (2 / α) / n ≤ g - g₀) :
    radius sig b n α ≤ g - g₀ := by
  have hL : 0 ≤ Real.log (2 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα]; linarith [hα2])
  unfold radius
  have hsqrt : Real.sqrt (2 * sig * Real.log (2 / α) / n) ≤ g - g₀ - 2 * b * Real.log (2 / α) / n := by
    exact Real.sqrt_le_iff.2
      ⟨by linarith [hadd], hsq⟩
  linarith

/-- Winner's curse, bounded: if every candidate's gain is within its own
radius of its true gain (`gain k ≤ μ k + r k`), the selected maximum is within
the worst radius of the best true gain: `max gain ≤ max μ + max r`. Selection
adds no extra factor. -/
theorem max_gain_le (S : Finset ℕ) (hS : S.Nonempty) (gain μ r : ℕ → ℝ)
    (hE : ∀ k ∈ S, gain k ≤ μ k + r k) :
    (S.image gain).max' (image_nonempty.2 hS) ≤
      (S.image μ).max' (image_nonempty.2 hS) + (S.image r).max' (image_nonempty.2 hS) := by
  apply Finset.max'_le
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  have h1 : μ k ≤ (S.image μ).max' (image_nonempty.2 hS) :=
    le_max' _ _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)
  have h2 : r k ≤ (S.image r).max' (image_nonempty.2 hS) :=
    le_max' _ _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)
  linarith [hE k hk]

/-- Цена независимости на коротком домене: при `n < 256·k` сетка из
`windows_exist` берёт `m = n/k < 256` окон, и EB-радиус не меньше, чем у
полной сетки из 256 окон. -/
theorem short_domain_radius_ge (sig b α : ℝ) (hα : 0 < α) (hα2 : α < 1)
    (hsig : 0 ≤ sig) (hb : 0 ≤ b) (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (h : n < 256 * k) :
    radius sig b 256 α ≤ radius sig b ((n / k : ℕ) : ℝ) α := by
  have hlt : n / k < 256 := (Nat.div_lt_iff_lt_mul (by omega)).2 h
  have hpos : 0 < n / k := Nat.div_pos hkn hk
  exact radius_anti sig b α hα hα2 (n / k) 256 hpos (by omega) hsig hb

/-- Радиус EB сколь угодно мал на длинном домене: при `n ≥ N(ε)` радиус ≤ ε
(`N = max(⌈8σL/ε²⌉+1, ⌈4bL/ε⌉+1)`, `L = log(2/α)`) — любой фиксированный
выигрыш `g − g₀ > ε` сертификатуем на достаточно длинном домене (`n_suffices`). -/
theorem radius_eventually_le (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 ≤ sig)
    (hb : 0 ≤ b) (he : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → radius sig b n α ≤ ε := by
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith [hα2])
  set L := Real.log (2 / α) with hLdef
  have hε2 : 0 < ε ^ 2 / 4 := by positivity
  have hεh : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, (0:ℝ) < N₁ ∧ 2 * sig * L ≤ ε ^ 2 / 4 * N₁ := by
    refine ⟨Nat.ceil (2 * sig * L / (ε ^ 2 / 4)) + 1, by positivity, ?_⟩
    have hc := Nat.le_ceil (2 * sig * L / (ε ^ 2 / 4))
    have hcR : (2 * sig * L / (ε ^ 2 / 4) : ℝ) ≤ Nat.ceil (2 * sig * L / (ε ^ 2 / 4)) := by exact_mod_cast hc
    rw [div_le_iff₀ hε2] at hcR
    push_cast
    nlinarith
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, (0:ℝ) < N₂ ∧ 2 * b * L ≤ ε / 2 * N₂ := by
    refine ⟨Nat.ceil (2 * b * L / (ε / 2)) + 1, by positivity, ?_⟩
    have hc := Nat.le_ceil (2 * b * L / (ε / 2))
    have hcR : (2 * b * L / (ε / 2) : ℝ) ≤ Nat.ceil (2 * b * L / (ε / 2)) := by exact_mod_cast hc
    rw [div_le_iff₀ hεh] at hcR
    push_cast
    nlinarith
  refine ⟨max N₁ N₂, fun n hn _ => ?_⟩
  have hnR : (0:ℝ) < n := by positivity
  have hmax1 : (N₁ : ℝ) ≤ n := by exact_mod_cast (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hmax2 : (N₂ : ℝ) ≤ n := by exact_mod_cast (Nat.le_trans (Nat.le_max_right _ _) hn)
  have h1 : 2 * sig * L / n ≤ ε ^ 2 / 4 := by
    rw [div_le_iff₀ hnR]
    calc 2 * sig * L ≤ ε ^ 2 / 4 * N₁ := hN₁.2
      _ ≤ ε ^ 2 / 4 * n := by nlinarith [hε2]
  have h2 : 2 * b * L / n ≤ ε / 2 := by
    rw [div_le_iff₀ hnR]
    calc 2 * b * L ≤ ε / 2 * N₂ := hN₂.2
      _ ≤ ε / 2 * n := by nlinarith [hεh]
  show Real.sqrt (2 * sig * L / (n:ℝ)) + 2 * b * L / (n:ℝ) ≤ ε
  have hsq : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
  have hsqrt : Real.sqrt (2 * sig * L / (n:ℝ)) ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt (show 2 * sig * L / (n:ℝ) ≤ (ε / 2) ^ 2 by rw [hsq]; exact h1)
    rw [Real.sqrt_sq (by linarith)] at h
    exact h
  linarith

/-- Радиус в переменной `t = 1/√n`: `A·t + B·t²`, строго возрастает по `t ≥ 0`. -/
noncomputable def radiusT (sig b α t : ℝ) : ℝ :=
  Real.sqrt (2 * sig * Real.log (2 / α)) * t + 2 * b * Real.log (2 / α) * t ^ 2
theorem radiusT_strict_mono (sig b α : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 < sig) (hb : 0 ≤ b)
    (t₁ t₂ : ℝ) (h₁ : 0 ≤ t₁) (h : t₁ < t₂) : radiusT sig b α t₁ < radiusT sig b α t₂ := by
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith [hα2])
  unfold radiusT
  have hA : 0 < Real.sqrt (2 * sig * Real.log (2 / α)) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 ≤ 2 * b * Real.log (2 / α) := by positivity
  have h1 : Real.sqrt (2 * sig * Real.log (2 / α)) * t₁ < Real.sqrt (2 * sig * Real.log (2 / α)) * t₂ := mul_lt_mul_of_pos_left h hA
  have h2 : 2 * b * Real.log (2 / α) * t₁ ^ 2 ≤ 2 * b * Real.log (2 / α) * t₂ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hB
    nlinarith
  linarith
/-- Радиус как функция `n` — это `radiusT` в `t = 1/√n`. -/
theorem radius_eq_radiusT (sig b α : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 ≤ sig)
    (n : ℕ) (hn : 0 < n) :
    radius sig b n α = radiusT sig b α (1 / Real.sqrt n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith)
  have hA : (0:ℝ) ≤ 2 * sig * Real.log (2 / α) := mul_nonneg (by linarith) hL.le
  unfold radius radiusT
  rw [Real.sqrt_div hA ↑n]
  rw [div_pow, one_pow, Real.sq_sqrt hnR.le]
  ring
/-- Точный порог: если `t*` — корень `radiusT t* = ε`, то `radius(n) ≤ ε ⇔ 1/√n ≤ t*`. -/
theorem radius_le_iff_root (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 < sig) (hb : 0 ≤ b)
    (tstar : ℝ) (ht0 : 0 ≤ tstar) (hroot : radiusT sig b α tstar = ε) (n : ℕ) (hn : 0 < n) :
    radius sig b n α ≤ ε ↔ 1 / Real.sqrt n ≤ tstar := by
  rw [radius_eq_radiusT sig b α hα hα2 hsig.le n hn]
  constructor
  · intro h
    by_contra hcon
    have hlt : tstar < 1 / Real.sqrt n := lt_of_not_ge hcon
    have := radiusT_strict_mono sig b α hα hα2 hsig hb tstar (1 / Real.sqrt n) ht0 hlt
    linarith
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · have h0 : (0:ℝ) ≤ 1 / Real.sqrt n := by positivity
      have := radiusT_strict_mono sig b α hα hα2 hsig hb (1 / Real.sqrt n) tstar h0 hlt
      linarith
    · rw [heq, hroot]

/-- Замкнутая форма корня: `t* = (−A + √(A² + 4Bε)) / (2B)`,
`A = √(2σL)`, `B = 2bL`. -/
noncomputable def rootT (sig b α ε : ℝ) : ℝ :=
  let A := Real.sqrt (2 * sig * Real.log (2 / α))
  let B := 2 * b * Real.log (2 / α)
  (-A + Real.sqrt (A ^ 2 + 4 * B * ε)) / (2 * B)
theorem rootT_nonneg (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 ≤ sig)
    (hb : 0 < b) (he : 0 < ε) : 0 ≤ rootT sig b α ε := by
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith)
  have hA : 0 ≤ Real.sqrt (2 * sig * Real.log (2 / α)) := Real.sqrt_nonneg _
  have hB : 0 < 2 * b * Real.log (2 / α) := by positivity
  unfold rootT
  have hs : Real.sqrt (2 * sig * Real.log (2 / α)) ≤
      Real.sqrt (Real.sqrt (2 * sig * Real.log (2 / α)) ^ 2 + 4 * (2 * b * Real.log (2 / α)) * ε) := by
    apply (Real.le_sqrt hA (show (0:ℝ) ≤ Real.sqrt (2 * sig * Real.log (2 / α)) ^ 2
        + 4 * (2 * b * Real.log (2 / α)) * ε by positivity)).2
    nlinarith
  apply div_nonneg _ (by positivity)
  linarith
theorem rootT_is_root (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 ≤ sig)
    (hb : 0 < b) (he : 0 < ε) : radiusT sig b α (rootT sig b α ε) = ε := by
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith)
  unfold rootT radiusT
  have hA : 0 ≤ Real.sqrt (2 * sig * Real.log (2 / α)) := Real.sqrt_nonneg _
  have hB : 0 < 2 * b * Real.log (2 / α) := by positivity
  set A := Real.sqrt (2 * sig * Real.log (2 / α)) with hAdef
  set B := 2 * b * Real.log (2 / α) with hBdef
  set D := A ^ 2 + 4 * B * ε with hD
  have hDpos : 0 < D := by nlinarith
  have hDsqrt : Real.sqrt D ^ 2 = D := Real.sq_sqrt (by linarith)
  have hAsq : A ^ 2 = 2 * sig * Real.log (2 / α) := Real.sq_sqrt (by positivity)
  -- раскрываем
  show A * ((-A + Real.sqrt D) / (2 * B)) + B * ((-A + Real.sqrt D) / (2 * B)) ^ 2 = ε
  field_simp [hB.ne']
  nlinarith [hDsqrt, hAsq, mul_pos hB he]
/-- Точный порог числа окон: `n ≥ n* = ⌈1/t*²⌉` ⇔ радиус ≤ ε. -/
theorem radius_le_iff_ge_root (sig b α ε : ℝ) (hα : 0 < α) (hα2 : α < 1) (hsig : 0 < sig)
    (hb : 0 < b) (he : 0 < ε) (n : ℕ) (hn : 0 < n) :
    radius sig b n α ≤ ε ↔ 1 / Real.sqrt n ≤ rootT sig b α ε :=
  radius_le_iff_root sig b α ε hα hα2 hsig hb.le (rootT sig b α ε)
    (rootT_nonneg sig b α ε hα hα2 hsig.le hb he)
    (rootT_is_root sig b α ε hα hα2 hsig.le hb he) n hn

open scoped Classical in
/-- Union bound с индивидуальными бюджетами: `P(∃ r, A r) ≤ ∑ α r`. -/
theorem prodPq_union_le_sum {n : ℕ} (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (m : ℕ) (A : Fin m → (Fin n → V) → Prop) (α : Fin m → ℝ)
    (hA : ∀ r, prodPq (fun _ : Fin n => q) (A r) ≤ α r) :
    prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω) ≤ ∑ r, α r := by
  classical
  have hu := prodPq_union_finset (fun _ : Fin n => q) (fun i => ⟨fun v => hq0 v, hq1⟩) univ A
  have heq : prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω)
      = prodPq (fun _ : Fin n => q) (fun ω => ∃ i ∈ univ, A i ω) :=
    prodPq_iff _ _ _ (fun ω => ⟨fun ⟨r, hr⟩ => ⟨r, Finset.mem_univ r, hr⟩,
      fun ⟨r, _, hr⟩ => ⟨r, hr⟩⟩)
  rw [heq]
  calc prodPq (fun _ : Fin n => q) (fun ω => ∃ i ∈ univ, A i ω)
      ≤ ∑ r : Fin m, prodPq (fun _ : Fin n => q) (A r) := by
        convert hu using 1 <;> congr 1 <;> exact Subsingleton.elim _ _
    _ ≤ ∑ r, α r := Finset.sum_le_sum fun r _ => hA r

open scoped Classical in
/-- Бюджет `δ₀`, разделённый на `M` проверок на одном holdout: совокупная
вероятность ложного приёма `≤ δ₀` независимо от `M`. -/
theorem delta_budget_scaled {n : ℕ} (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (δ₀ : ℝ) (M : ℕ) (hM : 0 < M) (A : Fin M → (Fin n → V) → Prop)
    (hA : ∀ r, prodPq (fun _ : Fin n => q) (A r) ≤ δ₀ / M) :
    prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω) ≤ δ₀ := by
  calc prodPq (fun _ : Fin n => q) (fun ω => ∃ r, A r ω) ≤ ∑ _r : Fin M, δ₀ / M :=
      prodPq_union_le_sum q hq0 hq1 M A (fun _ => δ₀ / M) hA
    _ = δ₀ := by
        have h : (∑ x : Fin M, δ₀) / (M:ℝ) = δ₀ := by simp [ne_of_gt hM]
        exact (Finset.sum_div _ _ _).symm.trans h

/-- Цена union bound по `M` проверкам: уровень `α` становится `α/M`, радиус
растёт не более чем на `√(2σ·log M/n) + 2b·log M/n`. -/
theorem radius_delta_cost_le (sig b α : ℝ) (hα : 0 < α) (hαM : α < 1) (hsig : 0 ≤ sig)
    (hb : 0 ≤ b) (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : 1 ≤ M) :
    radius sig b n (α / M) ≤ radius sig b n α
      + Real.sqrt (2 * sig * Real.log M / n) + 2 * b * Real.log M / n := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hαM' : 0 < α / M := div_pos hα hMpos
  have hαM2 : α / M < 1 := by rw [div_lt_iff₀ hMpos]; linarith
  have hL : 0 < Real.log (2 / α) := Real.log_pos (by rw [lt_div_iff₀ hα]; linarith)
  have hLM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.log (2 / (α / M)) = Real.log (2 / α) + Real.log M := by
    rw [show 2 / (α / M) = (2 / α) * M by field_simp]
    rw [Real.log_mul (by positivity) (by positivity)]
  unfold radius
  rw [hsplit]
  have h1 : Real.sqrt (2 * sig * (Real.log (2 / α) + Real.log M) / n)
      ≤ Real.sqrt (2 * sig * Real.log (2 / α) / n) + Real.sqrt (2 * sig * Real.log M / n) := by
    rw [show 2 * sig * (Real.log (2 / α) + Real.log M) / n
        = (2 * sig * Real.log (2 / α) / n) + (2 * sig * Real.log M / n) by ring]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    have hA := Real.sq_sqrt (show 0 ≤ 2 * sig * Real.log (2 / α) / n by positivity)
    have hB := Real.sq_sqrt (show 0 ≤ 2 * sig * Real.log M / n by positivity)
    have hnn : 0 ≤ Real.sqrt (2 * sig * Real.log (2 / α) / n) * Real.sqrt (2 * sig * Real.log M / n) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have h2 : 2 * b * (Real.log (2 / α) + Real.log M) / n
      = 2 * b * Real.log (2 / α) / n + 2 * b * Real.log M / n := by ring
  rw [h2]
  linarith

/-- Разбиение бюджета окон `W` поровну на `m` старых доменов (OLD_GATE_WINDOWS
в HAGI_v2): радиус каждого домена radius(σ, b, W/m, α) лежит между √m-кратным
и m-кратным радиусом одного домена с полным бюджетом: шумовое слагаемое растёт
как `√m`, смещение — как `m`. Худший домен при ограниченном бюджете стоит
дороже именно по смещению. -/
theorem budget_split_radius_bounds (sig b W α m : ℝ) (hsig : 0 < sig) (hb : 0 ≤ b)
    (hW : 0 < W) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (hm : 1 ≤ m) :
    Real.sqrt m * Real.sqrt (2 * sig * Real.log (2 / α) / W)
        ≤ radius sig b (W / m) α
      ∧ radius sig b (W / m) α ≤ m * radius sig b W α := by
  have hL : 0 < Real.log (2 / α) := by
    apply Real.log_pos
    have : 1 < 2 / α := (lt_div_iff₀ hα).2 (by linarith)
    linarith
  have hm0 : 0 < m := by linarith
  have hWm : 0 < W / m := div_pos hW hm0
  constructor
  · unfold radius
    have hdiv : 2 * sig * Real.log (2 / α) / (W / m)
        = m * (2 * sig * Real.log (2 / α) / W) := by
      field_simp [ne_of_gt hWm, ne_of_gt hW]
    have h1 : Real.sqrt (2 * sig * Real.log (2 / α) / (W / m))
        = Real.sqrt m * Real.sqrt (2 * sig * Real.log (2 / α) / W) := by
      rw [hdiv, Real.sqrt_mul (by positivity : (0:ℝ) ≤ m), mul_comm]
    rw [h1]
    have h2 : 0 ≤ 2 * b * Real.log (2 / α) / (W / m) := by positivity
    linarith
  · unfold radius
    have hdiv : 2 * sig * Real.log (2 / α) / (W / m)
        = m * (2 * sig * Real.log (2 / α) / W) := by
      field_simp [ne_of_gt hWm, ne_of_gt hW]
    have h1 : Real.sqrt (2 * sig * Real.log (2 / α) / (W / m))
        ≤ m * Real.sqrt (2 * sig * Real.log (2 / α) / W) := by
      rw [hdiv, Real.sqrt_mul (by positivity : (0:ℝ) ≤ m), mul_comm]
      have hs : Real.sqrt m ≤ m := by
        have := Real.sq_sqrt (show 0 ≤ m by linarith)
        nlinarith [Real.sqrt_nonneg m]
      have hA : 0 ≤ Real.sqrt (2 * sig * Real.log (2 / α) / W) := Real.sqrt_nonneg _
      nlinarith
    have h3 : 2 * b * Real.log (2 / α) / (W / m) = m * (2 * b * Real.log (2 / α) / W) := by
      field_simp [ne_of_gt hWm, ne_of_gt hW]
    rw [h3]
    linarith

/-- Clamp бюджета окон (HAGI_v2 `w = min 256, max 16, W/n`): при любом числе
доменов `n` на домен приходится не меньше 16 окон, поэтому радиус шума не
превосходит `radius(16)` — константа, не зависящая от `n` (измерено кодом:
0.16 нат при 16 окнах). Цена: при `n > W/16` худший домен не отличает
прирост, меньший `radius(16)`, от шума. -/
theorem clamped_budget_radius_le (sig b α : ℝ) (hα : 0 < α) (hα2 : α < 1)
    (hsig : 0 ≤ sig) (hb : 0 ≤ b) (w : ℕ) (hw : 16 ≤ w) :
    radius sig b w α ≤ radius sig b 16 α :=
  radius_anti sig b α hα hα2 16 w (by norm_num) hw hsig hb

end Hagi.Probability.PairedGain

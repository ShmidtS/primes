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
  максимума не добавляет фактора (совместно с union bound по `K`).
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

end Hagi.Probability.PairedGain

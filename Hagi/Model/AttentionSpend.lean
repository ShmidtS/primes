import Hagi.Model.Attention

/-!
# Композиционная экономия внимания: SWA × GQA

Гибридное внимание — скользящее окно + сгруппированные
KV-головки — строго дешевле плотного многоголового
внимания: относительная стоимость равна произведению
факторов экономии (окно/длина) × (KV-головки/головки).
Механизмы экономии перемножаются, не складываются.
-/

namespace Hagi.Model.AttentionSpend

open Hagi.Model.GQA Hagi.Model.SWA

/-- Стоимость плотного внимания: длина × контекст × все
головки. -/
def denseAttnCost (T n n_h d : ℕ) : ℕ := T * n * n_h * d

/-- Стоимость гибридного внимания: окно × KV-головки. -/
def hybridAttnCost (T w n_kv d : ℕ) : ℕ := T * (2 * w + 1) * n_kv * d

/-- ПРЯМОЕ СРАВНЕНИЕ: окно короче последовательности и
KV-групп меньше головок ⟹ гибрид строго дешевле плотного
внимания. -/
theorem hybrid_spend_lt (T n w n_h n_kv d : ℕ)
    (hT : 0 < T) (hd : 0 < d)
    (hw : 2 * w + 1 < n) (hkv : n_kv < n_h) :
    hybridAttnCost T w n_kv d < denseAttnCost T n n_h d := by
  have core : (2 * w + 1) * n_kv * d < n * n_h * d := by
    rcases Nat.eq_zero_or_pos n_kv with h0 | hp
    · rw [h0]
      have hn : (0:ℕ) < n := by omega
      have hh : (0:ℕ) < n_h := by omega
      have hpos : (0:ℕ) < n * n_h * d :=
        Nat.mul_pos (Nat.mul_pos hn hh) hd
      rw [Nat.mul_zero, Nat.zero_mul]
      exact hpos
    · calc (2 * w + 1) * n_kv * d
          < n * n_kv * d :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (by omega : (2 * w + 1) < n) hp) hd
        _ ≤ n * n_h * d := by gcongr
  unfold hybridAttnCost denseAttnCost
  gcongr

/-- ОТНОСИТЕЛЬНАЯ СТОИМОСТЬ — ПРОИЗВЕДЕНИЕ ФАКТОРОВ:
гибрид/плотное = (окно/длина) × (KV/головки) — механизмы
экономии независимы и перемножаются. -/
theorem hybrid_ratio (T n w n_h n_kv d : ℕ)
    (hT : 0 < T) (hn : 0 < n) (hh : 0 < n_h) (hd : 0 < d) :
    (hybridAttnCost T w n_kv d : ℝ) / (denseAttnCost T n n_h d : ℝ)
      = ((2 * w + 1 : ℝ) / n) * ((n_kv : ℝ) / n_h) := by
  have hpos : (0:ℝ) < (denseAttnCost T n n_h d : ℝ) := by
    unfold denseAttnCost
    positivity
  simp only [hybridAttnCost, denseAttnCost, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-- СЛЕДСТВИЕ-ФОРМА ПЛАНА: относительная стоимость
строго меньше произведения факторов, каждый ≤
соответствующей доли; при окне короче длины и меньшем
числе KV-групп — строго меньше единицы. -/
theorem hybrid_ratio_lt_one (T n w n_h n_kv d : ℕ)
    (hT : 0 < T) (hn : 0 < n) (hh : 0 < n_h) (hd : 0 < d)
    (hw : 2 * w + 1 < n) (hkv : n_kv < n_h) :
    (hybridAttnCost T w n_kv d : ℝ)
      / (denseAttnCost T n n_h d : ℝ) < 1 := by
  rw [hybrid_ratio T n w n_h n_kv d hT hn hh hd]
  have h1 : ((2 * w + 1 : ℝ) / n) < 1 := by
    rw [div_lt_one₀ (by positivity : (0:ℝ) < n)]
    exact_mod_cast hw
  have h2 : ((n_kv : ℝ) / n_h) < 1 := by
    rw [div_lt_one₀ (by positivity : (0:ℝ) < n_h)]
    exact_mod_cast hkv
  have hp1 : (0:ℝ) < (2 * w + 1 : ℝ) / n :=
    div_pos (by positivity) (by positivity)
  have hp2 : (0:ℝ) ≤ (n_kv : ℝ) / n_h :=
    div_nonneg (by positivity) (by positivity)
  nlinarith [h1, h2, hp1, hp2]

/-- ПОЛНЫЙ СТЕК: глубина × MoD-ширина × окно × KV-группы. -/
def fullStackCost (L k w n_kv d : ℕ) : ℕ :=
  L * k * (2 * w + 1) * n_kv * d

/-- Плотный базлайн полного стека: глубина × длина ×
длина × все головки. -/
def fullDenseCost (L n n_h d : ℕ) : ℕ :=
  L * n * n * n_h * d

/-- ПОЛНАЯ КОМПОЗИЦИЯ: относительная стоимость полного
гибридного стека — ТОЧНОЕ произведение трёх факторов
экономии (MoD k/n) × (окно/длина) × (KV/головки). -/
theorem fullStack_ratio (L n w n_h n_kv k d : ℕ)
    (hL : 0 < L) (hn : 0 < n) (hh : 0 < n_h) (hd : 0 < d) :
    (fullStackCost L k w n_kv d : ℝ)
      / (fullDenseCost L n n_h d : ℝ)
      = ((k : ℝ) / n) * ((2 * w + 1 : ℝ) / n)
        * ((n_kv : ℝ) / n_h) := by
  simp only [fullStackCost, fullDenseCost, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-- ПОЛНЫЙ ГИБРИД СТРОГО ДЕШЕВЛЕ: при трёх активных
механизмах экономии (k < n, окно < длины, n_kv < n_h)
полный стек строго дешевле плотного базлайна. -/
theorem fullStack_lt (L n w n_h n_kv k d : ℕ)
    (hL : 0 < L) (hd : 0 < d)
    (hk : k < n) (hw : 2 * w + 1 < n) (hkv : n_kv < n_h) :
    fullStackCost L k w n_kv d < fullDenseCost L n n_h d := by
  unfold fullStackCost fullDenseCost
  gcongr <;> omega

end Hagi.Model.AttentionSpend

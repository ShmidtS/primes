import Mathlib.Tactic
import Mathlib.Data.List.SplitLengths

/-!
# AdaptiveChunking (приоритет 3 «HAGI Neural Computer»,
# ): динамический чанкинг H-Net — M зависит от
# ВХОДА и параметров, а не фиксирован.

Статическая теория (HNet.lean) оценивает cost при
константном коэффициенте r. Реальное преимущество H-Net —
обучаемые границы: M_φ(x) = ChunkCount(H_φ(x)).

Формализуем честное сравнение:
1. `adaptive_cost`: C(x) = Σ_ℓ c_ℓ·M_ℓ(x)² — суммарная
   стоимость иерархии как функция входа;
2. `adaptive_le_static`: при ПОТОЧЕЧНОМ доминировании
   (∀ℓ, M_ℓ(x) ≤ L/r) динамическая стоимость ≤ статической
   (Σ c_ℓ (L/r)²) — адаптивность не хуже статического
   сжатия, если чанкер не проигрывает ни на одном уровне;
3. `adaptive_lt_of_strict`: строгое превосходство на одном
   уровне при неотрицательных ценах даёт строгую экономию.
-/

namespace Hagi.Model.AdaptiveChunking

variable {k : Type*} [Fintype k]

/-- Иерархическая стоимость: сумма по уровням c_ℓ·M_ℓ(x)². -/
noncomputable def adaptiveCost (c : k → ℝ) (M : k → ℝ) : ℝ :=
  ∑ l, c l * M l ^ 2

/-- АДАПТИВНОСТЬ НЕ ХУЖЕ СТАТИКИ: если динамический чанкер
на каждом уровне укладывается в статический размер
(M_ℓ(x) ≤ L/r ∀ℓ), то полная иерархическая стоимость не
превосходит статической. -/
theorem adaptive_le_static (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (M : k → ℝ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hM : ∀ l, 0 ≤ M l)
    (hdom : ∀ l, M l ≤ L / r) :
    adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2 := by
  have h1 : ∀ l : k, c l * M l ^ 2 ≤ c l * (L / r) ^ 2 := by
    intro l
    exact mul_le_mul_of_nonneg_left
      (by rw [sq, sq]; exact mul_self_le_mul_self (hM l) (hdom l)) (hc l)
  exact Finset.sum_le_sum (fun l _ => h1 l)

/-- СТРОГОЕ ПРЕИМУЩЕСТВО: положительная цена на уровне
l₀ и строгое доминирование M_{l₀}(x) < L/r дают строгую
экономию полной стоимости. -/
theorem adaptive_lt_of_strict (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (M : k → ℝ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hM : ∀ l, 0 ≤ M l)
    (hdom : ∀ l, M l ≤ L / r)
    (l₀ : k) (hc₀ : 0 < c l₀) (hstrict : M l₀ < L / r) :
    adaptiveCost c M < ∑ l, c l * (L / r) ^ 2 := by
  have h1 : ∀ l : k, c l * M l ^ 2 ≤ c l * (L / r) ^ 2 := by
    intro l
    exact mul_le_mul_of_nonneg_left
      (by rw [sq, sq]; exact mul_self_le_mul_self (hM l) (hdom l)) (hc l)
  have hstrictl : c l₀ * M l₀ ^ 2 < c l₀ * (L / r) ^ 2 := by
    have hkey : M l₀ ^ 2 < (L / r) ^ 2 := by
      rw [sq, sq]
      exact mul_self_lt_mul_self (hM l₀) hstrict
    exact mul_lt_mul_of_pos_left hkey hc₀
  exact Finset.sum_lt_sum (fun l _ => h1 l)
    ⟨l₀, Finset.mem_univ l₀, hstrictl⟩

/-! ## Finite capped lossless chunks -/

def cappedChunks {α : Type} (capacity width : ℕ) (xs : List α) :
    Option (List (List α)) :=
  if xs.length ≤ capacity * width then
    some (((List.replicate capacity width).splitLengths xs).filter
      (fun chunk => !chunk.isEmpty))
  else
    none

noncomputable def floorCappedChunks {α : Type} (L r : ℝ) (width : ℕ)
    (xs : List α) : Option (List (List α)) :=
  cappedChunks ⌊L / r⌋₊ width xs

theorem length_cappedChunks_le {α : Type} {capacity width : ℕ}
    {xs : List α} {chunks : List (List α)}
    (hsuccess : cappedChunks capacity width xs = some chunks) :
    chunks.length ≤ capacity := by
  unfold cappedChunks at hsuccess
  by_cases hfit : xs.length ≤ capacity * width
  · rw [if_pos hfit] at hsuccess
    have hchunks := Option.some.inj hsuccess
    subst chunks
    simpa only [List.length_splitLengths, List.length_replicate] using
      (List.length_filter_le
        (fun chunk : List α => !chunk.isEmpty)
        ((List.replicate capacity width).splitLengths xs))
  · rw [if_neg hfit] at hsuccess
    simp at hsuccess

theorem flatten_cappedChunks {α : Type} {capacity width : ℕ}
    {xs : List α} {chunks : List (List α)}
    (hsuccess : cappedChunks capacity width xs = some chunks) :
    chunks.flatten = xs := by
  unfold cappedChunks at hsuccess
  by_cases hfit : xs.length ≤ capacity * width
  · rw [if_pos hfit] at hsuccess
    have hchunks := Option.some.inj hsuccess
    subst chunks
    rw [List.flatten_filter_not_isEmpty]
    apply List.flatten_splitLengths
    simpa only [List.sum_replicate_nat] using hfit
  · rw [if_neg hfit] at hsuccess
    simp at hsuccess

theorem ne_nil_of_mem_cappedChunks {α : Type} {capacity width : ℕ}
    {xs : List α} {chunks : List (List α)} {chunk : List α}
    (hsuccess : cappedChunks capacity width xs = some chunks)
    (hmem : chunk ∈ chunks) : chunk ≠ [] := by
  unfold cappedChunks at hsuccess
  by_cases hfit : xs.length ≤ capacity * width
  · rw [if_pos hfit] at hsuccess
    have hchunks := Option.some.inj hsuccess
    subst chunks
    have hbool : (!chunk.isEmpty) = true := (List.mem_filter.mp hmem).2
    apply List.isEmpty_eq_false_iff.mp
    cases hi : chunk.isEmpty <;> simp_all
  · rw [if_neg hfit] at hsuccess
    simp at hsuccess

theorem floorCappedChunks_length_le {α : Type} (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 < r) {width : ℕ} {xs : List α}
    {chunks : List (List α)}
    (hsuccess : floorCappedChunks L r width xs = some chunks) :
    (chunks.length : ℝ) ≤ L / r := by
  unfold floorCappedChunks at hsuccess
  have hcap : chunks.length ≤ ⌊L / r⌋₊ := length_cappedChunks_le hsuccess
  calc
    (chunks.length : ℝ) ≤ (⌊L / r⌋₊ : ℝ) := by exact_mod_cast hcap
    _ ≤ L / r := Nat.floor_le (div_nonneg hL hr.le)

theorem floorCappedChunks_flatten {α : Type} (L r : ℝ) {width : ℕ}
    {xs : List α} {chunks : List (List α)}
    (hsuccess : floorCappedChunks L r width xs = some chunks) :
    chunks.flatten = xs := by
  unfold floorCappedChunks at hsuccess
  exact flatten_cappedChunks hsuccess

theorem floorCappedChunks_cost_le_floor {α : Type} (c : k → ℝ)
    (hc : ∀ l, 0 ≤ c l) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    {width : ℕ} {xs : List α} {chunks : List (List α)}
    (hsuccess : floorCappedChunks L r width xs = some chunks) :
    adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤
      ∑ l, c l * (⌊L / r⌋₊ : ℝ) ^ 2 := by
  unfold floorCappedChunks at hsuccess
  have hcap : chunks.length ≤ ⌊L / r⌋₊ := length_cappedChunks_le hsuccess
  have hbound :
      adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤
        ∑ l, c l * ((⌊L / r⌋₊ : ℝ) / 1) ^ 2 :=
    adaptive_le_static c hc (fun _ => (chunks.length : ℝ))
      (⌊L / r⌋₊ : ℝ) 1 (Nat.cast_nonneg _) (by norm_num)
      (fun _ => Nat.cast_nonneg _) (fun _ => by
        rw [div_one]
        exact_mod_cast hcap)
  simpa only [div_one] using hbound

theorem floorCappedChunks_adaptive_le_static {α : Type} (c : k → ℝ)
    (hc : ∀ l, 0 ≤ c l) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    {width : ℕ} {xs : List α} {chunks : List (List α)}
    (hsuccess : floorCappedChunks L r width xs = some chunks) :
    adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤
      ∑ l, c l * (L / r) ^ 2 := by
  exact adaptive_le_static c hc (fun _ => (chunks.length : ℝ)) L r hL hr
    (fun _ => Nat.cast_nonneg _)
    (fun _ => floorCappedChunks_length_le L r hL hr hsuccess)

end Hagi.Model.AdaptiveChunking

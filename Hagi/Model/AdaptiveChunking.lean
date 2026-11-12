import Mathlib.Tactic
import Mathlib.Data.List.SplitLengths
import Mathlib.Data.List.SplitBy

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

-- C213_BOUNDARY_BLOCK_START
/-! ## Finite Boolean boundary-driven lossless chunks -/

/-- Split before each next token whose boundary flag is true. -/
def boundaryChunks {α : Type*} (boundary : α → Bool) (xs : List α) : List (List α) :=
  xs.splitBy (fun _ next => !boundary next)

@[simp] theorem flatten_boundaryChunks {α : Type*} (boundary : α → Bool) (xs : List α) :
    (boundaryChunks boundary xs).flatten = xs := by
  exact List.flatten_splitBy _ _

theorem ne_nil_of_mem_boundaryChunks {α : Type*} {boundary : α → Bool} {xs chunk : List α}
    (h : chunk ∈ boundaryChunks boundary xs) : chunk ≠ [] := by
  exact List.ne_nil_of_mem_splitBy h

/-- Exact count for the existing `List.splitBy.loop` under the boundary comparator. -/
private theorem boundary_split_loop_length {α : Type*} (boundary : α → Bool)
    (xs : List α) (prev : α) (current : List α) (acc : List (List α)) :
    (List.splitBy.loop (fun _ next => !boundary next) xs prev current acc).length =
      acc.length + 1 + xs.countP boundary := by
  induction xs generalizing prev current acc with
  | nil => simp [List.splitBy.loop]
  | cons next rest ih =>
    cases h : boundary next <;>
      simp [List.splitBy.loop, h, ih, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem length_boundaryChunks {α : Type*} (boundary : α → Bool) (xs : List α) :
    (boundaryChunks boundary xs).length =
      match xs with
      | [] => 0
      | _ :: tail => tail.countP boundary + 1 := by
  cases xs with
  | nil => simp [boundaryChunks, List.splitBy]
  | cons first rest => simp [boundaryChunks, List.splitBy, boundary_split_loop_length, Nat.add_comm]

/-- The exact count gives the generic upper bound without any empty-chunk caveat. -/
theorem length_boundaryChunks_le {α : Type*} (boundary : α → Bool) (xs : List α) :
    (boundaryChunks boundary xs).length ≤ xs.length := by
  rw [length_boundaryChunks]
  cases xs with
  | nil => exact Nat.zero_le _
  | cons first rest =>
    exact Nat.add_le_add_right (List.countP_le_length (p := boundary) (l := rest)) 1

/-- Return the computed boundary route exactly when its actual count fits. -/
def cappedBoundaryChunks {α : Type*} (capacity : ℕ) (boundary : α → Bool) (xs : List α) :
    Option (List (List α)) :=
  if (boundaryChunks boundary xs).length ≤ capacity then
    some (boundaryChunks boundary xs)
  else
    none

theorem cappedBoundaryChunks_eq_some_iff {α : Type*} {capacity : ℕ}
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)} :
    cappedBoundaryChunks capacity boundary xs = some chunks ↔
      chunks = boundaryChunks boundary xs ∧ chunks.length ≤ capacity := by
  unfold cappedBoundaryChunks
  by_cases hfit : (boundaryChunks boundary xs).length ≤ capacity
  · simp only [hfit, ↓reduceIte]
    constructor
    · intro hSuccess
      have hchunks := (Option.some.inj hSuccess).symm
      refine ⟨hchunks, ?_⟩
      simpa only [hchunks] using hfit
    · rintro ⟨rfl, _⟩
      rfl
  · simp only [hfit, ↓reduceIte]
    constructor
    · intro hSuccess
      simp at hSuccess
    · rintro ⟨hchunks, hlen⟩
      exfalso
      apply hfit
      simpa only [hchunks] using hlen

theorem length_cappedBoundaryChunks_le {α : Type*} {capacity : ℕ}
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)}
    (hSuccess : cappedBoundaryChunks capacity boundary xs = some chunks) :
    chunks.length ≤ capacity := by
  exact (cappedBoundaryChunks_eq_some_iff.mp hSuccess).2

theorem flatten_cappedBoundaryChunks {α : Type*} {capacity : ℕ}
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)}
    (hSuccess : cappedBoundaryChunks capacity boundary xs = some chunks) :
    chunks.flatten = xs := by
  have hchunks := (cappedBoundaryChunks_eq_some_iff.mp hSuccess).1
  rw [hchunks]
  exact flatten_boundaryChunks boundary xs

theorem ne_nil_of_mem_cappedBoundaryChunks {α : Type*} {capacity : ℕ}
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)} {chunk : List α}
    (hSuccess : cappedBoundaryChunks capacity boundary xs = some chunks)
    (hmem : chunk ∈ chunks) : chunk ≠ [] := by
  have hchunks := (cappedBoundaryChunks_eq_some_iff.mp hSuccess).1
  rw [hchunks] at hmem
  exact ne_nil_of_mem_boundaryChunks hmem

/-- Use the exact natural floor of `L / r` as the route-count capacity. -/
noncomputable def floorBoundaryChunks {α : Type*} (L r : ℝ)
    (boundary : α → Bool) (xs : List α) : Option (List (List α)) :=
  cappedBoundaryChunks ⌊L / r⌋₊ boundary xs

theorem floorBoundaryChunks_length_le {α : Type*} (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 < r) {boundary : α → Bool} {xs : List α}
    {chunks : List (List α)}
    (hSuccess : floorBoundaryChunks L r boundary xs = some chunks) :
    (chunks.length : ℝ) ≤ L / r := by
  unfold floorBoundaryChunks at hSuccess
  have hcap : chunks.length ≤ ⌊L / r⌋₊ := length_cappedBoundaryChunks_le hSuccess
  calc
    (chunks.length : ℝ) ≤ (⌊L / r⌋₊ : ℝ) := by exact_mod_cast hcap
    _ ≤ L / r := Nat.floor_le (div_nonneg hL hr.le)

theorem floorBoundaryChunks_flatten {α : Type*} (L r : ℝ)
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)}
    (hSuccess : floorBoundaryChunks L r boundary xs = some chunks) :
    chunks.flatten = xs := by
  unfold floorBoundaryChunks at hSuccess
  exact flatten_cappedBoundaryChunks hSuccess

theorem floorBoundaryChunks_adaptive_le_static {α : Type*} (c : k → ℝ)
    (hc : ∀ l, 0 ≤ c l) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)}
    (hSuccess : floorBoundaryChunks L r boundary xs = some chunks) :
    adaptiveCost c (fun _ => (chunks.length : ℝ)) ≤
      ∑ l, c l * (L / r) ^ 2 := by
  exact adaptive_le_static c hc (fun _ => (chunks.length : ℝ)) L r hL hr
    (fun _ => Nat.cast_nonneg _)
    (fun _ => floorBoundaryChunks_length_le L r hL hr hSuccess)

theorem floorBoundaryChunks_adaptive_lt_of_strict {α : Type*} (c : k → ℝ)
    (hc : ∀ l, 0 ≤ c l) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    {boundary : α → Bool} {xs : List α} {chunks : List (List α)}
    (hSuccess : floorBoundaryChunks L r boundary xs = some chunks)
    (l₀ : k) (hc₀ : 0 < c l₀)
    (hstrict : (chunks.length : ℝ) < L / r) :
    adaptiveCost c (fun _ => (chunks.length : ℝ)) <
      ∑ l, c l * (L / r) ^ 2 := by
  exact adaptive_lt_of_strict c hc (fun _ => (chunks.length : ℝ)) L r hL hr
    (fun _ => Nat.cast_nonneg _)
    (fun _ => floorBoundaryChunks_length_le L r hL hr hSuccess)
    l₀ hc₀ hstrict

-- C213_BOUNDARY_BLOCK_END
-- C214_ADJACENT_BLOCK_START
/-! ## Adjacent previous/current tags with plain-erasure projection -/

-- Proof route: reviewed A-snd probe at
-- `.tmp/C214/research/AdjacentPrefixProbe.lean`, using C213 transport.
/-- Tag each value with its predecessor; the seed is a dummy pair. -/
def adjacentPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | a :: rest => (a, a) :: (a :: rest).zip rest

/-- Second projection recovers every plain value, including the seed. -/
theorem map_snd_adjacentPairs {α : Type*} (xs : List α) :
    (adjacentPairs xs).map Prod.snd = xs := by
  cases xs with
  | nil => rfl
  | cons a rest =>
    simp only [adjacentPairs, List.map_cons]
    rw [List.map_snd_zip (by simp)]

/-- Adjacent tagging preserves the input length by plain-value reconstruction. -/
theorem length_adjacentPairs {α : Type*} (xs : List α) :
    (adjacentPairs xs).length = xs.length := by
  have h := congrArg List.length (map_snd_adjacentPairs xs)
  simpa using h

/-- Projecting every actual boundary chunk erases tags without loss. -/
theorem flatten_map_snd_adjacentBoundary {α : Type*} (θ : α × α → Bool)
    (xs : List α) :
    ((boundaryChunks θ (adjacentPairs xs)).map (List.map Prod.snd)).flatten = xs := by
  rw [← List.map_flatten, flatten_boundaryChunks, map_snd_adjacentPairs]

/-- Projection preserves the actual boundary route count. -/
theorem length_adjacentBoundary_projection {α : Type*} (θ : α × α → Bool)
    (xs : List α) :
    ((boundaryChunks θ (adjacentPairs xs)).map (List.map Prod.snd)).length =
      (boundaryChunks θ (adjacentPairs xs)).length := by
  simp only [List.length_map]

/-- Projection transfers C213's exact boundary route count. -/
theorem length_adjacentBoundary_projection_exact {α : Type*} (θ : α × α → Bool)
    (xs : List α) :
    ((boundaryChunks θ (adjacentPairs xs)).map (List.map Prod.snd)).length =
      match adjacentPairs xs with
      | [] => 0
      | _ :: tail => tail.countP θ + 1 := by
  cases xs <;> simp [adjacentPairs]

/-- Every member of the projected boundary route is nonempty. -/
theorem ne_nil_of_mem_adjacentBoundary_projection {α : Type*} {θ : α × α → Bool}
    {xs : List α} {chunk : List α}
    (hmem : chunk ∈ (boundaryChunks θ (adjacentPairs xs)).map (List.map Prod.snd)) :
    chunk ≠ [] := by
  obtain ⟨rawChunk, hraw, rfl⟩ := List.mem_map.mp hmem
  simpa using ne_nil_of_mem_boundaryChunks hraw

/-- A successful capped paired route flattens losslessly after projection. -/
theorem flatten_cappedAdjacent_projection {α : Type*} {capacity : ℕ}
    {θ : α × α → Bool} {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : cappedBoundaryChunks capacity θ (adjacentPairs xs) = some chunks) :
    (chunks.map (List.map Prod.snd)).flatten = xs := by
  have hchunks := (cappedBoundaryChunks_eq_some_iff.mp hSuccess).1
  rw [hchunks]
  exact flatten_map_snd_adjacentBoundary θ xs

/-- Projection preserves the actual successful capped route's capacity bound. -/
theorem length_cappedAdjacent_projection_le {α : Type*} {capacity : ℕ}
    {θ : α × α → Bool} {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : cappedBoundaryChunks capacity θ (adjacentPairs xs) = some chunks) :
    (chunks.map (List.map Prod.snd)).length ≤ capacity := by
  have h := length_cappedBoundaryChunks_le hSuccess
  simpa only [List.length_map] using h

/-- Every member of a successful projected capped route is nonempty. -/
theorem ne_nil_of_mem_cappedAdjacent_projection {α : Type*} {capacity : ℕ}
    {θ : α × α → Bool} {xs : List α} {chunks : List (List (α × α))}
    {chunk : List α}
    (hSuccess : cappedBoundaryChunks capacity θ (adjacentPairs xs) = some chunks)
    (hmem : chunk ∈ chunks.map (List.map Prod.snd)) : chunk ≠ [] := by
  obtain ⟨rawChunk, hraw, rfl⟩ := List.mem_map.mp hmem
  simpa using ne_nil_of_mem_cappedBoundaryChunks hSuccess hraw

/-- A successful floor-cap paired route flattens losslessly after projection. -/
theorem floorAdjacent_projection_flatten {α : Type*} (L r : ℝ)
    {θ : α × α → Bool} {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : floorBoundaryChunks L r θ (adjacentPairs xs) = some chunks) :
    (chunks.map (List.map Prod.snd)).flatten = xs := by
  unfold floorBoundaryChunks at hSuccess
  exact flatten_cappedAdjacent_projection hSuccess

/-- The projected successful floor route inherits C213's real count bound. -/
theorem floorAdjacent_projection_length_le {α : Type*} (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 < r) {θ : α × α → Bool}
    {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : floorBoundaryChunks L r θ (adjacentPairs xs) = some chunks) :
    ((chunks.map (List.map Prod.snd)).length : ℝ) ≤ L / r := by
  have h := floorBoundaryChunks_length_le L r hL hr hSuccess
  simpa only [List.length_map] using h

/-- The projected floor route count transports C213's static cost bound. -/
theorem floorAdjacent_projection_adaptive_le_static
    {α k : Type*} [Fintype k] (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r) {θ : α × α → Bool}
    {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : floorBoundaryChunks L r θ (adjacentPairs xs) = some chunks) :
    adaptiveCost c (fun _ => ((chunks.map (List.map Prod.snd)).length : ℝ)) ≤
      ∑ l, c l * (L / r) ^ 2 := by
  have h := floorBoundaryChunks_adaptive_le_static c hc L r hL hr hSuccess
  simpa only [List.length_map] using h

/-- Strictness at the selected positive-price level transports unchanged. -/
theorem floorAdjacent_projection_adaptive_lt_of_strict
    {α k : Type*} [Fintype k] (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r) {θ : α × α → Bool}
    {xs : List α} {chunks : List (List (α × α))}
    (hSuccess : floorBoundaryChunks L r θ (adjacentPairs xs) = some chunks)
    (l₀ : k) (hc₀ : 0 < c l₀)
    (hstrict : ((chunks.map (List.map Prod.snd)).length : ℝ) < L / r) :
    adaptiveCost c (fun _ => ((chunks.map (List.map Prod.snd)).length : ℝ)) <
      ∑ l, c l * (L / r) ^ 2 := by
  have hstrictRaw : (chunks.length : ℝ) < L / r := by
    simpa only [List.length_map] using hstrict
  have h := floorBoundaryChunks_adaptive_lt_of_strict c hc L r hL hr hSuccess
    l₀ hc₀ hstrictRaw
  simpa only [List.length_map] using h

/-- Every member of a successful projected floor route is nonempty. -/
theorem ne_nil_of_mem_floorAdjacent_projection {α : Type*} (L r : ℝ)
    {θ : α × α → Bool} {xs : List α} {chunks : List (List (α × α))}
    {chunk : List α}
    (hSuccess : floorBoundaryChunks L r θ (adjacentPairs xs) = some chunks)
    (hmem : chunk ∈ chunks.map (List.map Prod.snd)) : chunk ≠ [] := by
  unfold floorBoundaryChunks at hSuccess
  obtain ⟨rawChunk, hraw, rfl⟩ := List.mem_map.mp hmem
  simpa using ne_nil_of_mem_cappedBoundaryChunks hSuccess hraw
-- C214_ADJACENT_BLOCK_END
end Hagi.Model.AdaptiveChunking

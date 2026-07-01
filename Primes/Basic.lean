import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace PrimeGaps

/-! ## List utilities

Genuinely missing from Mathlib: `getLastD_mem_of_ne_nil` and `getLastD_is_max_of_pairwise_le`.
The latter uses Mathlib's `Pairwise.rel_getLast`.
-/

/-- У непустого списка значение `getLastD` действительно является его элементом. -/
theorem List.getLastD_mem_of_ne_nil {α : Type} [Inhabited α] (xs : List α) (hxs : xs ≠ []) :
    xs.getLastD default ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest => simp [List.getLastD]

/-! ## Prime enumeration -/

/-- Простые числа от `2` до `n` (чисто функциональное определение). -/
def primesUpTo (n : Nat) : Array Nat :=
  Array.mk (List.filter Nat.Prime (List.range' 2 (n + 1 - 2)))

/-- `primesUpTo n` contains exactly the primes ≤ n in increasing order. -/
theorem primesUpTo_spec (n p : Nat) :
    p ∈ (primesUpTo n).toList ↔ Nat.Prime p ∧ p ≤ n := by
  unfold primesUpTo
  simp only
  constructor
  · intro h
    simp only [List.mem_filter] at h
    rcases h with ⟨hmem, hprime_dec⟩
    have hprime : Nat.Prime p := by simpa [decide_eq_true_eq] using hprime_dec
    rcases (List.mem_range'.mp hmem) with ⟨i, _, rfl⟩
    exact ⟨hprime, by omega⟩
  · intro ⟨hprime, hle⟩
    have hge : 2 ≤ p := hprime.two_le
    simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, hprime⟩
    simp only [List.mem_range']
    exact ⟨p - 2, by omega, by omega⟩

/-- `primesUpTo n` is strictly increasing. -/
theorem primesUpTo_sorted (n : Nat) : (primesUpTo n).toList.Pairwise (· < ·) := by
  unfold primesUpTo
  apply List.Pairwise.filter (p := fun x => Nat.Prime x) (l := List.range' 2 (n + 1 - 2))
  exact (List.sortedLT_range' 2 (n + 1 - 2) (s := 1) (by omega)).pairwise

/-- Размер `primesUpTo n` равен числу простых ≤ n. -/
lemma primesUpTo_size_eq_count (n : Nat) :
    (primesUpTo n).size = Nat.count Nat.Prime (n + 1) := by
  simp only [primesUpTo, Nat.count, List.countP_eq_length_filter]
  cases n with
  | zero => simp [List.range'_zero, List.range_succ, decide_eq_false Nat.not_prime_zero]
  | succ n =>
    cases n with
    | zero => simp [List.range'_zero, List.range_succ, decide_eq_false Nat.not_prime_zero,
                    decide_eq_false Nat.not_prime_one]
    | succ m =>
      have h : List.range (m + 3) = List.range 2 ++ List.range' 2 (m + 1) := by
        rw [show m + 3 = 2 + (m + 1) by omega, List.range_add, List.range'_eq_map_range]
      rw [h]
      simp [List.range_succ, decide_eq_false Nat.not_prime_zero,
            decide_eq_false Nat.not_prime_one]

/-- Первый элемент `primesUpTo n` равен 2, если n ≥ 2. -/
lemma primesUpTo_head_eq_2 (n : Nat) (hn : 2 ≤ n) :
    (primesUpTo n).toList.headD 0 = 2 := by
  rw [primesUpTo]
  have h : (Array.mk (List.filter Nat.Prime (List.range' 2 (n + 1 - 2)))).toList
           = List.filter Nat.Prime (List.range' 2 (n + 1 - 2)) := rfl
  rw [h]
  have hrange : List.range' 2 (n + 1 - 2) = 2 :: List.range' 3 (n - 2) := by
    rw [show n + 1 - 2 = (n - 2) + 1 by omega, List.range'_succ]
  rw [hrange]; simp [Nat.prime_two]

/-- Последний элемент `primesUpTo n` равен n, если n простое. -/
lemma primesUpTo_last_eq_n (n : Nat) (hn : Nat.Prime n) :
    (primesUpTo n).toList.getLastD 0 = n := by
  have hn2 : 2 ≤ n := Nat.Prime.two_le hn
  rw [primesUpTo]
  have h : (Array.mk (List.filter Nat.Prime (List.range' 2 (n + 1 - 2)))).toList
           = List.filter Nat.Prime (List.range' 2 (n + 1 - 2)) := rfl
  rw [h]
  have hrange : List.range' 2 (n + 1 - 2) = List.range' 2 (n - 2) ++ [n] := by
    rw [show n + 1 - 2 = (n - 2) + 1 by omega, List.range'_1_concat]; simp; omega
  rw [hrange, List.filter_append]; simp [decide_eq_true hn]

/-! ## Gap list -/

/-- Промежутки между соседними точками. -/
def pointGapsList (points : List Nat) : List Nat :=
  match points with
  | [] | [_] => []
  | a :: b :: rest => (b - a) :: pointGapsList (b :: rest)

/-- Сумма промежутков вместе с первой точкой равна последней точке. -/
theorem pointGapsList_sum_eq_last :
    ∀ points : List Nat, points.Pairwise (· <= ·) ->
      (pointGapsList points).sum + points.headD 0 = points.getLastD 0 := by
  intro points hmono
  induction points with
  | nil => simp [pointGapsList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [pointGapsList]
      | cons b tail =>
          have hab : a <= b := (List.pairwise_cons.mp hmono).1 b (by simp)
          have htail_sum := ih (List.pairwise_cons.mp hmono).2
          simp [pointGapsList] at htail_sum ⊢; omega

/-- Длина списка внутренних промежутков равна числу точек минус один. -/
theorem pointGapsList_length (points : List Nat) :
    (pointGapsList points).length = points.length - 1 := by
  induction points with
  | nil => simp [pointGapsList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [pointGapsList]
      | cons b tail => simp [pointGapsList, ih]

/-! ## Gap frequency distribution -/

/-- Добавляет промежуток в таблицу частот. -/
def addGapCount (counts : List (Nat × Nat)) (g : Nat) : List (Nat × Nat) :=
  match counts with
  | [] => [(g, 1)]
  | (a, b) :: rest =>
      if a == g then (a, b + 1) :: rest
      else (a, b) :: addGapCount rest g

/-- Добавляет sentinel `(0, 0)` в начало таблицы частот. -/
def gapCountsWithSentinel (counts : List (Nat × Nat)) : List (Nat × Nat) :=
  (0, 0) :: counts

/-- Вспомогательная: распределение промежутков по списку простых чисел. -/
noncomputable def gapDistributionFromPrimes (primes : List Nat) : List (Nat × Nat) :=
  let counts :=
    primes.foldl (fun (counts, prev) p => (addGapCount counts (p - prev), p)) ([], 1) |>.1
  gapCountsWithSentinel counts

/-- Распределение промежутков для первых `k` простых чисел. -/
noncomputable def gapDistributionByCount (k : Nat) : List (Nat × Nat) :=
  if k == 0 then [(0, 0)]
  else
    gapDistributionFromPrimes (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList

/-- k-е простое число через частоты промежутков. -/
noncomputable def nthPrimeByGapFrequencies (k : Nat) : Nat :=
  1 + ((gapDistributionByCount (k + 1)).map (fun entry => entry.1 * entry.2)).sum

/-! ## Gap frequency lemmas -/

/-- `addGapCount` увеличивает сумму частот на 1. -/
lemma addGapCount_sum_succ (counts : List (Nat × Nat)) (g : Nat) :
    ((addGapCount counts g).map Prod.snd).sum =
    (counts.map Prod.snd).sum + 1 := by
  induction counts with
  | nil => simp [addGapCount]
  | cons head tail ih =>
      cases head with
      | mk a b =>
        simp [addGapCount]
        split_ifs with h <;> simp [h, ih] <;> omega

/-- `gapCountsWithSentinel` сохраняет сумму частот. -/
lemma gapCountsWithSentinel_sum_eq (counts : List (Nat × Nat)) :
    ((gapCountsWithSentinel counts).map Prod.snd).sum =
    (counts.map Prod.snd).sum := by simp [gapCountsWithSentinel]

/-- `addGapCount` увеличивает взвешенную сумму на g. -/
lemma addGapCount_weighted_sum (counts : List (Nat × Nat)) (g : Nat) :
    ((addGapCount counts g).map (fun entry => entry.1 * entry.2)).sum =
    (counts.map (fun entry => entry.1 * entry.2)).sum + g := by
  induction counts with
  | nil => simp [addGapCount]
  | cons head tail ih =>
      cases head with
      | mk a b =>
        simp [addGapCount]
        split_ifs with h <;> simp [h, ih] <;> ring_nf

/-- `primesUpTo` для k-го простого содержит ровно k простых. -/
lemma primesUpTo_nth_prime_size (k : Nat) (hk : 0 < k) :
    (primesUpTo (Nat.nth Nat.Prime (k - 1))).size = k := by
  rw [primesUpTo_size_eq_count]
  have h := Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at h; exact h

/-! ## Gap distribution: sum and weighted sum -/

set_option maxHeartbeats 0 in
-- Proof requires unbounded heartbeats for nested foldl induction on prime lists
set_option linter.flexible false in
/-- Sum of frequencies in gapDistributionByCount equals k (for k > 0). -/
theorem gapDistributionByCount_sum_eq_k {k : Nat} (hk : 0 < k) :
    List.sum ((gapDistributionByCount k).map Prod.snd) = k := by
  unfold gapDistributionByCount
  have hk_ne_zero : k ≠ 0 := by omega
  simp [hk_ne_zero, gapDistributionFromPrimes]
  have h_primes_count := primesUpTo_nth_prime_size k hk
  have h_size : (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList.length = k := by
    have h1 : (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList.length =
        (primesUpTo (Nat.nth Nat.Prime (k - 1))).size := by simp
    rw [h1, h_primes_count]
  have h_foldl_sum :
      ∀ (counts : List (Nat × Nat)) (prev : Nat) (xs : List Nat),
        ((xs.foldl
          (fun (c : List (Nat × Nat) × Nat) x =>
            (addGapCount c.1 (x - c.2), x))
          (counts, prev)).1.map Prod.snd).sum =
        (counts.map Prod.snd).sum + xs.length := by
    intro counts prev xs
    induction xs generalizing counts prev with
    | nil => simp
    | cons y ys ih =>
        rw [show (y :: ys).foldl _ (counts, prev) =
          ys.foldl _ (addGapCount counts (y - prev), y) from rfl]
        have := ih (addGapCount counts (y - prev)) y
        simp [addGapCount_sum_succ] at this ⊢; omega
  have h_nil : ([] : List (Nat × Nat)).map Prod.snd = [] := by simp
  have h_sum_nil : ([] : List Nat).sum = 0 := by simp
  specialize h_foldl_sum [] 1 (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList
  simp [h_nil, h_sum_nil, h_size] at h_foldl_sum ⊢
  rw [gapCountsWithSentinel_sum_eq]
  exact h_foldl_sum

/-- Взвешенная сумма foldl `addGapCount` на списке простых
    равна сумме gaps плюс начальная взвешенная сумма. -/
lemma foldl_weightedSum_eq_pointGapsSum
    (counts : List (Nat × Nat)) (prev : Nat) (primes : List Nat) :
    let result :=
    primes.foldl
      (fun (c : List (Nat × Nat) × Nat) p => (addGapCount c.1 (p - c.2), p))
      (counts, prev)
    ((result.1).map (fun e => e.1 * e.2)).sum =
      (counts.map (fun e => e.1 * e.2)).sum +
      (pointGapsList (prev :: primes)).sum := by
  induction primes generalizing counts prev with
  | nil => simp [pointGapsList]
  | cons p ps ih =>
      rw [show (p :: ps).foldl _ (counts, prev) =
        ps.foldl _ (addGapCount counts (p - prev), p) from rfl]
      have ih_spec := ih (addGapCount counts (p - prev)) p
      simp only [addGapCount_weighted_sum] at ih_spec ⊢
      rw [ih_spec]; simp [pointGapsList]; ring_nf

/-- Сумма `gap * frequency` по распределению промежутков равна последнему простому. -/
lemma gapDistributionByCount_weighted_sum_eq_last (k : Nat) (hk : 0 < k) :
    1 + ((gapDistributionByCount k).map (fun entry => entry.1 * entry.2)).sum =
      Nat.nth Nat.Prime (k - 1) := by
  rw [gapDistributionByCount]
  split_ifs with h
  · exfalso; simp at h; omega
  let primes := (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList
  have hnonempty : primes ≠ [] := by
    have hsize : (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList.length > 0 := by
      have h_eq : (primesUpTo (Nat.nth Nat.Prime (k - 1))).size = k :=
        primesUpTo_nth_prime_size k hk
      have : (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList.length =
        (primesUpTo (Nat.nth Nat.Prime (k - 1))).size := by simp
      rw [this, h_eq]; omega
    exact List.ne_nil_of_length_pos hsize
  have hsorted : primes.Pairwise (· < ·) := by
    rw [show primes = (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList by rfl]
    exact primesUpTo_sorted _
  have hpairwise : (1 :: primes).Pairwise (· < ·) := by
    rw [List.pairwise_cons]
    constructor
    · intro a ha
      have h1 : Nat.Prime a ∧ a ≤ Nat.nth Nat.Prime (k - 1) := by
        rw [show primes = (primesUpTo (Nat.nth Nat.Prime (k - 1))).toList by rfl] at ha
        exact (primesUpTo_spec _ _).mp ha
      have h2 : 2 ≤ a := Nat.Prime.two_le h1.1
      omega
    · exact hsorted
  have hpairwise_le : (1 :: primes).Pairwise (· ≤ ·) := by
    have h1 : ∀ a ∈ primes, 1 ≤ a := by
      intro a ha
      have hlt := (List.pairwise_cons.mp hpairwise).1 a ha
      exact Nat.le_of_lt hlt
    have h2 : primes.Pairwise (· ≤ ·) := hsorted.imp fun hlt => Nat.le_of_lt hlt
    rw [List.pairwise_cons]
    exact ⟨h1, h2⟩
  have hlast : (1 :: primes).getLastD 0 = Nat.nth Nat.Prime (k - 1) := by
    have hget : (1 :: primes).getLastD 0 = primes.getLastD 0 := by
      cases hpr : primes with
      | nil => exfalso; exact hnonempty (by simp [hpr])
      | cons p ps => simp [List.getLastD]
    rw [hget]
    rw [primesUpTo_last_eq_n (Nat.nth Nat.Prime (k - 1)) (Nat.prime_nth_prime (k - 1))]
  have hsum : ((gapDistributionFromPrimes primes).map (fun entry => entry.1 * entry.2)).sum
      = (pointGapsList (1 :: primes)).sum := by
    simp [gapDistributionFromPrimes, gapCountsWithSentinel]
    have h := foldl_weightedSum_eq_pointGapsSum [] 1 primes
    simp at h ⊢; linarith
  have htelescoping :
    (pointGapsList (1 :: primes)).sum + (1 :: primes).headD 0 =
      (1 :: primes).getLastD 0 := pointGapsList_sum_eq_last _ hpairwise_le
  have hhead1 : (1 :: primes).headD 0 = 1 := by simp
  rw [← hsum, hhead1] at htelescoping
  linarith [htelescoping, hlast]

/-- `nthPrimeByGapFrequencies` корректно вычисляет k-е простое число. -/
theorem nthPrimeByGapFrequencies_correct (k : Nat) :
    nthPrimeByGapFrequencies k = Nat.nth Nat.Prime k := by
  rw [nthPrimeByGapFrequencies,
      gapDistributionByCount_weighted_sum_eq_last (k + 1) (by omega),
      show k + 1 - 1 = k by omega]

/-- В отсортированном непустом списке каждый элемент ≤ последнего. -/
theorem List.getLastD_is_max_of_pairwise_le {l : List Nat} (hsorted : l.Pairwise (· ≤ ·))
    (_hnonempty : l ≠ []) : ∀ x ∈ l, x ≤ l.getLastD 0 := by
  intro x hx
  have hle := hsorted.rel_getLast hx
  have hgetLastD : l.getLastD 0 = l.getLast (List.ne_nil_of_mem hx) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil (List.ne_nil_of_mem hx),
        Option.getD_some]
  rw [hgetLastD]
  exact hle

end PrimeGaps

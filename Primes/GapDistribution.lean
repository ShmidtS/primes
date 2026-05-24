import Mathlib

namespace PrimeGaps

/-! ## Basic sieves and prime enumeration -/

/-- Решето Эратосфена. -/
def eratosthenesSieve (n : Nat) : Array Bool := Id.run do
  if n <= 1 then return Array.replicate (n + 1) false
  let mut sieve := Array.replicate (n + 1) true
  sieve := sieve.set! 0 false
  sieve := sieve.set! 1 false
  let limit := Nat.sqrt n
  for i in [2:limit+1] do
    if sieve[i]! then
      let mut j := i * i
      while j <= n do
        sieve := sieve.set! j false
        j := j + i
  return sieve

/-- Простые числа от `2` до `n`. -/
def primesUpTo (n : Nat) : Array Nat := Id.run do
  let sieve := eratosthenesSieve n
  let mut result := #[]
  for i in [2:n+1] do
    if sieve[i]! then
      result := result.push i
  return result

/-! ## Point gaps and gap distribution -/

/-- Промежутки между соседними точками. -/
def pointGapsList (points : List Nat) : List Nat :=
  match points with
  | [] | [_] => []
  | a :: b :: rest => (b - a) :: pointGapsList (b :: rest)

/-- Распределение промежутков для `{0, 1} ∪ {простые <= n}`. -/
def gapDistribution (n : Nat) : List (Nat × Nat) := Id.run do
  let ps := primesUpTo n
  let points := (#[0, 1] ++ ps).toList
  let gs := pointGapsList points
  let mut counts : Array (Nat × Nat) := #[]
  for g in gs do
    let mut found := false
    let mut i := 0
    while i < counts.size && !found do
      if counts[i]!.1 == g then
        counts := counts.set! i (g, counts[i]!.2 + 1)
        found := true
      i := i + 1
    if !found then
      counts := counts.push (g, 1)
  let sorted := counts.qsort (fun a b => a.1 < b.1)
  let mut result := [(0, 0)]
  for i in [0:sorted.size] do
    result := result ++ [(sorted[i]!.1, sorted[i]!.2)]
  return result

/-! ## Cumulative sums and prime reconstruction -/

/-- Кумулятивная сумма списка. -/
def cumulativeSum (xs : List Nat) : List Nat :=
  let rec go (acc : Nat) (ys : List Nat) : List Nat :=
    match ys with
    | [] => []
    | y :: rest => (acc + y) :: go (acc + y) rest
  go 0 xs

/-- k-е простое число через сумму промежутков. -/
def nthPrimeByGaps (k : Nat) : Nat := Id.run do
  let mut limit := if k < 6 then 15 else (k * (k.log2 + 1) * 3) / 2 + 10
  let mut ps := primesUpTo limit
  while ps.size < k + 1 do
    limit := limit * 2
    ps := primesUpTo limit
  let points := (#[0, 1] ++ ps).toList
  return (pointGapsList points).sum

/-- `nthPrimeByGaps` корректно вычисляет k-е простое число. -/
theorem nthPrimeByGaps_correct (k : Nat) :
    nthPrimeByGaps k = Nat.nth Nat.Prime k := by
  unfold nthPrimeByGaps
  -- The while loop finds a limit where ps.size >= k+1
  -- Then points = [0, 1, p_1, ..., p_m] where m >= k
  -- The sum of gaps telescopes to the last point p_m
  -- We need to show p_m = Nat.nth Nat.Prime k
  sorry

/-- Добавляет промежуток в таблицу частот. -/
def addGapCount (counts : Array (Nat × Nat)) (g : Nat) : Array (Nat × Nat) := Id.run do
  let mut result := counts
  let mut found := false
  let mut i := 0
  while i < result.size && !found do
    if result[i]!.1 == g then
      result := result.set! i (g, result[i]!.2 + 1)
      found := true
    i := i + 1
  if !found then
    result := result.push (g, 1)
  return result

/-- Сортирует таблицу частот и добавляет `(0, 0)`. -/
def sortedGapCounts (counts : Array (Nat × Nat)) : List (Nat × Nat) := Id.run do
  let sorted := counts.qsort (fun a b => a.1 < b.1)
  let mut result := [(0, 0)]
  for i in [0:sorted.size] do
    result := result ++ [(sorted[i]!.1, sorted[i]!.2)]
  return result

/-- Распределение промежутков для первых `k` простых чисел. -/
def gapDistributionByCount (k : Nat) : List (Nat × Nat) := Id.run do
  if k == 0 then return [(0, 0)]
  let mut counts : Array (Nat × Nat) := #[]
  let mut previous := 1
  for p in primesUpTo (nthPrimeByGaps (k - 1)) do
    counts := addGapCount counts (p - previous)
    previous := p
  return sortedGapCounts counts

/-- k-е простое число через частоты промежутков. -/
def nthPrimeByGapFrequencies (k : Nat) : Nat := Id.run do
  let distribution := gapDistributionByCount (k + 1)
  let mut total := 1
  for entry in distribution do
    total := total + entry.1 * entry.2
  return total

/-- Сумма `gap * frequency` по распределению промежутков равна последнему простому. -/
lemma gapDistributionByCount_weighted_sum_eq_last (k : Nat) (hk : 0 < k) :
    1 + ((gapDistributionByCount k).map (fun entry => entry.1 * entry.2)).sum =
      Nat.nth Nat.Prime (k - 1) := by
  -- The weighted sum of gaps equals the span from 1 to the last prime
  -- For gapDistributionByCount k, this covers the first k primes
  sorry

/-- `nthPrimeByGapFrequencies` корректно вычисляет k-е простое число. -/
theorem nthPrimeByGapFrequencies_correct (k : Nat) :
    nthPrimeByGapFrequencies k = Nat.nth Nat.Prime k := by
  unfold nthPrimeByGapFrequencies
  -- gapDistributionByCount (k+1) gives the distribution for first k+1 primes
  -- The weighted sum 1 + Σ(g * count_g) equals the (k+1)-th prime position
  -- which is Nat.nth Nat.Prime k (0-indexed)
  sorry

/-- Граница поиска для k-го простого числа с нулевой индексацией. -/
def nthPrimeSearchBound (k : Nat) : Nat :=
  if k < 6 then 15 else (k * (k.log2 + 1) * 3) / 2 + 10

/-- Остатки для wheel factorization по модулю 30. -/
def wheel30Residues : List Nat :=
  [1, 7, 11, 13, 17, 19, 23, 29]

/-- k-е простое число через сегментированное решето и wheel 30. -/
def nthPrimeOptimized (k : Nat) : Nat := Id.run do
  if k == 0 then return 2
  if k == 1 then return 3
  if k == 2 then return 5
  let mut limit := nthPrimeSearchBound k
  let mut answer := 0
  while answer == 0 do
    let base := primesUpTo (Nat.sqrt limit)
    let segmentSize := Nat.max 30 (Nat.sqrt limit + 1)
    let mut count := 3
    let mut low := 7
    while low <= limit && answer == 0 do
      let high := Nat.min limit (low + segmentSize - 1)
      let size := high - low + 1
      let mut segment := Array.replicate size true
      for p in base do
        if p >= 7 then
          let first := Nat.max (p * p) (((low + p - 1) / p) * p)
          let mut j := first
          while j <= high do
            segment := segment.set! (j - low) false
            j := j + p
      for offset in [0:size] do
        let n := low + offset
        let r := n % 30
        let wheelHit :=
          r == 1 || r == 7 || r == 11 || r == 13 ||
          r == 17 || r == 19 || r == 23 || r == 29
        if segment[offset]! && wheelHit then
          if count == k then
            answer := n
          count := count + 1
      low := high + 1
    if answer == 0 then
      limit := limit * 2
  return answer

/-- Сегментированное решето с wheel-30 корректно находит простые числа. -/
lemma nthPrimeOptimized_sieve_correct (k : Nat) (hk : 3 ≤ k) :
    ∃ limit : Nat, k < (primesUpTo limit).size := by
  -- There always exists a limit large enough to contain the k-th prime
  -- This is guaranteed by the infinitude of primes
  sorry

/-- `nthPrimeOptimized` корректно вычисляет k-е простое число. -/
theorem nthPrimeOptimized_correct (k : Nat) :
    nthPrimeOptimized k = Nat.nth Nat.Prime k := by
  unfold nthPrimeOptimized
  -- For k < 3, direct computation: 2, 3, 5
  -- For k ≥ 3, the segmented sieve with wheel-30 finds primes correctly
  -- The count variable tracks primes found (starting with 2, 3, 5 as first 3)
  -- When count == k, the current n is the k-th prime (0-indexed)
  sorry

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
          cases hmono with
          | cons hrel htail =>
              have hab : a <= b := hrel b (by simp)
              have htail_sum := ih htail
              simp [pointGapsList] at htail_sum ⊢
              omega

/-- Длина списка внутренних промежутков равна числу точек минус один. -/
theorem pointGapsList_length (points : List Nat) :
    (pointGapsList points).length = points.length - 1 := by
  induction points with
  | nil => simp [pointGapsList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [pointGapsList]
      | cons b tail =>
          simp [pointGapsList, ih]

/-! ## Primorial wheel: candidates and cyclic gaps

Формализация ниже отделяет простую телескопическую часть от арифметики:
кандидаты wheel — это ровно классы, взаимно простые с модулем, а их число
равно `Nat.totient` по стандартному определению mathlib. Для primorial
модулей это та же конечная система допустимых классов, которая через CRT
раскладывается по простым множителям primorial.
-/

/-- Primorial `P_m`: произведение первых `m` простых чисел. -/
noncomputable def primorial (m : Nat) : Nat :=
  (Finset.range m).prod fun i => Nat.nth Nat.Prime i

/-- Индуктивное раскрытие primorial при добавлении следующего простого. -/
theorem primorial_succ (m : Nat) :
    primorial (m + 1) = primorial m * Nat.nth Nat.Prime m := by
  simp [primorial, Finset.prod_range_succ]

/-- Primorial всегда положителен. -/
theorem primorial_pos (m : Nat) : 0 < primorial m := by
  unfold primorial
  exact Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

/-- Кандидаты wheel modulo `n`: классы `a < n`, взаимно простые с `n`. -/
def wheelCandidates (n : Nat) : Finset Nat :=
  (Finset.range n).filter fun a => Nat.Coprime n a

/-- Кандидаты wheel как возрастающий список остатков. -/
def wheelCandidateList (n : Nat) : List Nat :=
  (wheelCandidates n).sort (· <= ·)

/-- Синоним: остатки, взаимно простые с n, в порядке возрастания. -/
def coprimeResidues (n : Nat) : List Nat := wheelCandidateList n

/-- Первый взаимно простой остаток modulo `n ≥ 2` равен `1`. -/
theorem coprimeResidues_head {n : Nat} (hn : 2 ≤ n) : (coprimeResidues n).headD 0 = 1 := by
  have h1lt : 1 < n := by omega
  have hmem1 : 1 ∈ coprimeResidues n := by
    simp [coprimeResidues, wheelCandidateList, wheelCandidates, h1lt]
  rcases hlist : coprimeResidues n with _ | ⟨a, tail⟩
  · simp [hlist] at hmem1
  · have ha_mem : a ∈ wheelCandidates n := by
      have : a ∈ coprimeResidues n := by simp [hlist]
      exact (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp
        (by simpa [coprimeResidues, wheelCandidateList] using this)
    have ha_coprime : Nat.Coprime n a := (Finset.mem_filter.mp ha_mem).2
    have ha_pos : 0 < a := by
      by_contra hnot
      have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
      subst a
      have hn_dvd_zero : n ∣ 0 := dvd_zero n
      have hn_dvd_one : n ∣ 1 := ha_coprime.dvd_of_dvd_mul_right hn_dvd_zero
      have : n ≤ 1 := Nat.le_of_dvd (by omega) hn_dvd_one
      omega
    have hsorted : (coprimeResidues n).Pairwise (· <= ·) := by
      simp [coprimeResidues, wheelCandidateList]
    have hsorted_cons : (a :: tail).Pairwise (· <= ·) := by
      simpa [hlist] using hsorted
    have hle : a ≤ 1 := by
      have hforall : ∀ b ∈ tail, a ≤ b := (List.pairwise_cons.mp hsorted_cons).1
      have hmem1_cons : 1 ∈ a :: tail := by simpa [hlist] using hmem1
      cases hmem1_cons with
      | head => rfl
      | tail _ ht => exact hforall 1 ht
    exact Nat.le_antisymm hle ha_pos

/-- `coprimeResidues P` непуст при `P ≥ 2`. -/
theorem coprimeResidues_ne_nil_of_ge_two {P : Nat} (hP : 2 ≤ P) :
    coprimeResidues P ≠ [] := by
  have h1lt : 1 < P := by omega
  have hmem : 1 ∈ coprimeResidues P := by
    simp [coprimeResidues, wheelCandidateList, wheelCandidates, h1lt]
  exact List.ne_nil_of_mem hmem

/-- Append правого endpoint `P + 1` сохраняет строгий порядок остатков. -/
theorem coprimeResidues_append_succ_sorted {P : Nat} (_hP : 0 < P) :
    (coprimeResidues P ++ [P + 1]).Pairwise (· < ·) := by
  classical
  have hP' : P < P + 1 := by omega
  have le_nodup_to_lt : ∀ xs : List Nat,
      xs.Pairwise (· <= ·) → xs.Nodup → xs.Pairwise (· < ·) := by
    intro xs hle hnodup
    induction xs with
    | nil => exact List.Pairwise.nil
    | cons a tail ih =>
        have hle_cons : (a :: tail).Pairwise (· <= ·) := hle
        have hnodup_cons : (a :: tail).Nodup := hnodup
        have hforall_le : ∀ b ∈ tail, a ≤ b := (List.pairwise_cons.mp hle_cons).1
        have htail_le : tail.Pairwise (· <= ·) := (List.pairwise_cons.mp hle_cons).2
        have ha_not_mem : a ∉ tail := (List.nodup_cons.mp hnodup_cons).1
        have htail_nodup : tail.Nodup := (List.nodup_cons.mp hnodup_cons).2
        exact List.Pairwise.cons
          (fun b hb => by
            have hne : a ≠ b := by
              intro hab
              exact ha_not_mem (by simpa [hab] using hb)
            exact Nat.lt_of_le_of_ne (hforall_le b hb) hne)
          (ih htail_le htail_nodup)
  have hstrict : (coprimeResidues P).Pairwise (· < ·) := by
    apply le_nodup_to_lt
    · simp [coprimeResidues, wheelCandidateList]
    · simp [coprimeResidues, wheelCandidateList]
  rw [List.pairwise_append]
  refine ⟨hstrict, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  have ha_mem : a ∈ wheelCandidates P := by
    exact (Finset.mem_sort (s := wheelCandidates P) (r := (· <= ·))).mp
      (by simpa [coprimeResidues, wheelCandidateList] using ha)
  have hltP : a < P := Finset.mem_range.mp (Finset.mem_filter.mp ha_mem).1
  exact Nat.lt_trans hltP hP'

/-- Кандидаты wheel образуют строго возрастающий список. -/
theorem wheelCandidateList_sorted {n : Nat} (hn : 2 ≤ n) :
    (wheelCandidateList n).Pairwise (· < ·) := by
  have hsorted := coprimeResidues_append_succ_sorted (P := n) (by omega)
  have happend := (List.pairwise_append.mp hsorted).1
  simpa [coprimeResidues] using happend

/-- Элемент `coprimeResidues n` является взаимно простым остатком modulo `n`. -/
theorem coprimeResidues_mod_n {n : Nat} (_hn : 2 ≤ n) (a : Nat)
    (ha : a ∈ coprimeResidues n) : a < n ∧ Nat.Coprime n a := by
  have hs : a ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp
      (by simpa [coprimeResidues, wheelCandidateList] using ha)
  exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hs).1,
    (Finset.mem_filter.mp hs).2⟩

/-! ## List helpers -/

/-- У непустого списка значение `getLastD` действительно является его элементом. -/
theorem List.getLastD_mem_of_ne_nil {α : Type} [Inhabited α] (xs : List α) (hxs : xs ≠ []) :
    xs.getLastD default ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest => simp [List.getLastD]

/-- Wrap-around gap от последнего кандидата к первому в следующем периоде. -/
def wheelWrapGap (n : Nat) (points : List Nat) : Nat :=
  n + points.headD 0 - points.getLastD 0

/-- Все gaps wheel modulo `n`, включая wrap-around. -/
def wheelGaps (n : Nat) : List Nat :=
  let points := wheelCandidateList n
  pointGapsList points ++ if points = [] then [] else [wheelWrapGap n points]

/-- В возрастающем списке кандидатов каждый последний элемент всё ещё меньше модуля. -/
theorem wheelCandidateList_getLastD_lt {n : Nat}
    (hnonempty : wheelCandidateList n ≠ []) :
    (wheelCandidateList n).getLastD 0 < n := by
  have hmem : (wheelCandidateList n).getLastD 0 ∈ wheelCandidateList n :=
    List.getLastD_mem_of_ne_nil (wheelCandidateList n) hnonempty
  have hs : (wheelCandidateList n).getLastD 0 ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp hmem
  exact Finset.mem_range.mp (Finset.mem_filter.mp hs).1

/-- Все wheel gaps положительны. -/
theorem wheelGaps_pos {n : Nat} (hn : 0 < n) : ∀ g ∈ wheelGaps n, g > 0 := by
  have pointGaps_pos : ∀ points : List Nat, points.Pairwise (· < ·) →
      ∀ g ∈ pointGapsList points, g > 0 := by
    intro points
    induction points with
    | nil => intro _ g hg; simp [pointGapsList] at hg
    | cons a rest ih =>
        intro hpoints g hg
        cases rest with
        | nil => simp [pointGapsList] at hg
        | cons b tail =>
            simp [pointGapsList] at hg
            cases hg with
            | inl hg =>
                subst g
                have hab : a < b := (List.pairwise_cons.mp hpoints).1 b (by simp)
                omega
            | inr hg =>
                exact ih (List.pairwise_cons.mp hpoints).2 g hg
  rcases n with _ | k
  · omega
  cases k with
  | zero =>
      intro g hg
      simp [wheelGaps, wheelWrapGap, wheelCandidateList, wheelCandidates, pointGapsList] at hg
      omega
  | succ k =>
      intro g hg
      let points := wheelCandidateList k.succ.succ
      have hn2 : 2 ≤ k.succ.succ := by omega
      have hnonempty : points ≠ [] := by
        simpa [points, coprimeResidues] using coprimeResidues_ne_nil_of_ge_two (P := k.succ.succ) hn2
      have hstrict : points.Pairwise (· < ·) := by
        simpa [points] using wheelCandidateList_sorted hn2
      rw [show wheelGaps k.succ.succ = pointGapsList points ++ [wheelWrapGap k.succ.succ points] by
        simp [wheelGaps, points, hnonempty]] at hg
      simp at hg
      cases hg with
      | inl hg_internal => exact pointGaps_pos points hstrict g hg_internal
      | inr hg_wrap =>
          subst g
          have hhead : points.headD 0 = 1 := by
            simpa [points, coprimeResidues] using coprimeResidues_head hn2
          have hlast : points.getLastD 0 < k.succ.succ := by
            simpa [points] using wheelCandidateList_getLastD_lt hnonempty
          change k.succ.succ + points.headD 0 - points.getLastD 0 > 0
          rw [hhead]
          omega

/-- В одном периоде сумма всех wheel gaps равна модулю. -/
theorem wheelGaps_sum_eq_of_pos (n : Nat) (hpos : 0 < n) :
    (wheelGaps n).sum = n := by
  let points := wheelCandidateList n
  have hsorted : points.Pairwise (· <= ·) := by
    simp [points, wheelCandidateList]
  have htel := pointGapsList_sum_eq_last points hsorted
  have hnonempty : points ≠ [] := by
    rcases n with _ | k
    · omega
    · cases k with
      | zero =>
          have hmem : 0 ∈ wheelCandidateList 1 := by
            simp [wheelCandidateList, wheelCandidates]
          exact List.ne_nil_of_mem hmem
      | succ k =>
          have hlt : 1 < k.succ.succ := by omega
          have hmem : 1 ∈ wheelCandidateList k.succ.succ := by
            simp [wheelCandidateList, wheelCandidates, hlt]
          exact List.ne_nil_of_mem hmem
  have hlast : points.getLastD 0 < n := by
    simpa [points] using wheelCandidateList_getLastD_lt hnonempty
  have hgap : (pointGapsList points).sum + (n + points.headD 0 - points.getLastD 0) = n := by
    omega
  rw [show wheelGaps n = pointGapsList points ++ [wheelWrapGap n points] by
    simp [wheelGaps, points, hnonempty], List.sum_append, wheelWrapGap]
  change (pointGapsList points).sum + [n + points.headD 0 - points.getLastD 0].sum = n
  rw [show [n + points.headD 0 - points.getLastD 0].sum =
    n + points.headD 0 - points.getLastD 0 by simp]
  exact hgap

/-- Число кандидатов wheel в периоде равно `Nat.totient n`. -/
theorem wheelCandidates_card_eq_totient (n : Nat) :
    (wheelCandidates n).card = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime]
  rfl

/-- Количество wheel gaps равно числу кандидатов, то есть `Nat.totient n`. -/
theorem wheelGaps_length_eq_totient (n : Nat) :
    (wheelGaps n).length = Nat.totient n := by
  let points := wheelCandidateList n
  have hpoints : points.length = (wheelCandidates n).card := by
    simp [points, wheelCandidateList]
  have hcard : (wheelCandidates n).card = Nat.totient n := wheelCandidates_card_eq_totient n
  by_cases hempty : points = []
  · have htot : Nat.totient n = 0 := by
      rw [← hcard, ← hpoints]
      simp [hempty]
    simp [wheelGaps, points, hempty, htot, pointGapsList]
  · have hposlen : 0 < points.length := List.length_pos_of_ne_nil hempty
    simp [wheelGaps, points, hempty, pointGapsList_length, hpoints, hcard]
    omega

/-- Для primorial wheel сумма gaps в одном периоде равна `P_m`. -/
theorem primorial_wheelGaps_sum_eq (m : Nat) :
    (wheelGaps (primorial m)).sum = primorial m := by
  exact wheelGaps_sum_eq_of_pos (primorial m) (primorial_pos m)

/-- Для primorial wheel количество gaps равно `φ(P_m)`. -/
theorem primorial_wheelGaps_length_eq_totient (m : Nat) :
    (wheelGaps (primorial m)).length = Nat.totient (primorial m) := by
  exact wheelGaps_length_eq_totient (primorial m)

/-- Средний gap как рациональное число равен `P_m / φ(P_m)`. -/
noncomputable def primorialWheelMeanGap (m : Nat) : ℚ :=
  (primorial m : ℚ) / (Nat.totient (primorial m) : ℚ)

/-- Среднее, вычисленное по списку gaps, имеет заявленную формулу. -/
theorem primorial_wheelGaps_mean_eq (m : Nat) :
    ((wheelGaps (primorial m)).sum : ℚ) /
        ((wheelGaps (primorial m)).length : ℚ) = primorialWheelMeanGap m := by
  simp [primorialWheelMeanGap, primorial_wheelGaps_sum_eq,
    primorial_wheelGaps_length_eq_totient]

/-- Primorial строго возрастает при добавлении следующего простого множителя. -/
theorem primorial_strictly_increasing (m : Nat) : primorial m < primorial (m + 1) := by
  rw [primorial_succ]
  have hpos : 0 < primorial m := primorial_pos m
  have hprime : 2 ≤ Nat.nth Nat.Prime m := (Nat.prime_nth_prime m).two_le
  nlinarith [Nat.mul_le_mul_left (primorial m) hprime]

/-- Корректная конечная формула Эйлера для `φ(P_m)`. Запрошенная форма с
`Finset.Iic (Nat.nth Nat.Prime m)` включает следующий простой и ложна при `m = 0`. -/
theorem totient_primorial_formula (m : Nat) :
    (Nat.totient (primorial m) : ℚ) =
      (primorial m : ℚ) * (primorial m).primeFactors.prod (fun p => 1 - (p : ℚ)⁻¹) := by
  simpa using Nat.totient_eq_mul_prod_factors (primorial m)

/-- Формальная Mertens-asymptotic гипотеза для среднего primorial wheel gap. -/
def PrimorialWheelAverageGapMertensAsymptotic (γ : ℝ) : Prop :=
  Filter.Tendsto (fun m : Nat => (primorialWheelMeanGap m : ℝ) /
    (Real.exp γ * Real.log (Nat.nth Nat.Prime m))) Filter.atTop (nhds 1)

/-- Последний элемент `cumulativeSum` равен сумме списка. -/
theorem cumulativeSum_last_eq_sum (xs : List Nat) :
    (cumulativeSum xs).getLastD 0 = xs.sum := by
  suffices h : ∀ acc ys, (cumulativeSum.go acc ys).getLastD acc = acc + ys.sum by
    simpa [cumulativeSum] using h 0 xs
  intro acc ys
  induction ys generalizing acc with
  | nil => simp [cumulativeSum.go]
  | cons y rest ih =>
      cases rest with
      | nil => simp [cumulativeSum.go]
      | cons z zs =>
          simpa [cumulativeSum.go, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (acc + y)


/-! ## Exact finite formulas for gap frequencies -/

/-!
## Исследовательский слой: точные формулы для частот промежутков

`primeGapFrequencyExact g x` — конечная формула для числа промежутков `g`
между соседними простыми с правым концом `≤ x`. Доказанные результаты ниже —
развёртки точных конечных определений. Асимптотические, мёбиусовы и
дирихлеевы утверждения оформлены как объекты типа `Prop`, то есть как
слой явно названных математических гипотез.
-/

noncomputable section

open scoped BigOperators
open Filter

/-- Индикатор утверждения со значениями в `Nat`. -/
def natIndicator (P : Prop) [Decidable P] : Nat :=
  if P then 1 else 0

/-- Индикатор простоты. -/
def primeIndicator (n : Nat) : Nat :=
  natIndicator (Nat.Prime n)

/-- `n` и `n + g` — соседние простые с правым концом `≤ x`. -/
def ConsecutivePrimeStart (g x n : Nat) : Prop :=
  0 < g ∧ Nat.Prime n ∧ Nat.Prime (n + g) ∧ n + g ≤ x ∧
    ∀ h : Nat, h ∈ Finset.Icc 1 (g - 1) → ¬ Nat.Prime (n + h)

/-- Один член точной формулы `F(g, x)`: формальный аналог Python `term`. -/
def primeGapTerm (g x n : Nat) : Nat := by
  classical
  exact natIndicator (0 < g) * primeIndicator n * primeIndicator (n + g) *
    natIndicator (n + g ≤ x) *
      (Finset.Icc 1 (g - 1)).prod (fun h => 1 - primeIndicator (n + h))

/-- Точная частота `F(g, x)` через конечное решето по возможным левым концам. -/
def primeGapFrequencyExact (g x : Nat) : Nat :=
  (Finset.range (x + 1)).sum (fun n => primeGapTerm g x n)

/-- Точная частота равна числу левых концов соседних простых с промежутком `g`. -/
theorem primeGapFrequencyExact_eq_count (g x : Nat) :
    primeGapFrequencyExact g x =
      (by classical
       exact ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card) := by
  classical
  trans (Finset.range (x + 1)).sum (fun n => if ConsecutivePrimeStart g x n then 1 else 0)
  · unfold primeGapFrequencyExact
    apply Finset.sum_congr rfl
    intro n hn
    unfold primeGapTerm primeIndicator natIndicator ConsecutivePrimeStart
    have hprod :
        (Finset.Icc 1 (g - 1)).prod (fun h => 1 - if Nat.Prime (n + h) then 1 else 0) =
          if (∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)) then 1 else 0 := by
      by_cases hall : ∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)
      · rw [if_pos hall]
        apply Finset.prod_eq_one
        intro h hh
        simp [hall h hh]
      · rw [if_neg hall]
        push Not at hall
        rcases hall with ⟨h, hh, hp⟩
        exact Finset.prod_eq_zero hh (by simp [hp])
    by_cases hgpos : 0 < g <;>
      by_cases hnprime : Nat.Prime n <;>
      by_cases hngprime : Nat.Prime (n + g) <;>
      by_cases hle : n + g ≤ x <;>
      simp [hgpos, hnprime, hngprime, hle, hprod]
  · exact Finset.sum_boole (fun n => ConsecutivePrimeStart g x n) (Finset.range (x + 1))

/-- Для нечётного `g > 1` точных промежутков нет. Формулировка без `1 < g` ложна: `2,3`. -/
theorem primeGapFrequencyExact_zero_for_odd_g_gt_one (g x : Nat) (hg : Odd g) (hg1 : 1 < g) :
    primeGapFrequencyExact g x = 0 := by
  rw [primeGapFrequencyExact_eq_count]
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro n hn hstart
  rcases hstart with ⟨hgpos, hnprime, hngprime, hle, hbetween⟩
  rcases Nat.even_or_odd n with hneven | hnodd
  · have hn_eq_two : n = 2 := by
      exact hnprime.eq_two_or_odd'.resolve_right (by simpa using hneven)
    have h1mem : 1 ∈ Finset.Icc 1 (g - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hnot : ¬ Nat.Prime (n + 1) := hbetween 1 h1mem
    exact hnot (by simpa [hn_eq_two] using Nat.prime_three)
  · have heven : Even (n + g) := hnodd.add_odd hg
    rcases hngprime.eq_two_or_odd' with htwo | hodd
    · have hn2 : 2 ≤ n := hnprime.two_le
      omega
    · exact (by simpa using heven : ¬ Odd (n + g)) hodd

/-- Булевофинитная форма точной формулы, совпадающая с исходным Python-подходом. -/
theorem primeGapFrequencyExact_eq_sieve_sum (g x : Nat) :
    primeGapFrequencyExact g x =
      (Finset.range (x + 1)).sum (fun n =>
        natIndicator (0 < g) * primeIndicator n * primeIndicator (n + g) *
          natIndicator (n + g ≤ x) *
            (Finset.Icc 1 (g - 1)).prod (fun h => 1 - primeIndicator (n + h))) := by
  rfl

/-- Число простых `≤ x`. -/
def primeCountingExact (x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p => Nat.Prime p).card

/-- Относительная частота промежутка `g` среди простых `≤ x`. -/
def primeGapRelativeFrequency (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) / (primeCountingExact x : ℝ)

/-- Главный член вида `A(g) · π(x) / x`. -/
def pairCorrelationMainTerm (A : Nat → ℝ) (g x : Nat) : ℝ :=
  A g * (primeCountingExact x : ℝ) / (x : ℝ)

/-- Точный остаток после выделения главного члена `A(g) · π(x) / x`. -/
def pairCorrelationError (A : Nat → ℝ) (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) - pairCorrelationMainTerm A g x

/-- Универсальная точная декомпозиция: формула всегда верна с явным остатком. -/
theorem primeGapFrequencyExact_main_add_error (A : Nat → ℝ) (g x : Nat) :
    (primeGapFrequencyExact g x : ℝ) =
      pairCorrelationMainTerm A g x + pairCorrelationError A g x := by
  simp [pairCorrelationError]

/-- Сдвиги, которые должны быть проверены решетом для промежутка `g`. -/
def gapPatternShifts (g : Nat) : Finset Nat :=
  insert 0 (insert g (Finset.Icc 1 (g - 1)))

/-- `p` отбрасывает `n`, если делит хотя бы один из сдвигов `n + h`. -/
def primeDividesPatternAt (g n p : Nat) : Prop :=
  Nat.Prime p ∧ ∃ h : Nat, h ∈ gapPatternShifts g ∧ p ∣ n + h

/-- Конечный слой решета Эратосфена по простым `≤ y`. -/
def survivesFiniteEratosthenesLayer (g n y : Nat) : Prop :=
  ∀ p : Nat, Nat.Prime p → p ≤ y → ¬ primeDividesPatternAt g n p

/-- Частота после просеивания арифметических прогрессий `n ≡ -h (mod p)`. -/
def arithmeticProgressionSieveCount (g x y : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n =>
    0 < g ∧ n + g ≤ x ∧ survivesFiniteEratosthenesLayer g n y).card

/-- Количество запрещённых классов вычетов для двух концов `n` и `n+g` modulo `p`. -/
def endpointForbiddenResidueCount (g p : Nat) : Nat :=
  if p ∣ g then 1 else 2

/-- Формальный конечный singular-series фактор для пары `n, n+g`. -/
def finitePairSieveFactor (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod (fun p =>
    if Nat.Prime p then 1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ) else 1)

/-- Мёбиусоподобное ядро оставлено параметром, чтобы не смешивать его с доказанным `Nat.Prime`. -/
def mobiusPairKernel (mu : Nat → Int) (g x n : Nat) : Int :=
  (Finset.range (x + 1)).sum (fun d =>
    (Finset.range (x + 1)).sum (fun e =>
      if d * d ∣ n ∧ e * e ∣ n + g then mu d * mu e else 0))

/-- Conjecture: мёбиусов слой восстанавливает точную частоту. -/
def MobiusPairGapFormulaConjecture (mu : Nat → Int) : Prop :=
  ∀ g x : Nat,
    (primeGapFrequencyExact g x : Int) =
      (Finset.range (x + 1)).sum (fun n => mobiusPairKernel mu g x n)

/-- Количество простых `≤ x` в прогрессии `a mod q`. -/
def primesInArithmeticProgression (a q x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n => Nat.Prime n ∧ n % q = a % q).card

/-- Conjecture-форма Дирихле: простые равномерны в допустимых классах вычетов. -/
def DirichletUniformityConjecture : Prop :=
  ∀ a q : Nat, Nat.Coprime a q → 0 < q →
    Tendsto (fun x : Nat =>
      (primesInArithmeticProgression a q x : ℝ) /
        ((primeCountingExact x : ℝ) / (Nat.totient q : ℝ))) atTop (nhds 1)

/-- Псевдослучайная модель: конечное решето даёт главный член, а остаток мал после нормировки. -/
def PrimeGapPseudorandomnessConjecture (A normalization : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat => pairCorrelationError A g x / normalization x) atTop (nhds 0)

/-- Средний масштаб простого промежутка около `x`: эвристически `log x`. -/
def meanPrimeGapScale (x : Nat) : ℝ :=
  Real.log (x : ℝ)

/-- GOE Wigner surmise для нормированных промежутков. -/
def wignerGOESurmise (t : ℝ) : ℝ :=
  (Real.pi / 2) * t * Real.exp (-(Real.pi / 4) * t ^ 2)

/-- Масштабированная точечная плотность промежутков. -/
def scaledPrimeGapDensity (g x : Nat) : ℝ :=
  meanPrimeGapScale x * primeGapRelativeFrequency g x

/--
RMT/квантовый хаос: нормированные промежутки между простыми имеют
GOE-предельную плотность с арифметическим коэффициентом `C₂`.
-/
def GOEWignerPrimeGapConjecture (C₂ : ℝ) : Prop :=
  ∀ (g : Nat → Nat) (τ : ℝ),
    Tendsto (fun x : Nat => (g x : ℝ) / meanPrimeGapScale x) atTop (nhds τ) →
      Tendsto (fun x : Nat => scaledPrimeGapDensity (g x) x) atTop
        (nhds (C₂ * wignerGOESurmise τ))

/-- Условие критической прямой для выбранной модели дзета-функции. -/
def ZetaZerosOnCriticalLine (ζ : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, ζ ρ = 0 → ∃ γ : ℝ, ρ = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I

/-- Один член явной формулы `x^ρ / ρ`. -/
def zetaExplicitTerm (ρ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ρ / ρ

/-- Усечённая сумма по выбранному конечному множеству нулей. -/
def zetaExplicitSum (zeros : Finset ℂ) (x : ℝ) : ℂ :=
  zeros.sum fun ρ => zetaExplicitTerm ρ x

/-- Осцилляция явной формулы на интервале длины `g`. -/
def zetaGapOscillation (zeros : Finset ℂ) (g x : Nat) : ℂ :=
  zetaExplicitSum zeros ((x + g : Nat) : ℝ) - zetaExplicitSum zeros (x : ℝ)

/-- Явный остаток после выбора главного члена и конечного набора нулей. -/
def zetaGapRemainder (main : Nat → Nat → ℂ) (zeros : Nat → Finset ℂ)
    (g x : Nat) : ℂ :=
  (primeGapFrequencyExact g x : ℂ) - main g x - zetaGapOscillation (zeros x) g x

/-- Точное разложение через выбранную дзета-осцилляцию и явный остаток. -/
theorem zeta_gap_exact_decomposition (main : Nat → Nat → ℂ) (zeros : Nat → Finset ℂ)
    (g x : Nat) :
    (primeGapFrequencyExact g x : ℂ) =
      main g x + zetaGapOscillation (zeros x) g x + zetaGapRemainder main zeros g x := by
  simp [zetaGapRemainder]

/-- Дзета-гипотеза для промежутков: критическая прямая плюс малый нормированный остаток. -/
def ZetaExplicitPrimeGapConjecture (ζ : ℂ → ℂ) (main : Nat → Nat → ℂ)
    (zeros : Nat → Finset ℂ) (normalization : Nat → ℝ) : Prop :=
  ZetaZerosOnCriticalLine ζ ∧
    ∀ g : Nat,
      Tendsto (fun x : Nat =>
        ‖zetaGapRemainder main zeros g x‖ / normalization x) atTop (nhds 0)

/-! ## Chebyshev, zeta, and analytic conjectures -/

/-- Функция Чебышева `ψ(x) = ∑_{n≤x} Λ(n)`. -/
def chebyshevPsi (x : Nat) : ℝ :=
  (Finset.range (x + 1)).sum fun n => _root_.ArithmeticFunction.vonMangoldt n

/-- При увеличении аргумента `ψ` добавляется ровно следующий член Мангольдта. -/
theorem chebyshevPsi_succ (x : Nat) :
    chebyshevPsi (x + 1) = chebyshevPsi x + _root_.ArithmeticFunction.vonMangoldt (x + 1) := by
  change (Finset.range ((x + 1) + 1)).sum (fun n => _root_.ArithmeticFunction.vonMangoldt n) =
    (Finset.range (x + 1)).sum (fun n => _root_.ArithmeticFunction.vonMangoldt n) +
      _root_.ArithmeticFunction.vonMangoldt (x + 1)
  rw [Finset.sum_range_succ]

/-- Helper: after the sieve completes, composites are marked false. -/
lemma sieve_marks_composites {n i : Nat} (hi : i ≤ n) (hcomp : ¬Nat.Prime i) :
    (eratosthenesSieve n)[i]! = false := by
  sorry

/-- Helper: after the sieve completes, primes are marked true. -/
lemma sieve_keeps_primes {n i : Nat} (hi : i ≤ n) (hprime : Nat.Prime i) :
    (eratosthenesSieve n)[i]! = true := by
  sorry

/-- `eratosthenesSieve n` is true exactly at primes ≤ n.
    Proof structure: split into cases based on primality of i. -/
@[simp]
theorem eratosthenesSieve_correct {n i : Nat} (hi : i ≤ n) :
    (eratosthenesSieve n)[i]! = true ↔ Nat.Prime i := by
  constructor
  · -- Forward: if sieve[i] = true, then i is prime
    intro hsieve
    by_contra hnotprime
    have := sieve_marks_composites hi hnotprime
    simp_all
  · -- Backward: if i is prime, then sieve[i] = true
    intro hprime
    exact sieve_keeps_primes hi hprime

/-- Helper: the for loop in primesUpTo collects exactly indices where sieve is true. -/
lemma primesUpTo_loop_collects (sieve : Array Bool) (n p : Nat) :
    p ∈ (Id.run do
      let mut result := #[]
      for i in [2:n+1] do
        if sieve[i]! then
          result := result.push i
      return result).toList ↔ p ∈ Finset.Ico 2 (n+1) ∧ sieve[p]! := by
  -- The for loop iterates over Finset.Ico 2 (n+1) = {2, 3, ..., n}
  -- Each index i is appended iff sieve[i]! is true
  -- So p is in result iff p ∈ [2:n+1] and sieve[p]!
  sorry

/-- Helper: the for loop produces a strictly increasing array. -/
lemma primesUpTo_loop_sorted (sieve : Array Bool) (n : Nat) :
    (Id.run do
      let mut result := #[]
      for i in [2:n+1] do
        if sieve[i]! then
          result := result.push i
      return result).toList.Pairwise (· < ·) := by
  -- The loop visits indices 2, 3, ..., n in strictly increasing order
  -- Each element is appended to the end, so result is strictly increasing
  sorry

/-- `primesUpTo n` contains exactly the primes ≤ n in increasing order. -/
theorem primesUpTo_spec (n p : Nat) :
    p ∈ (primesUpTo n).toList ↔ Nat.Prime p ∧ p ≤ n := by
  unfold primesUpTo
  rw [primesUpTo_loop_collects]
  constructor
  · intro h
    have h₁ : p ∈ Finset.Ico 2 (n+1) := h.1
    have h₂ : (eratosthenesSieve n)[p]! = true := h.2
    have h₃ : p ≤ n := by
      simp only [Finset.mem_Ico] at h₁
      omega
    have h₄ : Nat.Prime p := by
      rw [eratosthenesSieve_correct h₃] at h₂
      exact h₂
    exact ⟨h₄, h₃⟩
  · intro h
    have h₁ : Nat.Prime p := h.1
    have h₂ : p ≤ n := h.2
    have h₃ : p ∈ Finset.Ico 2 (n+1) := by
      simp only [Finset.mem_Ico]
      have h₄ : 2 ≤ p := h₁.two_le
      omega
    have h₄ : (eratosthenesSieve n)[p]! = true := by
      rw [eratosthenesSieve_correct h₂]
      exact h₁
    exact ⟨h₃, h₄⟩

/-- `primesUpTo n` is strictly increasing. -/
theorem primesUpTo_sorted (n : Nat) : (primesUpTo n).toList.Pairwise (· < ·) := by
  unfold primesUpTo
  exact primesUpTo_loop_sorted (eratosthenesSieve n) n

/-- Вещественный индикатор простоты. -/
def realPrimeIndicator (n : Nat) : ℝ :=
  if n.Prime then 1 else 0

/-- Нормированная функция Мангольдта, занулённая вне простых. -/
def normalizedMangoldtPrime (n : Nat) : ℝ :=
  if n.Prime then _root_.ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) else 0

/-- На простых `Λ(n) / log n = 1`; вне простых обе стороны занулены. -/
theorem normalizedMangoldtPrime_eq_realPrimeIndicator (n : Nat) :
    normalizedMangoldtPrime n = realPrimeIndicator n := by
  unfold normalizedMangoldtPrime realPrimeIndicator
  by_cases hn : n.Prime
  · rw [if_pos hn, _root_.ArithmeticFunction.vonMangoldt_apply_prime hn, if_pos hn]
    have hgt : (1 : ℝ) < n := by exact_mod_cast hn.one_lt
    exact div_self (Real.log_pos hgt).ne'
  · simp [hn]

/-- Нормированная Λ-свёртка на концах `n` и `n + g`. -/
def normalizedMangoldtEndpointWeight (g n : Nat) : ℝ :=
  normalizedMangoldtPrime n * normalizedMangoldtPrime (n + g)

/-- После нормировки по логарифмам Λ-свёртка на концах совпадает с индикаторами простоты. -/
theorem normalizedMangoldtEndpointWeight_eq_prime_indicators (g n : Nat) :
    normalizedMangoldtEndpointWeight g n =
      realPrimeIndicator n * realPrimeIndicator (n + g) := by
  simp [normalizedMangoldtEndpointWeight, normalizedMangoldtPrime_eq_realPrimeIndicator]

/-- Нуль дзета-функции Римана, исключая полюс `1` и нормировочную точку `0`. -/
def RiemannZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1

/-- Один вклад нетривиального нуля в явной формуле для `ψ`: `x^ρ / ρ`. -/
def chebyshevZeroTerm (x ρ : ℂ) : ℂ :=
  x ^ ρ / ρ

/-- Усечённая явная формула Чебышева: главный член минус конечная сумма по выбранным нулям. -/
def truncatedChebyshevExplicitFormula (zeros : Finset ℂ) (x : ℂ) : ℂ :=
  x - zeros.sum (fun ρ => chebyshevZeroTerm x ρ)

/-- Абстрактный остаток полной явной формулы: тривиальные нули, полюс и член усечения. -/
opaque chebyshevExplicitRemainder : ℂ → ℂ := fun _ => 0

/-- Аналитическая формулировка явной формулы для `ψ` через нули `ζ`. -/
def ChebyshevExplicitFormulaConjecture (zeroContribution : ℂ → ℂ) : Prop :=
  ∀ x : Nat,
    (chebyshevPsi x : ℂ) = (x : ℂ) - zeroContribution (x : ℂ) +
      chebyshevExplicitRemainder (x : ℂ)

/-- Коэффициенты Дирихле для скорректированной конечной формулы простых промежутков. -/
def gapDirichletCoeff (g x n : Nat) : ℂ :=
  (primeGapTerm g x n : ℂ)

/-- Ядро Перрона/Меллина `x^s / s`. -/
def perronKernel (x s : ℂ) : ℂ :=
  x ^ s / s

/-- Абстрактный контурный интеграл Перрона для ряда Дирихле. -/
opaque perronIntegral : (ℂ → ℂ) → ℂ → ℂ := fun _ _ => 0

/-- Формальное утверждение, что `A(s)` извлекает частичные суммы коэффициентов `a(n)`. -/
def PerronExtracts (a : Nat → ℂ) (A : ℂ → ℂ) : Prop :=
  ∀ x : Nat, (Finset.range (x + 1)).sum a = perronIntegral A (x : ℂ)

/-- Абстрактная Dirichlet/Mellin-производящая функция для промежутка `g`. -/
opaque gapDirichletSeries : Nat → ℂ → ℂ := fun _ _ => 0

/-- Формулировка Перрона для коэффициентов скорректированной конечной формулы. -/
def PerronGapFormulaConjecture (g x : Nat) : Prop :=
  PerronExtracts (gapDirichletCoeff g x) (gapDirichletSeries g)

/-- Суммарная функция Мёбиуса `M(x) = ∑_{n≤x} μ(n)` в подходе Мингацина/Глауде. -/
def summatoryMoebius (x : Nat) : ℤ :=
  (Finset.range (x + 1)).sum fun n => _root_.ArithmeticFunction.moebius n

/-- При увеличении аргумента `M` добавляется следующий член функции Мёбиуса. -/
theorem summatoryMoebius_succ (x : Nat) :
    summatoryMoebius (x + 1) = summatoryMoebius x + _root_.ArithmeticFunction.moebius (x + 1) := by
  change (Finset.range ((x + 1) + 1)).sum (fun n => _root_.ArithmeticFunction.moebius n) =
    (Finset.range (x + 1)).sum (fun n => _root_.ArithmeticFunction.moebius n) +
      _root_.ArithmeticFunction.moebius (x + 1)
  rw [Finset.sum_range_succ]

/-- Формальная оболочка подхода Мингацина/Глауде: `M` выступает инвертирующим фильтром. -/
def mingazinMoebiusFilteredGapWeight (g x n : Nat) : ℤ × ℂ :=
  (summatoryMoebius n, gapDirichletCoeff g x n)

/-- Арифметическая функция на натуральных числах. -/
abbrev ArithmeticFunction := Nat → ℝ

/-- Оператор суммирования по простым: `(Af)(n) = Σ_{p≤n} f(p)`. -/
def primeSummatoryOperator (f : ArithmeticFunction) (n : Nat) : ℝ :=
  (Finset.range (n + 1)).sum fun p => if Nat.Prime p then f p else 0

/-- Собственная пара для оператора суммирования по простым. -/
def IsPrimeSummatoryEigenpair (f : ArithmeticFunction) (eigenvalue : ℝ) : Prop :=
  f ≠ 0 ∧ ∀ n : Nat, primeSummatoryOperator f n = eigenvalue * f n

/-- Локальная рекурсия оператора: при переходе от `n` к `n+1` добавляется только `n+1`. -/
theorem primeSummatoryOperator_succ (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator f (n + 1) =
      primeSummatoryOperator f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  change (Finset.range ((n + 1) + 1)).sum (fun p => if Nat.Prime p then f p else 0) =
    (Finset.range (n + 1)).sum (fun p => if Nat.Prime p then f p else 0) +
      (if Nat.Prime (n + 1) then f (n + 1) else 0)
  rw [Finset.sum_range_succ]

/-- Любая собственная пара удовлетворяет локальной рекурсии оператора. -/
theorem primeSummatoryEigenpair_recurrence {f : ArithmeticFunction} {eigenvalue : ℝ}
    (h : IsPrimeSummatoryEigenpair f eigenvalue) (n : Nat) :
    eigenvalue * f (n + 1) =
      eigenvalue * f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  rw [← h.2 (n + 1), ← h.2 n]
  exact primeSummatoryOperator_succ f n

/-! ## Determinantal model -/

/-- Детерминантная модель частот простых промежутков. -/
def DeterminantalPrimeGapConjecture
    (kernel : (x g m : Nat) → Fin m → Fin m → ℝ) (weight : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat =>
      primeGapRelativeFrequency g x -
        (Finset.range (g + 1)).sum fun m => weight m * Matrix.det (kernel x g m)) atTop (nhds 0)

/-- Одномерное ядро, тривиально кодирующее точную частоту. -/
def exactOneByOneGapKernel (g x : Nat) : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => primeGapRelativeFrequency g x

/-- Детерминант точного `1 × 1` ядра равен относительной частоте. -/
theorem det_exactOneByOneGapKernel (g x : Nat) :
    Matrix.det (exactOneByOneGapKernel g x) = primeGapRelativeFrequency g x := by
  simp [exactOneByOneGapKernel]

/-! ## Deriving singular series from local wheel model -/

/-!
## Вывод singular series из локальной wheel-модели

1. Для фиксированного gap `g` рассматривается пара endpoint-ов `n` и `n + g`.
2. Просеивание по простому `p` удаляет те классы `n mod p`,
   где хотя бы один endpoint делится на `p`.
3. Первый endpoint запрещает класс `n ≡ 0 (mod p)`.
4. Второй endpoint запрещает класс `n ≡ -g (mod p)`.
5. Эти два класса могут совпасть только тогда, когда `p ∣ g`.
6. Поэтому число запрещённых классов равно `ν_g(p) = 1`, если `p ∣ g`.
7. Если `p ∤ g`, запрещённые классы различны, и `ν_g(p) = 2`.
8. В файле это число формализовано как `endpointForbiddenResidueCount g p`.
9. Обёртка `endpointForbiddenResidueCount` использует ту же локальную величину.
10. Из `p` классов выживает ровно `p - ν_g(p)` классов.
11. Локальная плотность выживания равна `(p - ν_g(p)) / p`.
12. Алгебраически это записано как `1 - ν_g(p) / p`.
13. В коде эта плотность называется `wheelEndpointSurvivalDensity g p`.
14. Для одного endpoint-а эвристическая вероятность не делиться на `p` равна `1 - 1/p`.
15. Для двух независимых endpoint-ов наивная плотность равна `(1 - 1/p)^2`.
16. Но endpoint-ы `n` и `n + g` не независимы modulo `p`.
17. Коррекция сравнивает фактическую локальную плотность с наивной.
18. Поэтому локальный множитель singular series равен `(1 - ν_g(p)/p) / (1 - 1/p)^2`.
19. В файле это `wheelLocalSingularFactor g p`.
20. Если `p ∣ g`, фактор больше, потому что два запрета сливаются в один класс.
21. Если `p ∤ g`, фактор отражает два разных запрещённых класса.
22. Умножение этих локальных поправок по простым даёт глобальную арифметическую поправку.
23. Частичное произведение до уровня `y` задано как `finiteWheelSingularSeries g y`.
24. Предельный объект — singular series `S(g)` для пары сдвигов `(0, g)`.
25. Для нечётного `g` фактор при `p = 2` равен нулю: одна из двух чисел всегда чётна.
26. Поэтому asymptotic singular series нечётных gaps равна `0`.
27. Для чётного `g` фактор при `p = 2` даёт базовый множитель `2`.
28. Остальные нечётные простые дают divisor corrections по простым делителям `g`.
29. Twin prime constant `C₂` собирает регуляризованное произведение по нечётным простым.
30. Оно компенсирует расходимость прямого произведения локальных плотностей.
31. В этом файле `twinPrimeConstantPartial` задаёт конечные приближения к `C₂`.
32. `IsTwinPrimeConstant C₂` формализует выбор предела этих приближений.
33. `singularSeriesFactor C₂ g` использует `C₂` и конечные divisor corrections.
34. Для `g = 2` divisor corrections пусты, и получается классический множитель `2 C₂`.
35. Для больших чётных `g` множители `(p - 1)/(p - 2)` появляются
    ровно при нечётных `p ∣ g`.
-/

/-! ## Hardy-Littlewood conjectures and Gallagher's theorem -/

/-!
## Hardy--Littlewood и теорема Галлагера

В этом блоке аналитические утверждения оформлены как именованные `Prop`.
Бесконечные произведения задаются через пределы частичных произведений по
`Filter.atTop`, без выбора численного значения константы.
-/

/-- Частичное произведение для twin prime constant `C₂`. -/
def twinPrimeConstantPartial (y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- `C₂` является twin prime constant как пределом эйлерова произведения. -/
def IsTwinPrimeConstant (C₂ : ℝ) : Prop :=
  Tendsto twinPrimeConstantPartial atTop (nhds C₂)

/-- Конечное произведение поправок по нечётным простым делителям `k`. -/
def divisorCorrectionProduct (k : Nat) : ℝ :=
  (Finset.range (k + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- Singular series для пары сдвигов `(0, g)` при заданном значении `C₂`. -/
def singularSeriesFactor (C₂ : ℝ) (g : Nat) : ℝ :=
  if Even g then 2 * C₂ * divisorCorrectionProduct (g / 2) else 0

/-- Локальная плотность выживания пары `(n, n + g)` modulo `p`. -/
def wheelEndpointSurvivalDensity (g p : Nat) : ℝ :=
  1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ)

/-- Нормированный локальный множитель singular series в wheel-модели. -/
def wheelLocalSingularFactor (g p : Nat) : ℝ :=
  wheelEndpointSurvivalDensity g p / (1 - 1 / (p : ℝ)) ^ 2

/-- Конечная wheel-версия произведения локальных множителей. -/
def finiteWheelSingularSeries (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then wheelLocalSingularFactor g p else 1

/-- Конечный wheel-ряд сходится к singular series factor при `y → ∞`. -/
def finiteWheelSingularSeriesLimit (g : Nat) (C₂ : ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun y => finiteWheelSingularSeries g y) Filter.atTop (nhds L) ∧
    L = singularSeriesFactor C₂ g

/-- Локальный wheel-множитель совпадает с нормированной локальной плотностью survival. -/
theorem wheelLocalSingularFactor_eq_singular (g p : Nat) (_hp : Nat.Prime p) :
    wheelLocalSingularFactor g p =
      (1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ)) /
        (1 - 1 / (p : ℝ)) ^ 2 := by
  simp [wheelLocalSingularFactor, wheelEndpointSurvivalDensity, endpointForbiddenResidueCount]

/-- Явная форма локального wheel-множителя через делимость `p ∣ g`. -/
theorem wheelLocalSingularFactor_eq_singular_simplified (g p : Nat) (hp : Nat.Prime p) :
    wheelLocalSingularFactor g p =
      (1 - (if p ∣ g then (1 : ℝ) else (2 : ℝ)) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  rw [wheelLocalSingularFactor_eq_singular g p hp]
  simp [endpointForbiddenResidueCount]

/-- Глобальная wheel-series равна survival-произведению с делением на наивные endpoint-плотности. -/
theorem finiteWheelSingularSeries_eq_finitePairSieveFactor_div_sq (g y : Nat) :
    finiteWheelSingularSeries g y =
      finitePairSieveFactor g y /
        (Finset.range (y + 1)).prod (fun p =>
          if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else 1) := by
  rw [finiteWheelSingularSeries, finitePairSieveFactor, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hprime : Nat.Prime p
  · simp [hprime, wheelLocalSingularFactor, wheelEndpointSurvivalDensity,
      endpointForbiddenResidueCount]
  · simp [hprime]

/-- Wheel-ряд, умноженный на квадратичное произведение наивных плотностей, даёт sieve-фактор. -/
theorem finiteWheelSingularSeries_eq_finitePairSieveFactor_normalized (g y : Nat) :
    finiteWheelSingularSeries g y * (Finset.range (y + 1)).prod (fun p =>
      if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else 1) =
    finitePairSieveFactor g y := by
  let denom := (Finset.range (y + 1)).prod (fun p =>
    if Nat.Prime p then (1 - 1 / (p : ℝ)) ^ 2 else (1 : ℝ))
  have hdenom_ne_zero : denom ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p _
    by_cases hprime : Nat.Prime p
    · rw [if_pos hprime]
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast Nat.Prime.pos hprime
      have hp_gt_one : 1 < (p : ℝ) := by exact_mod_cast Nat.Prime.one_lt hprime
      have h_div_lt_one : 1 / (p : ℝ) < 1 := (div_lt_one hp_pos).mpr hp_gt_one
      exact pow_ne_zero 2 (sub_ne_zero_of_ne (ne_of_lt h_div_lt_one).symm)
    · rw [if_neg hprime]
      exact one_ne_zero
  rw [finiteWheelSingularSeries_eq_finitePairSieveFactor_div_sq g y]
  exact div_mul_cancel₀ _ hdenom_ne_zero

/-- Интеграл `li₂(x) = ∫₂ˣ dt / log² t`. -/
def logarithmicIntegral₂ (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2

/-- Главный член Hardy--Littlewood для пар простых с промежутком `g`. -/
def hardyLittlewoodMainTerm (C₂ : ℝ) (g : Nat) (x : ℝ) : ℝ :=
  singularSeriesFactor C₂ g * logarithmicIntegral₂ x

/-- Число простых пар `(p, p + g)` с `p ≤ x`. -/
def primePairCount (g x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (p + g)).card

/-- Отношение `f(x) / h(x) → 1` при `x → ∞`. -/
def AsymptoticEquivalentAtTop (f h : Nat → ℝ) : Prop :=
  Tendsto (fun x : Nat => f x / h x) atTop (nhds 1)

/-- Hardy--Littlewood k-tuple conjecture для пар `(0, g)`. -/
def HardyLittlewoodPairConjecture (C₂ : ℝ) : Prop :=
  ∀ g : Nat, 0 < singularSeriesFactor C₂ g →
    AsymptoticEquivalentAtTop
      (fun x => (primePairCount g x : ℝ))
      (fun x => hardyLittlewoodMainTerm C₂ g (x : ℝ))

/-- Множество сдвигов допустимо, если modulo каждого простого остаётся свободный класс. -/
def AdmissibleSet (H : Finset ℤ) : Prop :=
  ∀ p : Nat, Nat.Prime p → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- Сколько сдвигов из `H` попадает в запрещённый класс modulo `p`. -/
def tupleForbiddenResidueCount (H : Finset ℤ) (p : Nat) : Nat := by
  classical
  exact (H.image fun h => (h : ZMod p)).card

/-- Частичное произведение singular series для произвольного finite tuple. -/
def tupleSingularSeriesPartial (H : Finset ℤ) (y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then
      (1 - (tupleForbiddenResidueCount H p : ℝ) / (p : ℝ)) /
        (1 - 1 / (p : ℝ)) ^ H.card
    else 1

/-- `S` является singular series для tuple `H`. -/
def IsTupleSingularSeries (H : Finset ℤ) (S : ℝ) : Prop :=
  Tendsto (tupleSingularSeriesPartial H) atTop (nhds S)

/-- Число `n ≤ x`, для которых все `n + h`, `h ∈ H`, простые. -/
def primeTupleCount (H : Finset ℤ) (x : Nat) : Nat := by
  classical
  let p : ℕ → Prop := fun n => ∀ h ∈ H, Nat.Prime ((n : ℤ) + h).toNat
  exact ((Finset.range (x + 1)).filter p).card

/-- Hardy--Littlewood k-tuple conjecture как именованное утверждение. -/
def HardyLittlewoodKTupleConjecture : Prop :=
  ∀ H : Finset ℤ, AdmissibleSet H → ∀ S : ℝ, IsTupleSingularSeries H S →
    AsymptoticEquivalentAtTop
      (fun x => (primeTupleCount H x : ℝ))
      (fun x => S * logarithmicIntegral₂ (x : ℝ) / (Real.log (x : ℝ)) ^ (H.card - 2))

/-- Промежуток `g` встречается как соседний простой промежуток с левым концом `≤ x`. -/
def PrimeGapOccursUpTo (g x : Nat) : Prop :=
  ∃ p : Nat, ConsecutivePrimeStart g (p + g) p ∧ p ≤ x

/-- Число соседних простых промежутков `≤ T log x` среди левых концов `≤ x`. -/
def normalizedPrimeGapCountLE (T : ℝ) (x : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun p =>
    ∃ g : Nat, ConsecutivePrimeStart g (p + g) p ∧ (g : ℝ) ≤ T * Real.log (x : ℝ)).card

/-- Предельный закон Галлагера: нормированные промежутки имеют экспоненциальное распределение. -/
def GallaghersPoissonLimit : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    Tendsto (fun x : Nat => (normalizedPrimeGapCountLE T x : ℝ) /
      (primeCountingExact x : ℝ)) atTop (nhds (1 - Real.exp (-T)))

/-- Теорема Галлагера как условная формулировка от k-tuple conjecture. -/
def GallaghersTheoremFromHL : Prop :=
  HardyLittlewoodKTupleConjecture → GallaghersPoissonLimit

/-- Нулевое частичное произведение `C₂` пусто по простым `> 2`. -/
theorem twinPrimeConstantPartial_zero : twinPrimeConstantPartial 0 = 1 := by
  norm_num [twinPrimeConstantPartial]

/-- До простого `2` в произведении `C₂` ещё нет нечётных простых. -/
theorem twinPrimeConstantPartial_two : twinPrimeConstantPartial 2 = 1 := by
  norm_num [twinPrimeConstantPartial, Finset.prod_range_succ]

/-- Для `k = 1` нет нечётных простых делителей. -/
theorem divisorCorrectionProduct_one : divisorCorrectionProduct 1 = 1 := by
  norm_num [divisorCorrectionProduct, Finset.prod_range_succ]

/-- Для `k = 2` нечётных простых делителей тоже нет. -/
theorem divisorCorrectionProduct_two : divisorCorrectionProduct 2 = 1 := by
  norm_num [divisorCorrectionProduct, Finset.prod_range_succ]

/-- Для `k = 3` единственная поправка равна `(3 - 1)/(3 - 2) = 2`. -/
theorem divisorCorrectionProduct_three : divisorCorrectionProduct 3 = 2 := by
  norm_num [divisorCorrectionProduct, Finset.prod_range_succ]

/-- Нечётные промежутки имеют нулевой singular series. -/
theorem singularSeriesFactor_of_odd {C₂ : ℝ} {g : Nat} (hg : Odd g) :
    singularSeriesFactor C₂ g = 0 := by
  simp [singularSeriesFactor, Nat.not_even_iff_odd.mpr hg]

/-- В частности, промежуток `1` имеет нулевой asymptotic singular series. -/
theorem singularSeriesFactor_one (C₂ : ℝ) : singularSeriesFactor C₂ 1 = 0 := by
  norm_num [singularSeriesFactor]

/-- Для twin-prime gap `2` получается `2 C₂`. -/
theorem singularSeriesFactor_two (C₂ : ℝ) : singularSeriesFactor C₂ 2 = 2 * C₂ := by
  norm_num [singularSeriesFactor, divisorCorrectionProduct, Finset.prod_range_succ]

/-- Для gap `4` поправка такая же, как для twin primes. -/
theorem singularSeriesFactor_four (C₂ : ℝ) : singularSeriesFactor C₂ 4 = 2 * C₂ := by
  norm_num [singularSeriesFactor, divisorCorrectionProduct, Finset.prod_range_succ]

/-- Для gap `6` появляется множитель `2` от простого делителя `3`. -/
theorem singularSeriesFactor_six (C₂ : ℝ) : singularSeriesFactor C₂ 6 = 4 * C₂ := by
  norm_num [singularSeriesFactor, divisorCorrectionProduct, Finset.prod_range_succ]
  ring

/-- Для чётного gap формула сводится к произведению по простым делителям половины gap. -/
theorem singularSeriesFactor_even (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) = 2 * C₂ * divisorCorrectionProduct k := by
  simp [singularSeriesFactor]

/-- Для gap `2` через общую формулу чётного gap: `2 C₂` с пустой поправкой. -/
theorem singularSeriesFactor_two_explicit (C₂ : ℝ) :
    singularSeriesFactor C₂ 2 = 2 * C₂ * divisorCorrectionProduct 1 := by
  rw [show 2 = 2 * 1 by norm_num]
  rw [singularSeriesFactor_even]

/-- Для gap `4` через общую формулу чётного gap: `2 C₂` с пустой поправкой. -/
theorem singularSeriesFactor_four_explicit (C₂ : ℝ) :
    singularSeriesFactor C₂ 4 = 2 * C₂ * divisorCorrectionProduct 2 := by
  rw [show 4 = 2 * 2 by norm_num]
  rw [singularSeriesFactor_even]

/-- Конечная поправка равна произведению по нечётным простым делителям. -/
theorem divisorCorrectionProduct_eq_primeFactors (k : Nat) :
    divisorCorrectionProduct k =
      ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [divisorCorrectionProduct]
  · rw [divisorCorrectionProduct, ← Finset.prod_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · intro h
      exact ⟨⟨h.2.1, h.2.2.2, hk0⟩, h.2.2.1⟩
    · intro h
      rcases h with ⟨⟨hprime, hdvd, _⟩, hgt⟩
      have hle : p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
      exact ⟨Nat.lt_succ_iff.mpr hle, hprime, hgt, hdvd⟩

/-- Явная формула singular series для чётного gap через нечётные простые делители `k`. -/
theorem singularSeriesFactor_even_correct (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) =
      2 * C₂ * ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [singularSeriesFactor_even, divisorCorrectionProduct_eq_primeFactors]

/-- Связь с wheel: глобальная формула — базовая константа `2 C₂` и поправки по `p ∣ k`. -/
theorem singularSeriesFactor_eq_wheel_divisor_product (C₂ : ℝ) (k : Nat) :
    singularSeriesFactor C₂ (2 * k) = 2 * C₂ *
      (Finset.range (k + 1)).prod (fun p =>
        if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
  simp [singularSeriesFactor_even, divisorCorrectionProduct]

/-- Пустое множество сдвигов допустимо. -/
theorem admissibleSet_empty : AdmissibleSet (∅ : Finset ℤ) := by
  intro p hp
  exact ⟨0, by simp⟩

/-- Singleton сдвигов допустим: берём класс `1` modulo любого простого. -/
theorem admissibleSet_singleton_zero : AdmissibleSet ({0} : Finset ℤ) := by
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨1, ?_⟩
  intro h hh
  simp at hh
  subst h
  simp [zero_ne_one]

/-- `addGapCount` увеличивает сумму частот на 1. -/
lemma addGapCount_sum_succ (counts : Array (Nat × Nat)) (g : Nat) :
    ((addGapCount counts g).toList.map Prod.snd).sum =
    (counts.toList.map Prod.snd).sum + 1 := by
  sorry

/-- `sortedGapCounts` сохраняет сумму частот. -/
lemma sortedGapCounts_sum_eq (counts : Array (Nat × Nat)) :
    ((sortedGapCounts counts).map Prod.snd).sum =
    (counts.toList.map Prod.snd).sum := by
  sorry

/-- For-loop в `gapDistributionByCount` обрабатывает ровно k простых чисел. -/
lemma primesUpTo_nthPrimeByGaps_size (k : Nat) (hk : 0 < k) :
    (primesUpTo (nthPrimeByGaps (k - 1))).size = k := by
  sorry

/-- Sum of frequencies in gapDistributionByCount equals k (for k > 0). -/
theorem gapDistributionByCount_sum_eq_k {k : Nat} (hk : 0 < k) :
    List.sum ((gapDistributionByCount k).map Prod.snd) = k := by
  unfold gapDistributionByCount
  have hk_ne_zero : k ≠ 0 := by omega
  simp [hk_ne_zero]
  -- After the for-loop, the array contains k gaps, each contributing 1 to the sum
  have h_primes_count := primesUpTo_nthPrimeByGaps_size k hk
  -- Each iteration of the for-loop adds 1 to the sum (by addGapCount_sum_succ)
  -- After k iterations starting from empty array, sum = k
  let counts := (primesUpTo (nthPrimeByGaps (k - 1))).toList.foldl
    (fun acc p => addGapCount acc (p - 1)) #[]
  have h_loop_sum : (counts.toList.map Prod.snd).sum = k := by
    sorry
  -- sortedGapCounts preserves the sum
  rw [sortedGapCounts_sum_eq]
  exact h_loop_sum

/-- For a pair tuple {0, g}, primeTupleCount equals primePairCount. -/
theorem primeTupleCount_pair_eq_primePairCount (g x : Nat) :
    primeTupleCount ({0, (g : ℤ)} : Finset ℤ) x = primePairCount g x := by
  unfold primeTupleCount primePairCount
  dsimp only
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hcast : (↑n + ↑g : ℤ).toNat = n + g := by
    rw [← Nat.cast_add, Int.toNat_natCast]
  constructor
  · intro h
    have h0 := h 0 (by simp)
    have hg := h (↑g) (by simp)
    have hn : Nat.Prime n := by simpa [Int.toNat_natCast] using h0
    have hng : Nat.Prime (n + g) := by simpa [hcast] using hg
    exact ⟨hn, hng⟩
  · intro ⟨hn, hng⟩ h hh
    cases hh with
    | inl h0 => rw [h0]; simpa [Int.toNat_natCast] using hn
    | inr hg => rw [hg]; simpa [hcast] using hng

end

end PrimeGaps

import Mathlib

namespace PrimeGaps

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

/-!
## Primorial wheel: кандидаты и циклические промежутки

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

/-- Wrap-around gap от последнего кандидата к первому в следующем периоде. -/
def wheelWrapGap (n : Nat) (points : List Nat) : Nat :=
  n + points.headD 0 - points.getLastD 0

/-- Все gaps wheel modulo `n`, включая wrap-around. -/
def wheelGaps (n : Nat) : List Nat :=
  let points := wheelCandidateList n
  pointGapsList points ++ if points = [] then [] else [wheelWrapGap n points]

/-- У непустого списка значение `getLastD` действительно является его элементом. -/
theorem List.getLastD_mem_of_ne_nil {α : Type} [Inhabited α] (xs : List α) (hxs : xs ≠ []) :
    xs.getLastD default ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest => simp [List.getLastD]

/-- В возрастающем списке кандидатов каждый последний элемент всё ещё меньше модуля. -/
theorem wheelCandidateList_getLastD_lt {n : Nat}
    (hnonempty : wheelCandidateList n ≠ []) :
    (wheelCandidateList n).getLastD 0 < n := by
  have hmem : (wheelCandidateList n).getLastD 0 ∈ wheelCandidateList n :=
    List.getLastD_mem_of_ne_nil (wheelCandidateList n) hnonempty
  have hs : (wheelCandidateList n).getLastD 0 ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp hmem
  exact Finset.mem_range.mp (Finset.mem_filter.mp hs).1

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

/-- Формула восстановления через сумму промежутков. -/
theorem nthPrimeByGaps_eq_sum (gaps : List Nat) :
    (cumulativeSum gaps).getLastD 0 = gaps.sum := by
  exact cumulativeSum_last_eq_sum gaps


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

/-- Локальная wheel-поправка: число запрещённых классов для концов пары. -/
def wheelEndpointForbiddenCount (g p : Nat) : Nat :=
  endpointForbiddenResidueCount g p

/-- Локальная плотность выживания пары `(n, n + g)` modulo `p`. -/
def wheelEndpointSurvivalDensity (g p : Nat) : ℝ :=
  1 - (wheelEndpointForbiddenCount g p : ℝ) / (p : ℝ)

/-- Нормированный локальный множитель singular series в wheel-модели. -/
def wheelLocalSingularFactor (g p : Nat) : ℝ :=
  wheelEndpointSurvivalDensity g p / (1 - 1 / (p : ℝ)) ^ 2

/-- Конечная wheel-версия произведения локальных множителей. -/
def finiteWheelSingularSeries (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then wheelLocalSingularFactor g p else 1

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
  exact ((Finset.range (x + 1)).filter fun n =>
    ∀ h ∈ H, Nat.Prime ((n : ℤ) + h).toNat).card

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
  simpa using (zero_ne_one : (0 : ZMod p) ≠ 1)

end

end PrimeGaps

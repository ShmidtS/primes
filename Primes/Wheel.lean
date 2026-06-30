import Mathlib
import Primes.Basic

namespace PrimeGaps

noncomputable section

/-! ## Primorial definitions -/

/-- Primorial `P_m`: произведение первых `m` простых чисел. -/
def primorial (m : Nat) : Nat :=
  (Finset.range m).prod fun i => Nat.nth Nat.Prime i

/-- Индуктивное раскрытие primorial при добавлении следующего простого. -/
theorem primorial_succ (m : Nat) :
    primorial (m + 1) = primorial m * Nat.nth Nat.Prime m := by
  simp [primorial, Finset.prod_range_succ]

/-- Primorial всегда положителен. -/
theorem primorial_pos (m : Nat) : 0 < primorial m := by
  unfold primorial
  exact Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

/-- Primorial строго возрастает при добавлении следующего простого множителя. -/
theorem primorial_strictly_increasing (m : Nat) : primorial m < primorial (m + 1) := by
  rw [primorial_succ]
  have hpos : 0 < primorial m := primorial_pos m
  have hprime : 2 <= Nat.nth Nat.Prime m := (Nat.prime_nth_prime m).two_le
  nlinarith [Nat.mul_le_mul_left (primorial m) hprime]

/-! ## Wheel candidates and coprime residues -/

/-- Кандидаты wheel modulo `n`: классы `a < n`, взаимно простые с `n`. -/
def wheelCandidates (n : Nat) : Finset Nat :=
  (Finset.range n).filter fun a => Nat.Coprime n a

/-- Кандидаты wheel как возрастающий список остатков. -/
def wheelCandidateList (n : Nat) : List Nat :=
  (wheelCandidates n).sort (· <= ·)

/-- Синоним: остатки, взаимно простые с n, в порядке возрастания. -/
def coprimeResidues (n : Nat) : List Nat := wheelCandidateList n

/-- Первый взаимно простой остаток modulo `n >= 2` равен `1`. -/
theorem coprimeResidues_head {n : Nat} (hn : 2 <= n) : (coprimeResidues n).headD 0 = 1 := by
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
      have : n <= 1 := Nat.le_of_dvd (by omega) hn_dvd_one
      omega
    have hsorted : (coprimeResidues n).Pairwise (· <= ·) := by
      simp [coprimeResidues, wheelCandidateList]
    have hsorted_cons : (a :: tail).Pairwise (· <= ·) := by
      simpa [hlist] using hsorted
    have hle : a <= 1 := by
      have hforall : ∀ b ∈ tail, a <= b := (List.pairwise_cons.mp hsorted_cons).1
      have hmem1_cons : 1 ∈ a :: tail := by simpa [hlist] using hmem1
      cases hmem1_cons with
      | head => rfl
      | tail _ ht => exact hforall 1 ht
    exact Nat.le_antisymm hle ha_pos

/-- `coprimeResidues P` непуст при `P >= 2`. -/
theorem coprimeResidues_ne_nil_of_ge_two {P : Nat} (hP : 2 <= P) :
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
        have hforall_le : ∀ b ∈ tail, a <= b := (List.pairwise_cons.mp hle_cons).1
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
theorem wheelCandidateList_sorted {n : Nat} (hn : 2 <= n) :
    (wheelCandidateList n).Pairwise (· < ·) := by
  have hsorted := coprimeResidues_append_succ_sorted (P := n) (by omega)
  have happend := (List.pairwise_append.mp hsorted).1
  simpa [coprimeResidues] using happend

/-- Элемент `coprimeResidues n` является взаимно простым остатком modulo `n`. -/
theorem coprimeResidues_mod_n {n : Nat} (_hn : 2 <= n) (a : Nat)
    (ha : a ∈ coprimeResidues n) : a < n ∧ Nat.Coprime n a := by
  have hs : a ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp
      (by simpa [coprimeResidues, wheelCandidateList] using ha)
  exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hs).1,
    (Finset.mem_filter.mp hs).2⟩

/-! ## Wheel gaps -/

/-- В возрастающем списке кандидатов каждый последний элемент всё ещё меньше модуля. -/
theorem wheelCandidateList_getLastD_lt {n : Nat}
    (hnonempty : wheelCandidateList n ≠ []) :
    (wheelCandidateList n).getLastD 0 < n := by
  have hmem : (wheelCandidateList n).getLastD 0 ∈ wheelCandidateList n :=
    List.getLastD_mem_of_ne_nil (wheelCandidateList n) hnonempty
  have hs : (wheelCandidateList n).getLastD 0 ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp hmem
  exact Finset.mem_range.mp (Finset.mem_filter.mp hs).1

/-- Wrap-around gap от последнего кандидата к первому в следующем периоде. -/
def wheelWrapGap (n : Nat) (points : List Nat) : Nat :=
  n + points.headD 0 - points.getLastD 0

/-- Все gaps wheel modulo `n`, включая wrap-around. -/
def wheelGaps (n : Nat) : List Nat :=
  let points := wheelCandidateList n
  pointGapsList points ++ if points = [] then [] else [wheelWrapGap n points]

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
            simp only [pointGapsList, List.mem_cons] at hg
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
      have hn2 : 2 <= k.succ.succ := by omega
      have hnonempty : points ≠ [] := by
        simpa [points, coprimeResidues] using
          coprimeResidues_ne_nil_of_ge_two (P := k.succ.succ) hn2
      have hstrict : points.Pairwise (· < ·) := by
        simpa [points] using wheelCandidateList_sorted hn2
      rw [show wheelGaps k.succ.succ = pointGapsList points ++ [wheelWrapGap k.succ.succ points] by
        simp [wheelGaps, points, hnonempty]] at hg
      rw [List.mem_append, List.mem_singleton] at hg
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

/-! ## Primorial wheel properties -/

/-- Для primorial wheel сумма gaps в одном периоде равна `P_m`. -/
theorem primorial_wheelGaps_sum_eq (m : Nat) :
    (wheelGaps (primorial m)).sum = primorial m := by
  exact wheelGaps_sum_eq_of_pos (primorial m) (primorial_pos m)

/-- Для primorial wheel количество gaps равно `φ(P_m)`. -/
theorem primorial_wheelGaps_length_eq_totient (m : Nat) :
    (wheelGaps (primorial m)).length = Nat.totient (primorial m) := by
  exact wheelGaps_length_eq_totient (primorial m)

/-- Средний gap как рациональное число равен `P_m / φ(P_m)`. -/
def primorialWheelMeanGap (m : Nat) : ℚ :=
  (primorial m : ℚ) / (Nat.totient (primorial m) : ℚ)

/-- Среднее, вычисленное по списку gaps, имеет заявленную формулу. -/
theorem primorial_wheelGaps_mean_eq (m : Nat) :
    ((wheelGaps (primorial m)).sum : ℚ) /
        ((wheelGaps (primorial m)).length : ℚ) = primorialWheelMeanGap m := by
  simp [primorialWheelMeanGap, primorial_wheelGaps_sum_eq,
    primorial_wheelGaps_length_eq_totient]

/-- Корректная конечная формула Эйлера для `φ(P_m)`. Запрошенная форма с
`Finset.Iic (Nat.nth Nat.Prime m)` включает следующий простой и ложна при `m = 0`. -/
theorem totient_primorial_formula (m : Nat) :
    (Nat.totient (primorial m) : ℚ) =
      (primorial m : ℚ) * (primorial m).primeFactors.prod (fun p => 1 - (p : ℚ)⁻¹) := by
  simpa using Nat.totient_eq_mul_prod_factors (primorial m)

/-- Явная формула `φ(P_m)` через произведение `(p_i - 1)` по первым `m` простым.
Доказательство: `P_{m+1} = P_m · p_m`, `p_m` не делит `P_m` (так как `p_m`
больше всех предыдущих простых), поэтому `φ(P_{m+1}) = φ(P_m)·(p_m - 1)`.
Индукция даёт произведение. -/
theorem totient_primorial_explicit (m : Nat) :
    Nat.totient (primorial m) = (Finset.range m).prod (fun i => Nat.nth Nat.Prime i - 1) := by
  induction m with
  | zero =>
    simp [primorial, Nat.totient_one]
  | succ m ih =>
    rw [primorial_succ, Nat.totient_mul]
    · rw [ih]
      have hp : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      rw [Nat.totient_prime hp]
      simp [Finset.prod_range_succ, Nat.mul_sub]
    · -- p_m не делит primorial m, так как все делители primorial m меньше p_m
      apply (Nat.coprime_prod_left_iff (t := Finset.range m)
        (s := fun i => Nat.nth Nat.Prime i) (x := Nat.nth Nat.Prime m)).mpr
      intro i hi
      simp only [Finset.mem_range] at hi
      have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
      have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m := by
        exact (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr hi
      exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)

/-- Гипотеза Мертенса для среднего primorial wheel gap: отношение
`P_m / φ(P_m)` к `e^γ log p_m` стремится к 1. Открытая проблема,
эквивалентна гипотезе Мертенса о произведении `(1 - 1/p)`.
Эйлерова константа `γ ≈ 0.5772`. -/
def PrimorialWheelAverageGapMertensAsymptotic (γ : ℝ) : Prop :=
  Filter.Tendsto (fun m : Nat => (primorialWheelMeanGap m : ℝ) /
    (Real.exp γ * Real.log (Nat.nth Nat.Prime m))) Filter.atTop (nhds 1)

/-! ### Exact wheel computations for small moduli -/

/-- `primorial 0 = 1` (пустое произведение). -/
theorem primorial_zero : primorial 0 = 1 := by
  simp [primorial]

/-- `primorial 1 = 2` (первое простое). -/
theorem primorial_one : primorial 1 = 2 := by
  simp only [primorial, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty,
    one_mul, Nat.nth_prime_zero_eq_two]

/-- `primorial 2 = 6` (2 · 3). -/
theorem primorial_two : primorial 2 = 6 := by
  simp only [primorial, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty,
    one_mul, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  norm_num

/-- `primorial 3 = 30` (2 · 3 · 5). -/
theorem primorial_three : primorial 3 = 30 := by
  simp only [primorial, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty,
    one_mul, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  norm_num

/-- `φ(P_0) = φ(1) = 1`. -/
theorem totient_primorial_zero : Nat.totient (primorial 0) = 1 := by
  rw [primorial_zero, Nat.totient_one]

/-- `φ(P_1) = φ(2) = 1`. -/
theorem totient_primorial_one : Nat.totient (primorial 1) = 1 := by
  rw [primorial_one, Nat.totient_prime (by decide : Nat.Prime 2)]

/-- `φ(P_2) = φ(6) = 2` (остатки 1 и 5). -/
theorem totient_primorial_two : Nat.totient (primorial 2) = 2 := by
  rw [primorial_two]
  have : Nat.totient 6 = 2 := by decide
  exact this

/-- `φ(P_3) = φ(30) = 8` (остатки 1,7,11,13,17,19,23,29). -/
theorem totient_primorial_three : Nat.totient (primorial 3) = 8 := by
  rw [primorial_three]
  have : Nat.totient 30 = 8 := by decide
  exact this

/-- Средний primorial wheel gap для `m = 2`: `P_2 / φ(P_2) = 6/2 = 3`. -/
theorem primorial_wheelGaps_mean_gap_m2 : primorialWheelMeanGap 2 = 3 := by
  unfold primorialWheelMeanGap primorial
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  change ((6 : ℚ) / (Nat.totient 6 : ℚ)) = 3
  rw [show Nat.totient 6 = 2 by decide]
  norm_num

/-! ### Exact wheel gap computations -/

/-- Сумма wheel gaps для `n = 6` равна `6` (один полный период). -/
theorem wheelGaps_6_sum : (wheelGaps 6).sum = 6 := by
  exact wheelGaps_sum_eq_of_pos 6 (by decide)

/-- Длина wheel gaps для `n = 6` равна `φ(6) = 2`. -/
theorem wheelGaps_6_length : (wheelGaps 6).length = 2 := by
  rw [wheelGaps_length_eq_totient]
  decide

end

end PrimeGaps

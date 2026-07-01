import Mathlib
import Primes.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

/-- Primorial `P_m`: произведение первых `m` простых чисел. -/
def primorial (m : Nat) : Nat :=
  (Finset.range m).prod fun i => Nat.nth Nat.Prime i

/-- Индуктивное раскрытие primorial. -/
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
      have hn_dvd_one : n ∣ 1 := ha_coprime.dvd_of_dvd_mul_right (dvd_zero n)
      have : n <= 1 := Nat.le_of_dvd (by omega) hn_dvd_one
      omega
    have hsorted : (coprimeResidues n).Pairwise (· <= ·) := by
      simp [coprimeResidues, wheelCandidateList]
    have hsorted_cons : (a :: tail).Pairwise (· <= ·) := by simpa [hlist] using hsorted
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
  have hmem : 1 ∈ coprimeResidues P := by
    simp [coprimeResidues, wheelCandidateList, wheelCandidates, show 1 < P by omega]
  exact List.ne_nil_of_mem hmem

/-- Append правого endpoint `P + 1` сохраняет строгий порядок остатков. -/
private theorem coprimeResidues_append_succ_sorted {P : Nat} (_hP : 0 < P) :
    (coprimeResidues P ++ [P + 1]).Pairwise (· < ·) := by
  classical
  have hP' : P < P + 1 := by omega
  have le_nodup_to_lt : ∀ xs : List Nat,
      xs.Pairwise (· <= ·) → xs.Nodup → xs.Pairwise (· < ·) := by
    intro xs hle hnodup
    induction xs with
    | nil => exact List.Pairwise.nil
    | cons a tail ih =>
        have hforall_le : ∀ b ∈ tail, a <= b := (List.pairwise_cons.mp hle).1
        have ha_not_mem : a ∉ tail := (List.nodup_cons.mp hnodup).1
        exact List.Pairwise.cons
          (fun b hb => Nat.lt_of_le_of_ne (hforall_le b hb)
            (fun hab => ha_not_mem (by simpa [hab] using hb)))
          (ih (List.pairwise_cons.mp hle).2 (List.nodup_cons.mp hnodup).2)
  have hstrict : (coprimeResidues P).Pairwise (· < ·) := by
    apply le_nodup_to_lt <;> simp [coprimeResidues, wheelCandidateList]
  rw [List.pairwise_append]
  refine ⟨hstrict, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  have ha_mem : a ∈ wheelCandidates P :=
    (Finset.mem_sort (s := wheelCandidates P) (r := (· <= ·))).mp
      (by simpa [coprimeResidues, wheelCandidateList] using ha)
  have hltP : a < P := Finset.mem_range.mp (Finset.mem_filter.mp ha_mem).1
  exact Nat.lt_trans hltP hP'

/-- Кандидаты wheel образуют строго возрастающий список. -/
theorem wheelCandidateList_sorted {n : Nat} (hn : 2 <= n) :
    (wheelCandidateList n).Pairwise (· < ·) := by
  have hsorted := coprimeResidues_append_succ_sorted (P := n) (by omega)
  have happend := (List.pairwise_append.mp hsorted).1
  simpa [coprimeResidues] using happend

/-- В возрастающем списке кандидатов каждый последний элемент меньше модуля. -/
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
            | inl hg => subst g; have hab : a < b := (List.pairwise_cons.mp hpoints).1 b (by simp); omega
            | inr hg => exact ih (List.pairwise_cons.mp hpoints).2 g hg
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
        simpa [points, coprimeResidues] using coprimeResidues_ne_nil_of_ge_two (P := k.succ.succ) hn2
      have hstrict : points.Pairwise (· < ·) := by simpa [points] using wheelCandidateList_sorted hn2
      rw [show wheelGaps k.succ.succ = pointGapsList points ++ [wheelWrapGap k.succ.succ points] by
        simp [wheelGaps, points, hnonempty]] at hg
      rw [List.mem_append, List.mem_singleton] at hg
      cases hg with
      | inl hg_internal => exact pointGaps_pos points hstrict g hg_internal
      | inr hg_wrap =>
          subst g
          have hhead : points.headD 0 = 1 := by simpa [points, coprimeResidues] using coprimeResidues_head hn2
          have hlast : points.getLastD 0 < k.succ.succ := by simpa [points] using wheelCandidateList_getLastD_lt hnonempty
          change k.succ.succ + points.headD 0 - points.getLastD 0 > 0
          rw [hhead]; omega

/-- В одном периоде сумма всех wheel gaps равна модулю. -/
theorem wheelGaps_sum_eq_of_pos (n : Nat) (hpos : 0 < n) :
    (wheelGaps n).sum = n := by
  let points := wheelCandidateList n
  have hsorted : points.Pairwise (· <= ·) := by simp [points, wheelCandidateList]
  have htel := pointGapsList_sum_eq_last points hsorted
  have hnonempty : points ≠ [] := by
    rcases n with _ | k
    · omega
    · cases k with
      | zero =>
          have hmem : 0 ∈ wheelCandidateList 1 := by simp [wheelCandidateList, wheelCandidates]
          exact List.ne_nil_of_mem hmem
      | succ k =>
          have hlt : 1 < k.succ.succ := by omega
          have hmem : 1 ∈ wheelCandidateList k.succ.succ := by
            simp [wheelCandidateList, wheelCandidates, hlt]
          exact List.ne_nil_of_mem hmem
  have hlast : points.getLastD 0 < n := by simpa [points] using wheelCandidateList_getLastD_lt hnonempty
  have hgap : (pointGapsList points).sum + (n + points.headD 0 - points.getLastD 0) = n := by omega
  rw [show wheelGaps n = pointGapsList points ++ [wheelWrapGap n points] by
    simp [wheelGaps, points, hnonempty], List.sum_append, wheelWrapGap]
  change (pointGapsList points).sum + [n + points.headD 0 - points.getLastD 0].sum = n
  rw [show [n + points.headD 0 - points.getLastD 0].sum = n + points.headD 0 - points.getLastD 0 by simp]
  exact hgap

/-- Количество wheel gaps равно `Nat.totient n`. -/
theorem wheelGaps_length_eq_totient (n : Nat) :
    (wheelGaps n).length = Nat.totient n := by
  let points := wheelCandidateList n
  have hpoints : points.length = (wheelCandidates n).card := by simp [points, wheelCandidateList]
  have hcard : (wheelCandidates n).card = Nat.totient n := by
    rw [Nat.totient_eq_card_coprime]; rfl
  by_cases hempty : points = []
  · have htot : Nat.totient n = 0 := by rw [← hcard, ← hpoints]; simp [hempty]
    simp [wheelGaps, points, hempty, htot, pointGapsList]
  · have hposlen : 0 < points.length := List.length_pos_of_ne_nil hempty
    simp [wheelGaps, points, hempty, pointGapsList_length, hpoints, hcard]
    omega

/-- Средний gap как рациональное число равен `P_m / φ(P_m)`. -/
def primorialWheelMeanGap (m : Nat) : ℚ :=
  (primorial m : ℚ) / (Nat.totient (primorial m) : ℚ)

/-- Явная формула `φ(P_m)` через произведение `(p_i - 1)`. -/
theorem totient_primorial_explicit (m : Nat) :
    Nat.totient (primorial m) = (Finset.range m).prod (fun i => Nat.nth Nat.Prime i - 1) := by
  induction m with
  | zero => simp [primorial, Nat.totient_one]
  | succ m ih =>
    rw [primorial_succ, Nat.totient_mul]
    · rw [ih]
      have hp : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      rw [Nat.totient_prime hp]
      simp [Finset.prod_range_succ, Nat.mul_sub]
    · apply (Nat.coprime_prod_left_iff (t := Finset.range m)
        (s := fun i => Nat.nth Nat.Prime i) (x := Nat.nth Nat.Prime m)).mpr
      intro i hi
      have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
      have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
      exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)

/-- Гипотеза Мертенса для среднего primorial wheel gap. Открытая проблема. -/
def PrimorialWheelAverageGapMertensAsymptotic (γ : ℝ) : Prop :=
  Filter.Tendsto (fun m : Nat => (primorialWheelMeanGap m : ℝ) /
    (Real.exp γ * Real.log (Nat.nth Nat.Prime m))) Filter.atTop (nhds 1)

/-- Средний primorial wheel gap равен эйлерову произведению `∏ p_i/(p_i - 1)`. -/
theorem primorialWheelMeanGap_eq_euler_product (m : Nat) :
    primorialWheelMeanGap m =
    (Finset.range m).prod (fun i =>
      (Nat.nth Nat.Prime i : ℚ) / ((Nat.nth Nat.Prime i - 1 : ℕ) : ℚ)) := by
  unfold primorialWheelMeanGap
  rw [totient_primorial_explicit]
  unfold primorial
  push_cast
  rw [← Finset.prod_div_distrib]

/-- Средний primorial wheel gap строго возрастает. -/
theorem primorialWheelMeanGap_strictMono :
    StrictMono primorialWheelMeanGap := by
  intro n m hnm
  have h_key : ∀ k : Nat, primorialWheelMeanGap k < primorialWheelMeanGap (k + 1) := by
    intro k
    rw [primorialWheelMeanGap_eq_euler_product, primorialWheelMeanGap_eq_euler_product,
        Finset.prod_range_succ]
    have hge2 : 2 ≤ Nat.nth Nat.Prime k := (Nat.prime_nth_prime k).two_le
    have hp_ratio_gt1 : (1 : ℚ) <
        (Nat.nth Nat.Prime k : ℚ) / ((Nat.nth Nat.Prime k - 1 : ℕ) : ℚ) := by
      rw [lt_div_iff₀ (by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime k - 1)), one_mul]
      exact_mod_cast (by omega : (Nat.nth Nat.Prime k - 1 : ℕ) < Nat.nth Nat.Prime k)
    have h_prev_pos : (0 : ℚ) < (Finset.range k).prod (fun i =>
        (Nat.nth Nat.Prime i : ℚ) / ((Nat.nth Nat.Prime i - 1 : ℕ) : ℚ)) := by
      apply Finset.prod_pos
      intro i hi
      have hpi_ge2 : 2 ≤ Nat.nth Nat.Prime i := (Nat.prime_nth_prime i).two_le
      exact div_pos (by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime i))
        (by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime i - 1))
    nlinarith [hp_ratio_gt1, h_prev_pos]
  rcases Nat.exists_eq_add_of_lt hnm with ⟨k, hk⟩
  subst hk
  clear hnm
  induction k with
  | zero => exact h_key n
  | succ k ih => exact lt_trans ih (h_key (n + k + 1))

/-- Все coprime остатки чётного модуля нечётны: чётный остаток делит gcd. -/
lemma coprimeResidues_odd_of_even_mod {n : Nat} (hn : Even n) (_hnpos : 0 < n) :
    ∀ a ∈ wheelCandidateList n, Odd a := by
  intro a ha
  have ha_mem : a ∈ wheelCandidates n :=
    (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp ha
  have hcoprime : Nat.Coprime n a := (Finset.mem_filter.mp ha_mem).2
  by_contra hnot_odd
  rcases Nat.even_or_odd a with heven | hodd
  · obtain ⟨kn, hkn⟩ := hn
    obtain ⟨ka, hka⟩ := heven
    have h2n : (2 : Nat) ∣ n := by use kn; omega
    have h2a : (2 : Nat) ∣ a := by use ka; omega
    have h2gcd : (2 : Nat) ∣ Nat.gcd n a := Nat.dvd_gcd h2n h2a
    rw [Nat.coprime_iff_gcd_eq_one] at hcoprime
    rw [hcoprime] at h2gcd
    exact absurd h2gcd (by intro h; obtain ⟨k, hk⟩ := h; omega)
  · exact absurd hodd hnot_odd

/-- Разности между нечётными элементами — чётные. -/
lemma pointGapsList_even_of_all_odd {l : List Nat} (hall_odd : ∀ a ∈ l, Odd a) :
    ∀ g ∈ pointGapsList l, Even g := by
  induction l with
  | nil => intro g hg; simp [pointGapsList] at hg
  | cons a tail ih =>
    cases tail with
    | nil => intro g hg; simp [pointGapsList] at hg
    | cons b rest =>
      intro g hg
      simp only [pointGapsList, List.mem_cons] at hg
      cases hg with
      | inl hg =>
        subst g
        have ha : Odd a := hall_odd a (by simp)
        have hb : Odd b := hall_odd b (by simp)
        obtain ⟨ka, hka⟩ := ha
        obtain ⟨kb, hkb⟩ := hb
        exact ⟨kb - ka, by omega⟩
      | inr hg =>
        have htail_odd : ∀ x ∈ b :: rest, Odd x := by
          intro x hx; exact hall_odd x (List.mem_cons_of_mem _ hx)
        exact ih htail_odd g hg

/-- Wrap-around gap равен 2 для `n ≥ 2`: первый остаток 1, последний `n - 1`. -/
theorem wheelWrapGap_eq_two {n : Nat} (hn : 2 ≤ n) :
    wheelWrapGap n (wheelCandidateList n) = 2 := by
  have hhead : (wheelCandidateList n).headD 0 = 1 := by
    simpa [wheelCandidateList, coprimeResidues] using coprimeResidues_head hn
  have hcoprime : Nat.Coprime n (n - 1) := by
    have hn' : n = 1 + (n - 1) := by omega
    nth_rewrite 1 [hn']
    rw [Nat.coprime_add_self_left, Nat.coprime_one_left_iff]
    trivial
  have hnm1_mem : (n - 1 : Nat) ∈ wheelCandidateList n := by
    rw [wheelCandidateList, Finset.mem_sort, wheelCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hcoprime⟩
  have hnonempty : wheelCandidateList n ≠ [] :=
    coprimeResidues_ne_nil_of_ge_two hn
  have hsorted_le : (wheelCandidateList n).Pairwise (· ≤ ·) := by
    have := wheelCandidateList_sorted hn
    exact this.imp fun hlt => Nat.le_of_lt hlt
  have hlast : (wheelCandidateList n).getLastD 0 = n - 1 := by
    have hle_last : (wheelCandidateList n).getLastD 0 ≤ n - 1 := by
      have hlast_mem : (wheelCandidateList n).getLastD 0 ∈ wheelCandidateList n :=
        List.getLastD_mem_of_ne_nil _ hnonempty
      have hlast_mem' : (wheelCandidateList n).getLastD 0 ∈ wheelCandidates n :=
        (Finset.mem_sort (s := wheelCandidates n) (r := (· <= ·))).mp hlast_mem
      have hlast_lt : (wheelCandidateList n).getLastD 0 < n :=
        Finset.mem_range.mp (Finset.mem_filter.mp hlast_mem').1
      omega
    have hge_last : n - 1 ≤ (wheelCandidateList n).getLastD 0 :=
      List.getLastD_is_max_of_pairwise_le hsorted_le hnonempty _ hnm1_mem
    omega
  unfold wheelWrapGap
  rw [hhead, hlast]
  omega

/-- Все wheel gaps чётны при чётном модуле `n > 0`. -/
theorem wheelGaps_even_of_even_modulus {n : Nat} (hn : Even n) (hnpos : 0 < n) :
    ∀ g ∈ wheelGaps n, Even g := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    have hkpos : 0 < k := by nlinarith
    omega
  have hpoints_nonempty : wheelCandidateList n ≠ [] :=
    coprimeResidues_ne_nil_of_ge_two hn2
  let points := wheelCandidateList n
  have hgaps : wheelGaps n = pointGapsList points ++ [wheelWrapGap n points] := by
    simp [wheelGaps, points, hpoints_nonempty]
  rw [hgaps]
  intro g hg
  rw [List.mem_append, List.mem_singleton] at hg
  cases hg with
  | inl hg =>
    have hall_odd : ∀ a ∈ points, Odd a :=
      coprimeResidues_odd_of_even_mod hn hnpos
    exact pointGapsList_even_of_all_odd hall_odd g hg
  | inr hg =>
    subst g
    have hhead : points.headD 0 = 1 := by
      simpa [points, coprimeResidues] using coprimeResidues_head hn2
    have hlast_mem : points.getLastD 0 ∈ points :=
      List.getLastD_mem_of_ne_nil _ hpoints_nonempty
    have hodd_last : Odd (points.getLastD 0) :=
      coprimeResidues_odd_of_even_mod hn hnpos _ hlast_mem
    have hodd_head : Odd (points.headD 0) := by rw [hhead]; exact odd_one
    unfold wheelWrapGap
    obtain ⟨k, hk⟩ := hn
    obtain ⟨j, hj⟩ := hodd_last
    rw [hk, hhead, hj]
    exact ⟨k - j, by omega⟩

/-- Средний primorial wheel gap ≥ 2 для `m ≥ 1`. -/
theorem primorialWheelMeanGap_ge_two (m : Nat) (hm : 1 ≤ m) :
    (2 : ℚ) ≤ primorialWheelMeanGap m := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · -- m = 1 (h : 1 = m)
    subst h
    rw [primorialWheelMeanGap, primorial, Finset.prod_range_one]
    have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
    rw [hp0, Nat.totient_prime (by decide : Nat.Prime 2)]
    simp
  · -- 1 < m
    have hstrict := primorialWheelMeanGap_strictMono h
    have hbase : (2 : ℚ) ≤ primorialWheelMeanGap 1 := by
      rw [primorialWheelMeanGap, primorial, Finset.prod_range_one]
      have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
      rw [hp0, Nat.totient_prime (by decide : Nat.Prime 2)]
      simp
    linarith [hbase, hstrict]

/-- `primorial m` чётно для `m ≥ 1`: первый множитель равен 2. -/
theorem primorial_even (m : Nat) (hm : 1 ≤ m) : Even (primorial m) := by
  match m, hm with
  | 0, h => exact absurd h (by simp)
  | 1, _ =>
    rw [primorial, Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
    exact even_two
  | m + 2, _ =>
    rw [primorial_succ]
    exact Nat.even_mul.mpr (Or.inl (primorial_even (m + 1) (by omega)))

/-- Все wheel gaps для primorial `P_m` чётны при `m ≥ 1`. -/
theorem primorialWheelGaps_even (m : Nat) (hm : 1 ≤ m) :
    ∀ g ∈ wheelGaps (primorial m), Even g := by
  exact wheelGaps_even_of_even_modulus (primorial_even m hm) (primorial_pos m)

/-- Множество простых делителей `primorial m` — первые `m` простых. -/
theorem primeFactors_primorial (m : Nat) (hm : 0 < m) :
    Nat.primeFactors (primorial m) =
      (Finset.range m).image (fun i => Nat.nth Nat.Prime i) := by
  induction m with
  | zero => exact absurd hm (by simp)
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
      have hp2 : Nat.Prime 2 := by decide
      unfold primorial
      rw [Finset.prod_range_one, hp0, Finset.range_one, Finset.image_singleton, hp0]
      ext q
      simp only [Finset.mem_singleton]
      constructor
      · intro hmem
        rw [Nat.mem_primeFactors] at hmem
        exact (Nat.prime_dvd_prime_iff_eq hmem.1 hp2).mp hmem.2.1
      · rintro rfl; exact Nat.mem_primeFactors.mpr ⟨hp2, dvd_rfl, hp2.ne_zero⟩
    · have hmpos : 0 < m := by omega
      rw [primorial_succ]
      have hcoprime : Nat.Coprime (primorial m) (Nat.nth Nat.Prime m) := by
        unfold primorial
        rw [Nat.coprime_prod_left_iff]
        intro i hi
        have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
        have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
        have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
        exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)
      rw [Nat.primeFactors_mul (primorial_pos m).ne' (Nat.prime_nth_prime m).pos.ne',
          ih hmpos]
      have hpf_pm : Nat.primeFactors (Nat.nth Nat.Prime m) = {Nat.nth Nat.Prime m} := by
        have hpm := Nat.prime_nth_prime m
        ext q
        simp only [Finset.mem_singleton]
        constructor
        · intro hmem
          rw [Nat.mem_primeFactors] at hmem
          exact (Nat.prime_dvd_prime_iff_eq hmem.1 hpm).mp hmem.2.1
        · rintro rfl; exact Nat.mem_primeFactors.mpr ⟨hpm, dvd_rfl, hpm.ne_zero⟩
      have hrange : Finset.range (m + 1) = insert m (Finset.range m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_range]
        constructor
        · intro h
          by_cases hx : x = m
          · exact Or.inl hx
          · exact Or.inr (by omega)
        · rintro (rfl | h)
          · omega
          · omega
      rw [hpf_pm, hrange, Finset.image_insert]
      exact Finset.union_comm _ _

/-- Gap 2 всегда присутствует в primorial wheel (как wrap-around). -/
theorem primorialWheel_gap_two_appears (m : Nat) (hm : 1 ≤ m) :
    2 ∈ wheelGaps (primorial m) := by
  have heven : Even (primorial m) := primorial_even m hm
  have h2dvd : 2 ∣ primorial m := by rcases heven with ⟨k, hk⟩; use k; omega
  have hpm_ge2 : 2 ≤ primorial m := Nat.le_of_dvd (primorial_pos m) h2dvd
  have hwrap : wheelWrapGap (primorial m) (wheelCandidateList (primorial m)) = 2 :=
    wheelWrapGap_eq_two hpm_ge2
  have hpoints_ne : wheelCandidateList (primorial m) ≠ [] :=
    coprimeResidues_ne_nil_of_ge_two hpm_ge2
  rw [wheelGaps, if_neg hpoints_ne]
  rw [List.mem_append, List.mem_singleton]
  exact Or.inr hwrap.symm

end
end PrimeGaps

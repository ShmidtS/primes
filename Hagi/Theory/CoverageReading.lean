/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.AdaptiveContext

set_option relaxedAutoImplicit false

/-!
# CoverageReading — полное чтение входа окнами (wave228)

Мост к HAGI_v2 `CertifiedStepLM._read_all_windows` (hagi/lm.py,
commit b7f7f64): промпт читается ЦЕЛИКОМ скользящими окнами — окно k,
шаг k (без пропусков), плюс суффикс-окно [n-k, n), если последняя
решётка ещё не накрывает суффикс; при n ≤ k — одно окно с паддингом.
generate_auto агрегирует logits по ВСЕМ окнам.

Честная граница исходника: финальное усечение windows[-max_span:]
(max_span = 64) оставляет только ПОСЛЕДНИЕ окна. «Каждый байт
прочитан» гарантирован кодом лишь пока окон не больше max_span;
иначе головные окна (включая окно 0) отбрасываются, и байт 0
остаётся непрочитанным — формализуем это как негативную теорему.

Fresh-minimal инвариант (KISS, 2 теоремы): список стартов окон как
чистая функция (covStarts), побайтовое покрытие интервала [s, s+k),
усечение drop (len - m) как точный аналог среза [-m:]. Частичное
падди-представление окна опущено честно: покрытие описано по
ИНТЕРВАЛАМ стартов, байтовое содержимое окон не моделируется.

- `covStarts_covers` — полный список стартов покрывает каждый байт
  [0, n) (union интервалов = весь диапазон; полное чтение входа);
- `covStarts_trunc_uncovered_zero` — если окон больше m, усечение
  до последних m отбрасывает старт 0 ⇒ байт 0 не покрыт никем
  (граница заявки «every byte, ≤64 windows»).
- второй namespace модуля `Hagi.Theory.WindowTradeoff`:
  certified trade-off ширины окна (totalCost = ⌈n/w⌉ · c(w), режимы
  fixed / linear / mixed) — опирается на `hier_total_min` ниже.

-/

namespace Hagi.Theory.CoverageReading

/-- Старты окон чтения _read_all_windows: при n ≤ k одно окно
(старт 0, с паддингом); иначе решётка 0, k, 2k, … ≤ n-k плюс
суффикс-окно n-k, если решётка его ещё не содержит (k ∣ n-k). -/
def covStarts (n k : ℕ) : List ℕ :=
  if n ≤ k then [0]
  else (List.range ((n - k) / k + 1)).map (fun j => j * k) ++
       (if k ∣ n - k then [] else [n - k])

/-- **Полное покрытие входа**: старты covStarts покрывают каждый
байт i < n некоторым окном [s, s + k) — union интервалов стартов
содержит весь диапазон [0, n) (каждый байт промпта прочитан,
contiguous coverage, ни одного пропуска). -/
theorem covStarts_covers (n k : ℕ) (hk : 0 < k) :
    ∀ i < n, ∃ s ∈ covStarts n k, s ≤ i ∧ i < s + k := by
  intro i hi
  have hk1 : 1 ≤ k := hk
  by_cases hnk : n ≤ k
  · exact ⟨0, by rw [covStarts, if_pos hnk]; simp, Nat.zero_le i, by omega⟩
  · by_cases hlast : i < n - k
    · -- байт решётки: окно j*k, j = i/k (j ≤ (n-k)/k)
      have hmem : i / k * k ∈ (List.range ((n - k) / k + 1)).map (fun j => j * k) := by
        refine List.mem_map.mpr ⟨i / k, List.mem_range.mpr ?_, rfl⟩
        have hle : i / k ≤ (n - k) / k :=
          Nat.div_le_div_right (by omega : i ≤ n - k)
        omega
      refine ⟨i / k * k, ?_, Nat.div_mul_le_self i k, ?_⟩
      · rw [covStarts, if_neg hnk]
        by_cases hd : k ∣ n - k
        · rw [if_pos hd]; simpa only [List.mem_append] using Or.inl hmem
        · rw [if_neg hd]; simpa only [List.mem_append] using Or.inl hmem
      · have hdmod := Nat.div_add_mod i k
        have hltmod := Nat.mod_lt i hk
        rw [Nat.mul_comm] at hdmod
        have hsucc : i / k * k + k = (i / k + 1) * k := by ring
        omega
    · -- хвостовой байт: суффикс-окно [n-k, n)
      refine ⟨n - k, ?_, by omega, by omega⟩
      rw [covStarts, if_neg hnk]
      by_cases hd : k ∣ n - k
      · rw [if_pos hd]
        have hq : (n - k) / k * k = n - k := by
          rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hd
        simpa only [List.mem_append] using Or.inl
          (List.mem_map.mpr ⟨(n - k) / k, List.mem_range.mpr (Nat.lt_succ_self _), hq⟩)
      · rw [if_neg hd]
        simpa only [List.mem_append] using Or.inr (by simp)

private theorem covStarts_tail_pos (n k : ℕ) (hk : 0 < k) :
    ∀ x ∈ (covStarts n k).drop 1, 0 < x := by
  by_cases hnk : n ≤ k
  · rw [covStarts, if_pos hnk]; simp
  · have hnk' : ¬(n ≤ k) := hnk
    intro x hx
    rw [covStarts, if_neg hnk', List.drop_append] at hx
    have hz : 1 - ((List.range ((n - k) / k + 1)).map (fun j => j * k)).length
        = 0 := by simp
    rw [hz, List.drop_zero, List.mem_append] at hx
    rcases hx with h | h
    · obtain ⟨i, hig⟩ := List.mem_iff_get.mp h
      have hlen2 : 1 + i.val < (List.map (fun j => j * k)
          (List.range ((n - k) / k + 1))).length := by
        have hlt := i.isLt
        simp only [List.length_drop] at hlt
        omega
      have hd1 : (List.map (fun j => j * k)
          (List.range ((n - k) / k + 1)))[1 + i.val]'hlen2 = x := by
        rw [← List.getElem_drop (i := 1) (j := i.val) (h := i.isLt)]
        exact hig
      have hval : (List.map (fun j => j * k)
          (List.range ((n - k) / k + 1)))[1 + i.val]'hlen2 = (1 + i.val) * k := by
        rw [List.getElem_map]
        have hlen3 : 1 + i.val < (List.range ((n - k) / k + 1)).length := by
          simpa using hlen2
        rw [show (List.range ((n - k) / k + 1))[1 + i.val] = 1 + i.val from
          List.getElem_range hlen3]
      rw [hval] at hd1
      have hik : (1 + i.val) * k = k + i.val * k := by ring
      omega
    · split at h
      · exact absurd h (by simp)
      · simp only [List.mem_singleton] at h
        omega

/-- **Граница max_span**: если стартов больше m, усечение до
последних m (срез windows[-m:] = drop (len - m)) удаляет старт 0,
и байт 0 не покрыт ни одним оставшимся окном. Честная граница
заявления wave228 «every byte read, ≤64 windows»: при числе окон
больше max_span полное чтение НЕ гарантируется — дыра в голове. -/
theorem covStarts_trunc_uncovered_zero (n k m : ℕ) (hk : 0 < k)
    (hbig : m < (covStarts n k).length) :
    ¬ ∃ s ∈ (covStarts n k).drop ((covStarts n k).length - m),
      s ≤ 0 ∧ 0 < s + k := by
  rintro ⟨s, hs, hsle, hsitv⟩
  have hd : 1 ≤ (covStarts n k).length - m := by omega
  -- drop d ⊆ drop 1 при d ≥ 1
  have hsub : ((covStarts n k).drop ((covStarts n k).length - m))
      ⊆ (covStarts n k).drop 1 := by
    intro x hx
    have hrew : (covStarts n k).drop ((covStarts n k).length - m)
        = ((covStarts n k).drop 1).drop (((covStarts n k).length - m) - 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [hrew] at hx
    exact List.drop_subset _ _ hx
  have hs' : s ∈ (covStarts n k).drop 1 := hsub hs
  have h0 : 0 ∈ (covStarts n k).drop 1 := by
    have hs0 : s = 0 := by omega
    rwa [hs0] at hs'
  have := covStarts_tail_pos n k hk 0 h0
  omega


/-!
## adaptive span — параметрический шаг (замыкание негатива)

Код-импликация `covStarts_trunc_uncovered_zero`: при переполнении
(окон > max_span) НЕ усекать хвост слепо (байт 0 теряется), а
ПЕРЕСЧИТАТЬ старты с бОльшим шагом s ≤ w — покрытие сохраняется,
число окон входит в бюджет. Точное условие покрытия при окне
длины w и шаге s: 0 < s ≤ w (соседние окна перекрываются/
стыкуются, суффикс-фоллбек закрывает хвост); при s > w между
окнами остаётся дыра (bench-witness).
-/

/-- Обобщение covStarts: окно длины w, шаг решётки s
(covStarts n k = covStartsStep n k k — tiling-частный случай).
При n ≤ w одно окно с паддингом; иначе решётка 0, s, 2s, … ≤ n−w
плюс суффикс-окно n−w при s ∤ n−w. -/
def covStartsStep (n w s : ℕ) : List ℕ :=
  if n ≤ w then [0]
  else (List.range ((n - w) / s + 1)).map (fun j => j * s) ++
       (if s ∣ n - w then [] else [n - w])

/-- covStarts — частный случай covStartsStep при шаге = длине
окна (def-eq, без доказательства содержимого). -/
theorem covStarts_eq_step (n k : ℕ) : covStarts n k = covStartsStep n k k := rfl

/-- **Adaptive span, покрытие**: старты covStartsStep покрывают
каждый байт i < n окном [t, t + w), если шаг строго положителен
и НЕ превосходит длины окна (ТОЧНОЕ условие: s ≤ w — соседние
окна перекрываются/стыкуются; при s > w между окнами дыра). -/
theorem covStartsStep_covers (n w s : ℕ) (hs : 0 < s) (hsw : s ≤ w) :
    ∀ i < n, ∃ t ∈ covStartsStep n w s, t ≤ i ∧ i < t + w := by
  intro i hi
  by_cases hnw : n ≤ w
  · exact ⟨0, by rw [covStartsStep, if_pos hnw]; simp, Nat.zero_le i, by omega⟩
  · by_cases hlast : i < n - w
    · -- байт решётки: окно j*s, j = i/s (j ≤ (n-w)/s)
      have hmem : i / s * s ∈ (List.range ((n - w) / s + 1)).map (fun j => j * s) := by
        refine List.mem_map.mpr ⟨i / s, List.mem_range.mpr ?_, rfl⟩
        have hle : i / s ≤ (n - w) / s := Nat.div_le_div_right (by omega)
        omega
      refine ⟨i / s * s, ?_, Nat.div_mul_le_self i s, ?_⟩
      · rw [covStartsStep, if_neg hnw]
        by_cases hd : s ∣ n - w
        · rw [if_pos hd]; simpa only [List.mem_append] using Or.inl hmem
        · rw [if_neg hd]; simpa only [List.mem_append] using Or.inl hmem
      · have hdm := Nat.div_add_mod i s
        have hltm := Nat.mod_lt i hs
        rw [Nat.mul_comm] at hdm
        have hsucc : i / s * s + w = i / s * s + s + (w - s) := by omega
        omega
    · -- хвостовой байт: суффикс-окно [n-w, n-w+w)
      refine ⟨n - w, ?_, by omega, by omega⟩
      rw [covStartsStep, if_neg hnw]
      by_cases hd : s ∣ n - w
      · rw [if_pos hd]
        have hq : (n - w) / s * s = n - w := by
          rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hd
        simpa only [List.mem_append] using Or.inl
          (List.mem_map.mpr ⟨(n - w) / s, List.mem_range.mpr (Nat.lt_succ_self _), hq⟩)
      · rw [if_neg hd]
        simpa only [List.mem_append] using Or.inr (by simp)

/-- **Adaptive span, бюджет**: при n > w стартов не больше
(n−w)/s + 2 (решётка (n−w)/s+1 + ≤1 суффикс) — условие входа
в max_span без всякого усечения. -/
theorem covStartsStep_len_le (n w s : ℕ) (_hs : 0 < s) (hw : w < n) :
    (covStartsStep n w s).length ≤ (n - w) / s + 2 := by
  rw [covStartsStep, if_neg (by omega : ¬ n ≤ w), List.length_append,
    List.length_map, List.length_range]
  by_cases hd : s ∣ n - w <;> simp [hd]

/-- **Замыкание негатива **: адаптивный шаг s (0 < s ≤ w,
бюджет (n−w)/s + 2 ≤ m) даёт ПОЛНОЕ покрытие [0, n) окнами
длины w И число окон ≤ m — усечение windows[-max_span:]
не срабатывает, старт 0 (и каждый байт) остаётся прочитанным.
Contrast: covStarts_trunc_uncovered_zero — слепое усечение при
переполнении теряет байт 0; пересчёт шага вместо усечения —
coverage-preserving стратегия. -/
theorem covStartsStep_adaptive_covers (n w s m : ℕ) (hs : 0 < s)
    (hsw : s ≤ w) (hbudget : (n - w) / s + 2 ≤ m) :
    (covStartsStep n w s).length ≤ m ∧
    ∀ i < n, ∃ t ∈ covStartsStep n w s, t ≤ i ∧ i < t + w := by
  refine ⟨?_, covStartsStep_covers n w s hs hsw⟩
  by_cases hw : w < n
  · exact Nat.le_trans (covStartsStep_len_le n w s hs hw) hbudget
  · have h1 : (covStartsStep n w s).length = 1 := by
      rw [covStartsStep, if_pos (by omega : n ≤ w)]; simp
    have h2 : n - w = 0 := by omega
    rw [h2] at hbudget
    have : 2 ≤ m := by simpa using hbudget
    omega


/-!
## иерархические окна — снятие INFEASIBLE-границы adaptive span

Одноуровневая граница бюджет (n−w)/s+2 ≤ m при s ≤ w даёт
n ≤ w + s·(m−2) ≤ w·(m−1) (= 4032 при w = m = 64) — дальше окон
больше max_span, полному чтению «не хватает» окон. Решение —
2 уровня: вход режется на блоки длины B; внутри каждого блока
covStartsStep с окном w и шагом s; блоки обрабатываются
ПОСЛЕДОВАТЕЛЬНО (streaming-модель): в памяти одновременно только
окна ТЕКУЩЕГО блока ⇒ peak-память ≤ m окон на блок, а полное
покрытие [0, n) сохраняется для ЛЮБОГО n (блоков ⌈n/B⌉ — не
ограничено). Честно: peak ≠ total — суммарное число окон растёт
как ⌈n/B⌉·(≤ m); теоремы ниже про peak (окон на блок), не про
total. Точный бюджет: при s = w, B = w·(m−1) пик (B−w)/s+2 = m.
Bench-witness: n = 8128 (> 4032) покрыт;
одноуровневый covStartsStep 8128 64 64 даёт 128 окон > 64.
-/

/-- Длина блока j: ℓ_j = min B (n − j·B) — полный блок B,
хвостовой короче (последний блок). -/
def hierBlockLen (n B j : ℕ) : ℕ := min B (n - j * B)

/-- Старты иерархического чтения: плоская конкатенация поблочных
стартов covStartsStep (блок j сдвигает свои старты на j·B);
numBlocks = ⌈n/B⌉ блоков. -/
def hierStarts (n B w s : ℕ) : List ℕ :=
  (((List.range ((n + B - 1) / B)).map (fun j =>
    ((covStartsStep (hierBlockLen n B j) w s).map (fun t => j * B + t)))).flatten)

/-- **Иерархическое покрытие ЛЮБОГО n** (снятие INFEASIBLE-границы
): без верхней границы на n старты hierStarts покрывают
каждый байт i < n окном [t, t + w) при 0 < s ≤ w и 0 < B —
байты блока j = i/B покрываются окнами этого блока
(covStartsStep_covers поблочно), число блоков ⌈n/B⌉ не
ограничено. -/
theorem hier_covers_any_n (n B w s : ℕ) (hB : 0 < B) (hs : 0 < s) (hsw : s ≤ w) :
    ∀ i < n, ∃ t ∈ hierStarts n B w s, t ≤ i ∧ i < t + w := by
  intro i hi
  have hdm : (i / B) * B + i % B = i := by
    have h := Nat.div_add_mod i B
    rw [Nat.mul_comm] at h
    exact h
  have hm : i % B < B := Nat.mod_lt i hB
  have hjle : (i / B) * B ≤ i := Nat.div_mul_le_self i B
  have hjlt : i / B < (n + B - 1) / B := by
    rw [Nat.lt_div_iff_mul_lt hB]
    have hring : (i / B + 1) * B = (i / B) * B + B := by ring
    omega
  have hℓ : i - (i / B) * B < hierBlockLen n B (i / B) := by
    unfold hierBlockLen
    rw [Nat.min_def]
    split <;> omega
  obtain ⟨t', ht', ht'le, ht'lt⟩ :=
    covStartsStep_covers (hierBlockLen n B (i / B)) w s hs hsw (i - (i / B) * B) hℓ
  refine ⟨(i / B) * B + t', ?_, by omega, by omega⟩
  refine List.mem_flatten.mpr
    ⟨(covStartsStep (hierBlockLen n B (i / B)) w s).map (fun t => (i / B) * B + t), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨i / B, List.mem_range.mpr hjlt, rfl⟩
  · exact List.mem_map.mpr ⟨t', ht', rfl⟩

/-- **Peak-бюджет (streaming)**: при 0 < s ≤ w, w ≤ B и бюджете
(B−w)/s + 2 ≤ m в списке КАЖДОГО блока не больше m окон — блоки
обрабатываются последовательно, одновременно в памяти ≤ m окон
(peak ≠ total: суммарно ⌈n/B⌉·(≤ m), с n растёт только total).
Точный выбор: s = w, B = w·(m−1) ⇒ (B−w)/s + 2 = m окон на блок
при любом n (w = m = 64: B = 4032, ровно 63–64 окна на блок,
bench-witness). -/
theorem hier_peak_window_budget (n B w s m : ℕ) (hs : 0 < s) (hsw : s ≤ w)
    (hwB : w ≤ B) (hbudget : (B - w) / s + 2 ≤ m) :
    ∀ j ∈ List.range ((n + B - 1) / B),
      ((covStartsStep (hierBlockLen n B j) w s).map (fun t => j * B + t)).length ≤ m := by
  intro j _hj
  have hℓ : hierBlockLen n B j ≤ B := Nat.min_le_left B (n - j * B)
  by_cases hw : hierBlockLen n B j ≤ w
  · have hlen1 : ((covStartsStep (hierBlockLen n B j) w s).map (fun t => j * B + t)).length = 1 := by
      simp only [List.length_map]
      rw [covStartsStep, if_pos hw]
      simp
    have h4 : 0 ≤ (B - w) / s := Nat.zero_le _
    have h2 : 2 ≤ (B - w) / s + 2 := by omega
    have h3 := Nat.le_trans h2 hbudget
    omega
  · have hlen := covStartsStep_len_le (hierBlockLen n B j) w s hs (by omega)
    simp only [List.length_map] at hlen ⊢
    have h5 : (hierBlockLen n B j - w) / s ≤ (B - w) / s :=
      Nat.div_le_div_right (by omega)
    omega


/-!
## оптимальность B — TOTAL окон иерархии

 честно разделил peak (≤ m окон на блок, streaming) и total
(⌈n/B⌉·(≤ m), растёт с n). Здесь закрывается вопрос: минимизирует ли выбор s = w,
B = w·(m−1) суммарное число
окон при ограничении peak ≤ m. Ответ: при s = w и w ∣ B total
равен ⌈n/w⌉ — ИНФОРМАЦИОННОМУ МИНИМУМУ (k окон длины w покрывают
не более k·w байтов) — и НЕ зависит от B: внутреннего оптимума
B* нет, выбор certified (любое B, кратное w, в допустимой
области B ≤ w + s·(m−1) даёт тот же минимальный total; bench-witness).
-/

/-- Точное число стартов при шаге = длине окна (tiling): при
0 < ℓ список `covStartsStep` ℓ w w имеет ровно ⌈ℓ/w⌉ = (ℓ+w−1)/w
элементов — решётка шага w без суффикс-дубля при w ∣ (ℓ−w),
с суффиксом иначе; при ℓ ≤ w одно окно. -/
theorem covStartsStep_len_tiling (l w : ℕ) (hw : 0 < w) (hl : 0 < l) :
    (covStartsStep l w w).length = (l + w - 1) / w := by
  by_cases hle : l ≤ w
  · rw [covStartsStep, if_pos hle]
    simp only [List.length_singleton]
    exact (Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)).symm
  · have hw' : w < l := by omega
    rw [covStartsStep, if_neg (by omega : ¬ l ≤ w)]
    by_cases hd : w ∣ l - w
    · rw [if_pos hd]
      simp only [List.length_append, List.length_map, List.length_range, List.length_nil,
        Nat.add_zero]
      have hq : w * ((l - w) / w) = l - w := Nat.mul_div_cancel' hd
      have e1 : ((l - w) / w + 1) * w = w * ((l - w) / w) + 1 * w := by ring
      have e2 : ((l - w) / w + 2) * w = w * ((l - w) / w) + 2 * w := by ring
      have hval : (l + w - 1) / w = (l - w) / w + 1 :=
        Nat.div_eq_of_lt_le (k := (l - w) / w + 1)
          (by rw [e1, hq]; omega) (by rw [e2, hq]; omega)
      omega
    · rw [if_neg hd]
      simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]
      have hdvd : (l - w) % w ≠ 0 := fun h0 => hd (Nat.dvd_iff_mod_eq_zero.mpr h0)
      have hdm : w * ((l - w) / w) + (l - w) % w = l - w := Nat.div_add_mod _ _
      have hmod : (l - w) % w < w := Nat.mod_lt _ hw
      have hq2 : w * ((l - w) / w) = l - w - (l - w) % w := by omega
      have e1 : ((l - w) / w + 2) * w = w * ((l - w) / w) + 2 * w := by ring
      have e2 : ((l - w) / w + 3) * w = w * ((l - w) / w) + 3 * w := by ring
      have hval : (l + w - 1) / w = (l - w) / w + 2 :=
        Nat.div_eq_of_lt_le (k := (l - w) / w + 2)
          (by rw [e1, hq2]; omega) (by rw [e2, hq2]; omega)
      omega

/-- Телескоп-сумма поблочных tiling-счётов: при B = w·c сумма
⌈min B (m − j·B)/w⌉ по j < k (m ≤ k·B) равна ⌈m/w⌉ — полные блоки
дают ровно c = B/w каждый, хвостовой добивает остаток. -/
theorem hier_blocks_sum_tiling (B w c k : ℕ) (hw : 0 < w) (hB : B = w * c) :
    ∀ m ≤ k * B,
      ((List.range k).map (fun j => (min B (m - j * B) + w - 1) / w)).sum
        = (m + w - 1) / w := by
  induction k with
  | zero =>
    intro m hm
    rw [Nat.zero_mul] at hm
    simp only [List.range_zero, List.map_nil, List.sum_nil]
    have h0 : (0 + w - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
    have hme : m = 0 := by omega
    subst hme
    rw [h0]
  | succ k ih =>
    intro m hm
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton]
    by_cases hfit : m ≤ k * B
    · have hz : min B (m - k * B) + w - 1 = w - 1 := by
        simp only [Nat.sub_eq_zero_of_le hfit]
        simp
      have h0 : (w - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
      rw [hz, h0]
      simp only [List.sum_singleton]
      exact ih m hfit
    · have hfull : ∀ j ∈ List.range k, (min B (m - j * B) + w - 1) / w = c := by
        intro j hj
        have hjk : j < k := List.mem_range.mp hj
        have ej : (j + 1) * B = j * B + B := by ring
        have ek : (k + 1) * B = k * B + B := by ring
        have hmul : (j + 1) * B ≤ k * B := Nat.mul_le_mul_right B (by omega)
        have hleB : B ≤ m - j * B := by omega
        rw [min_eq_left hleB, hB]
        have e : w * c + w - 1 = (w - 1) + w * c := by omega
        rw [e, Nat.add_mul_div_left (w - 1) c hw, Nat.div_eq_of_lt (by omega : w - 1 < w),
          Nat.zero_add]
      rw [List.map_congr_left hfull]
      have hsum : ((List.range k).map (fun _ => c)).sum = k * c := by simp
      rw [hsum]
      have hle : m - k * B ≤ B := by
        have ek : (k + 1) * B = k * B + B := by ring
        omega
      rw [min_eq_right hle]
      simp only [List.sum_singleton]
      have e3 : k * B = w * (k * c) := by rw [hB]; ring
      have eM : m + w - 1 = (m - k * B + w - 1) + w * (k * c) := by omega
      rw [eM, Nat.add_mul_div_left _ (k * c) hw]
      omega

/-- Общий upper bound TOTAL: суммарное число окон иерархии не
превосходит ⌈n/B⌉·((B−w)/s + 2) — per-block бюджет
умноженный на число блоков (peak-оценка, честная по total). -/
theorem hier_total_formula (n B w s : ℕ) (hB : 0 < B) (hs : 0 < s) (hsw : s ≤ w) (hwB : w ≤ B) :
    (hierStarts n B w s).length ≤ ((n + B - 1) / B) * ((B - w) / s + 2) := by
  unfold hierStarts hierBlockLen
  rw [List.length_flatten, List.map_map]
  have hblk : ∀ j ∈ List.range ((n + B - 1) / B),
      List.length (List.map (fun t => j * B + t) (covStartsStep (min B (n - j * B)) w s))
        ≤ (B - w) / s + 2 := by
    intro j _
    rw [List.length_map]
    by_cases hw : min B (n - j * B) ≤ w
    · rw [covStartsStep, if_pos hw]; simp
    · have hmB : min B (n - j * B) ≤ B := Nat.min_le_left _ _
      have hlen := covStartsStep_len_le (min B (n - j * B)) w s hs (by omega)
      have hmono := Nat.div_le_div_right (c := s) (by omega : min B (n - j * B) - w ≤ B - w)
      omega
  refine (List.sum_le_sum hblk).trans ?_
  simp

/-- ТОЧНЫЙ total при шаге = окну и B, кратном w: суммарное число
окон `hierStarts` n B w w равно ⌈n/w⌉ — НЕ зависит от B (любое
допустимое B даёт один и тот же total; телескоп-сумма
`hier_blocks_sum_tiling`). -/
theorem hier_total_min (n B w : ℕ) (hw : 0 < w) (hB : 0 < B) (hdiv : w ∣ B) :
    (hierStarts n B w w).length = (n + w - 1) / w := by
  obtain ⟨c, hc⟩ := hdiv
  unfold hierStarts hierBlockLen
  rw [List.length_flatten, List.map_map]
  have hjn : ∀ j ∈ List.range ((n + B - 1) / B), j * B < n := by
    intro j hj
    have hjk : j < (n + B - 1) / B := List.mem_range.mp hj
    by_contra hcon
    push_neg at hcon
    have e : (j + 1) * B = j * B + B := by ring
    have hlt : (n + B - 1) / B < j + 1 := (Nat.div_lt_iff_lt_mul hB).mpr (by omega)
    omega
  have hterm : ∀ j ∈ List.range ((n + B - 1) / B),
      (List.map (fun t => j * B + t) (covStartsStep (min B (n - j * B)) w w)).length
        = (min B (n - j * B) + w - 1) / w := by
    intro j hj
    rw [List.length_map]
    exact covStartsStep_len_tiling _ w hw (by have := hjn j hj; omega)
  show ((List.range ((n + B - 1) / B)).map
    (fun j => (List.map (fun t => j * B + t) (covStartsStep (min B (n - j * B)) w w)).length)).sum
    = (n + w - 1) / w
  rw [List.map_congr_left hterm]
  have hfit : n ≤ ((n + B - 1) / B) * B := by
    have hlt : (n + B - 1) < (((n + B - 1) / B) + 1) * B :=
      (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self _)
    have e : (((n + B - 1) / B) + 1) * B = ((n + B - 1) / B) * B + B := by ring
    omega
  exact hier_blocks_sum_tiling B w c ((n + B - 1) / B) hw hc n hfit

/-- Информационный floor: любой список стартов, покрывающий
каждый байт i < n окном [t, t+w), имеет длину не меньше n/w —
k окон покрывают не более k·w байтов (инъекция i ↦ (t, i − t) в
пары «окно × сдвиг»; Ico-интервалы длины w). -/
theorem hier_total_floor (L : List ℕ) (w n : ℕ) (hw : 0 < w)
    (hcover : ∀ i < n, ∃ t ∈ L, t ≤ i ∧ i < t + w) :
    n ≤ L.length * w := by
  classical
  have hico : ∀ t : ℕ, (Finset.Ico t (t + w)).card ≤ w := by
    intro t
    have hmaps : Set.MapsTo (fun i => i - t) ↑(Finset.Ico t (t + w)) ↑(Finset.range w) := by
      intro i hi
      refine Finset.mem_range.mpr ?_
      have h := Finset.mem_Ico.mp hi
      show i - t < w
      omega
    have hinj : Set.InjOn (fun i => i - t) ↑(Finset.Ico t (t + w)) := by
      intro a ha b hb hab
      have hka := Finset.mem_Ico.mp ha
      have hkb := Finset.mem_Ico.mp hb
      have hab' : a - t = b - t := hab
      omega
    have hcard := Finset.card_le_card_of_injOn (fun i => i - t) hmaps hinj
    simpa using hcard
  have hsub : Finset.range n ⊆ L.toFinset.biUnion (fun t => Finset.Ico t (t + w)) := by
    intro i hi
    obtain ⟨t, ht, hle, hlt⟩ := hcover i (Finset.mem_range.mp hi)
    exact Finset.mem_biUnion.mpr ⟨t, List.mem_toFinset.mpr ht, Finset.mem_Ico.mpr ⟨hle, by omega⟩⟩
  calc n = (Finset.range n).card := (Finset.card_range n).symm
    _ ≤ (L.toFinset.biUnion (fun t => Finset.Ico t (t + w))).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ L.toFinset, (Finset.Ico t (t + w)).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ L.toFinset, w := Finset.sum_le_sum (fun t _ => hico t)
    _ = L.toFinset.card * w := by simp
    _ ≤ L.length * w := Nat.mul_le_mul_right _ (List.toFinset_card_le L)

/-- **Оптимальность иерархии по total** (замыкание вопроса):
при s = w и w ∣ B иерархическое чтение даёт total ровно ⌈n/w⌉ —
информационный минимум из `hier_total_floor`: никакое покрытие
[0, n) окнами длины w не использует меньше ⌈n/w⌉ окон. Выбор
 (s = w, B = w·(m−1)) certified: внутреннего оптимума B нет —
total одинаков для любого допустимого B, кратного w. -/
theorem hier_optimal (n B w : ℕ) (hw : 0 < w) (hB : 0 < B) (hdiv : w ∣ B) :
    (hierStarts n B w w).length = (n + w - 1) / w ∧
      ∀ L : List ℕ, (∀ i < n, ∃ t ∈ L, t ≤ i ∧ i < t + w) →
        (n + w - 1) / w ≤ L.length := by
  refine ⟨hier_total_min n B w hw hB hdiv, ?_⟩
  intro L hc
  have hf := hier_total_floor L w n hw hc
  have hq1 : w * ((n + w - 1) / w) ≤ n + w - 1 := Nat.mul_div_le _ _
  have e4 : w * (L.length + 1) = L.length * w + w := by ring
  have hlt : w * ((n + w - 1) / w) < w * (L.length + 1) := by omega
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left hlt)

end Hagi.Theory.CoverageReading

namespace Hagi.Theory.WindowTradeoff

open Hagi.Theory.CoverageReading

/-- Анти-монотонность потолка деления: при 0 < w ≤ w' потолок
⌈n/w'⌉ ≤ ⌈n/w⌉ — более широкое окно требует не БОЛЬШЕ чтений
(k = ⌈n/w⌉ даёт n ≤ k·w ≤ k·w', значит ⌈n/w'⌉ < k+1). Ядро
режима (a) `windowCost_fixed_mono`. -/
theorem ceil_div_anti (n w w' : ℕ) (hw : 0 < w) (hw' : 0 < w') (hle : w ≤ w') :
    (n + w' - 1) / w' ≤ (n + w - 1) / w := by
  have hkm : w * ((n + w - 1) / w) + (n + w - 1) % w = n + w - 1 :=
    Nat.div_add_mod (n + w - 1) w
  have hmod : (n + w - 1) % w < w := Nat.mod_lt _ hw
  have hnle : n ≤ w * ((n + w - 1) / w) := by omega
  have hqw : w * ((n + w - 1) / w) ≤ ((n + w - 1) / w) * w' := by
    have h := Nat.mul_le_mul_right ((n + w - 1) / w) hle
    simpa [Nat.mul_comm] using h
  have hring : ((n + w - 1) / w + 1) * w' = ((n + w - 1) / w) * w' + 1 * w' := by
    ring
  have hlt : n + w' - 1 < ((n + w - 1) / w + 1) * w' := by omega
  have hdiv : (n + w' - 1) / w' < (n + w - 1) / w + 1 :=
    (Nat.div_lt_iff_lt_mul hw').mpr hlt
  omega

/-- **Режим (a) — фиксированная стоимость окна**: c(w) = c ⇒
totalCost(w) = c·⌈n/w⌉ монотонно НЕвозрастает по w: при
0 < w ≤ w_max стоимость максимального окна не превосходит
стоимость любого допустимого (`ceil_div_anti` +
`Nat.mul_le_mul_left`). Certified правило: бери w = w_max —
укрупнение окна бесплатно сокращает число чтений. -/
theorem windowCost_fixed_mono (n c w wmax : ℕ) (hw : 0 < w) (hwmax : 0 < wmax)
    (hle : w ≤ wmax) :
    c * ((n + wmax - 1) / wmax) ≤ c * ((n + w - 1) / w) :=
  Nat.mul_le_mul_left c (ceil_div_anti n w wmax hw hwmax hle)

/-- **Режим (b) — линейное окно, границы**: c(w) = c·w ⇒
totalCost(w) = c·(w·⌈n/w⌉), и n ≤ w·⌈n/w⌉ ≤ n + w − 1
(`Nat.mul_div_le` сверху, `Nat.div_add_mod` + `Nat.mod_lt`
снизу): total-cost зажат в [c·n, c·(n+w)). -/
theorem windowCost_linear_bounds (n w : ℕ) (hw : 0 < w) :
    n ≤ w * ((n + w - 1) / w) ∧ w * ((n + w - 1) / w) ≤ n + w - 1 := by
  have hmul : w * ((n + w - 1) / w) ≤ n + w - 1 := Nat.mul_div_le _ _
  have hkm : w * ((n + w - 1) / w) + (n + w - 1) % w = n + w - 1 :=
    Nat.div_add_mod (n + w - 1) w
  have hmod : (n + w - 1) % w < w := Nat.mod_lt _ hw
  omega

/-- **Режим (b) — w-инвариантность total-cost** (удивительный
результат): при линейной стоимости чтения окна c(w) = c·w
total-cost почти НЕ зависит от выбора ширины: для любых
0 < w1, w1' ширина w1 превышает w1' не более чем на w1 − 1
окно-эквивалентов (обе границы `windowCost_linear_bounds` +
omega). В терминах стоимости: totalCost(w1) ≤ totalCost(w1') +
c·(w1 − 1) и симметрично — выбор w свободен по total-cost, его
делают только точность/глубина контекста. -/
theorem windowCost_linear_near_const (n w1 w2 : ℕ) (hw1 : 0 < w1) (hw2 : 0 < w2) :
    w1 * ((n + w1 - 1) / w1) ≤ w2 * ((n + w2 - 1) / w2) + (w1 - 1) := by
  obtain ⟨hle1, hle2⟩ := windowCost_linear_bounds n w1 hw1
  obtain ⟨hle1', hle2'⟩ := windowCost_linear_bounds n w2 hw2
  omega

/-- **Мост к иерархическому чтению **: totalCost(w) в модели
равен c·(hierStarts n B w w).length — стоимости реального
полного чтения (total = ⌈n/w⌉ при w ∣ B, делегат `hier_total_min`
иерархия ДОСТИГАЕТ информационного минимума чтений, на
котором стоит вся модель стоимости этого файла). -/
theorem windowCost_hier (n B w c : ℕ) (hw : 0 < w) (hB : 0 < B) (hdiv : w ∣ B) :
    c * ((n + w - 1) / w) = c * (hierStarts n B w w).length := by
  rw [hier_total_min n B w hw hB hdiv]

/-! ### Режим (c): суперлинейное окно c(w) = a + c·w²

Непрерывная релаксация totalCost — амортизированная стоимость
n·(a/w + c·w) (расщепление «дешёвые частые чтения vs дорогие
широкие окна») — минимизируется AM-GM; дискретный totalCost
наследует нижнюю границу через ⌈n/w⌉ ≥ n/w. -/

/-- **Режим (c) — квадратичное окно, нижняя граница AM-GM**:
релаксация per-read-стоимости a/w + c·w ≥ 2·√(a·c) при
a, c, w > 0 (AM-GM: (√u − √v)² ≥ 0 для u = a/w, v = c·w,
√u·√v = √(u·v) = √(a·c)). Ядро смешанного режима: минимум
непрерывной релаксации (n/w)·(a + c·w²) = n·(a/w + c·w)
не ниже 2n·√(a·c). -/
theorem mixedCost_relax_min {a c w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hw : 0 < w) : 2 * Real.sqrt (a * c) ≤ a / w + c * w := by
  have hu : 0 ≤ a / w := by positivity
  have hv : 0 ≤ c * w := by positivity
  have key := sq_nonneg (Real.sqrt (a / w) - Real.sqrt (c * w))
  rw [sub_sq, Real.sq_sqrt hu, Real.sq_sqrt hv] at key
  have hmul : Real.sqrt (a / w) * Real.sqrt (c * w) = Real.sqrt (a * c) := by
    rw [← Real.sqrt_mul]
    congr 1
    field_simp
    positivity
  linarith [key, hmul]

/-- **Режим (c) — точка равенства релаксации**: при
w = √(a/c) неравенство `mixedCost_relax_min` обращается в
равенство: обе части a/w и c·w равны √(a·c) (квадраты обеих
равны a·c, injectivity по pow_left_inj₀). Итого внутренний
оптимум квадратичной смешанной стоимости w* = √(a/c) —
certified (bench-случай α = 2 формулы
w* = (a/(c·(α−1)))^(1/α)). -/
theorem mixedCost_relax_min_eq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    a / Real.sqrt (a / c) + c * Real.sqrt (a / c)
      = 2 * Real.sqrt (a * c) := by
  have hw2 : (Real.sqrt (a / c)) ^ 2 = a / c :=
    Real.sq_sqrt (by positivity)
  have h1 : (a / Real.sqrt (a / c)) ^ 2 = a * c := by
    rw [div_pow, hw2, div_div_eq_mul_div]; field_simp
  have h2 : (c * Real.sqrt (a / c)) ^ 2 = a * c := by
    rw [mul_pow, hw2]; field_simp
  have e1 : a / Real.sqrt (a / c) = Real.sqrt (a * c) := by
    apply (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1
    rw [h1, Real.sq_sqrt (by positivity)]
  have e2 : c * Real.sqrt (a / c) = Real.sqrt (a * c) := by
    apply (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1
    rw [h2, Real.sq_sqrt (by positivity)]
  rw [e1, e2]; ring

/-- **Режим (c) — certified нижняя граница дискретного
totalCost**: totalCost(w) = ⌈n/w⌉·(a + c·w²) ≥ 2n·√(a·c) при
a, c > 0, w > 0. Мост: ⌈n/w⌉ = (n+w−1)/w ≥ n/w
(`windowCost_linear_bounds`, каст в ℝ), множитель a + c·w² > 0,
далее релаксация `mixedCost_relax_min` ×n. Дискретное
равенство в общем случае НЕ достигается (⌈n/w⌉ > n/w при
w ∤ n) — нижняя граница certified, точность определяется
целочисленным argmin bench. -/
theorem mixedCost_lower {n w : ℕ} {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hw : 0 < w) :
    2 * (n : ℝ) * Real.sqrt (a * c)
      ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) := by
  obtain ⟨hle, _⟩ := windowCost_linear_bounds n w hw
  have hcast : (n : ℝ) ≤ (w : ℝ) * ((n + w - 1) / w : ℕ) :=
    by exact_mod_cast hle
  have hw' : (0 : ℝ) < (w : ℕ) := by exact_mod_cast hw
  have hbridge : (n : ℝ) / (w : ℝ) ≤ ((n + w - 1) / w : ℕ) := by
    rw [div_le_iff₀ hw']; linarith
  have hpos : (0 : ℝ) < a + c * (w : ℝ) ^ 2 := by positivity
  have hstep1 : (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2)
      ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hbridge hpos.le
  have hstep2 : (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2)
      = (n : ℝ) * (a / (w : ℝ) + c * (w : ℝ)) := by
    field_simp
  calc 2 * (n : ℝ) * Real.sqrt (a * c)
      ≤ (n : ℝ) * (a / (w : ℝ) + c * (w : ℝ)) :=
        by nlinarith [mixedCost_relax_min (w := (w : ℝ)) ha hc hw']
    _ = (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2) := hstep2.symm
    _ ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) := hstep1

end Hagi.Theory.WindowTradeoff

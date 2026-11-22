/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.AdaptiveContext

set_option relaxedAutoImplicit false

/-!
# CoverageReading — полное чтение входа окнами (C598, wave228)

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

end Hagi.Theory.CoverageReading

namespace Hagi.Theory.CoverageReading

/-!
## C602: adaptive span — параметрический шаг (замыкание негатива C598)

Код-импликация `covStarts_trunc_uncovered_zero`: при переполнении
(окон > max_span) НЕ усекать хвост слепо (байт 0 теряется), а
ПЕРЕСЧИТАТЬ старты с бОльшим шагом s ≤ w — покрытие сохраняется,
число окон входит в бюджет. Точное условие покрытия при окне
длины w и шаге s: 0 < s ≤ w (соседние окна перекрываются/
стыкуются, суффикс-фоллбек закрывает хвост); при s > w между
окнами остаётся дыра (witness .tmp/C602/trajSpan.lean).
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

/-- **Замыкание негатива C598**: адаптивный шаг s (0 < s ≤ w,
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

end Hagi.Theory.CoverageReading

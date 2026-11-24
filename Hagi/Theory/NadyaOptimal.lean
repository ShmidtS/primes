/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.TritCodec
import Hagi.Theory.ExactBypass
import Hagi.Theory.ArchiverCodeLength
import Hagi.Theory.Statistics
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
set_option linter.style.openClassical false
set_option linter.style.header false

/-!
# NadyaOptimal — идеи «HAGI v2 Optimal» и их носители в primes

Источник (READ-ONLY): `C:/HAGI_v2/checkpoints/Надя.txt` @2026-11-24,
961 строк Python «HAGI v2 Optimal — Compact Self-Growing Neuro-Symbolic
Byte Model». Формализованы только идеи с честным носителем; остальное —
карточки в STATUS.md.

* §BitAlloc: _pack_trits5/_unpack_trits5 (Надя.txt:413-424, 5 тритов
  {-1,0,1} → byte, base-3, цифра = уровень + 1) — round-trip
  `trit5_roundtrip` через `trit_roundtrip` (TritCodec, C574) после
  сдвига цифр; _pack_int4/_unpack_int4 (Надя.txt:427-440, два
  int4-кода → byte) — `int4_roundtrip` (list-level срез по длине не
  формализован, карточка); _best_mse_ternary (Надя.txt:390-410) —
  `exists_best_mse_scale` (существование минимизатора MSE).
* §Schedules: cosine-расписание HybridMuon (Надя.txt:136,
  sched = 0.15 + 0.85·½(1 + cos(π·min(t,T)/T))) — границы, старт,
  финиш, монотонность; Muon-шаг (Надя.txt:140-144) — `muon_step_norm_bound`.
* WIDTH-рост — отдельный модуль `Hagi/Theory/WidthGrowth.lean`;
  DEPTH-рост `trunk_function_preserving` — FunctionPreservingGrowth.
* §LCB: paired_gain (Надя.txt:109-112) — гейт ingest_continual
  (Надя.txt:884-890, GROW iff lcb > 0): вероятность ложного GROW
  через Hoeffding (`holdout_concentration`) при ограниченных разностях
  и детерминированном радиусе (`paired_lcb_false_grow_bound`).
* §Bypass: EXACT_BYPASS (Надя.txt:695-750) — one-hot предиктор ⇒ CE = 0,
  идеальная длина кода = 0 = энтропия (`bypass_reaches_compression_limit`;
  мост ExactBypass ↔ ArchiverCodeLength).

Арithmetic coder (Надя.txt:460-560) не формализован — карточка ArchiverCodeLength;
coherence_dust_filter — эвристика без certified-свойства (карточка).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.NadyaOptimal

open Hagi.Theory.TritCodec Hagi.Theory.ArchiverCodeLength Hagi.Prelude
open scoped BigOperators

/-! ## §BitAlloc — trit5 / int4 round-trip и лучший MSE scale -/

section BitAlloc

/-- Сдвиг уровня {-1,0,1} в цифру {0,1,2}: dig = уровень + 1
(_pack_trits5, Надя.txt:417: `dig = [v + 1 ...]`). Уровень 2
играет роль −1. -/
def trit5Dig (l : Fin 5 → Fin 3) (i : Fin 5) : Fin 3 := (l i + 1) % 3

/-- Обратный сдвиг (_unpack_trits5, Надя.txt:421: `(n % 3) - 1`;
цифра 0 — это уровень −1 = код 2). -/
def trit5Unshift (d : Fin 3) : Fin 3 := if d = 0 then 2 else ⟨(d : ℕ) - 1, by omega⟩

/-- _pack_trits5: 5 тритов → один byte, base-3 по сдвинутым
цифрам (Надя.txt:413-419). -/
def trit5Pack (l : Fin 5 → Fin 3) : ℕ := tritPack (trit5Dig l)

/-- _unpack_trits5: byte → 5 тритов (Надя.txt:421-424). -/
def trit5Unpack (v : ℕ) : Fin 5 → Fin 3 := fun i => trit5Unshift (tritUnpack v i)

theorem trit5_unshift (l : Fin 5 → Fin 3) (i : Fin 5) :
    trit5Unshift (trit5Dig l i) = l i := by
  have key : ∀ v : Fin 3, (trit5Unshift ((v + 1) % 3) : ℕ) = (v : ℕ) := by decide
  exact (Fin.val_inj.mp (key (l i)))

/-- ROUND-TRIP trit5: unpack (pack l) = l — позиционная система
TritCodec плюс биективность сдвига цифр. -/
theorem trit5_roundtrip (l : Fin 5 → Fin 3) : trit5Unpack (trit5Pack l) = l := by
  funext i
  have hi := congrFun (trit_roundtrip (trit5Dig l)) i
  show trit5Unshift (tritUnpack (tritPack (trit5Dig l)) i) = l i
  rw [hi]
  exact trit5_unshift l i

/-- Код trit5 всегда помещается в byte: < 243 < 256. -/
theorem trit5Pack_lt_243 (l : Fin 5 → Fin 3) : trit5Pack l < 243 :=
  tritPack_lt_243 _

/-- _pack_int4 (Надя.txt:427-431): два 4-битных кода → byte
`lo | hi << 4` = lo + 16·hi (lo < 16, поэтому OR = сумма); код = уровень + 7,
уровни -7..7 ↔ коды 0..14. -/
def int4Pack (a b : ℕ) : ℕ := a + 16 * b

/-- _unpack_int4 (Надя.txt:434-440): byte → (lo, hi) = (v % 16, v / 16). -/
def int4Unpack (v : ℕ) : ℕ × ℕ := (v % 16, v / 16)

theorem int4_roundtrip (a b : ℕ) (ha : a < 15) (hb : b < 15) :
    int4Pack a b < 256 ∧ int4Unpack (int4Pack a b) = (a, b) := by
  have hlt : int4Pack a b < 256 := by
    show a + 16 * b < 256
    have h1 := ha
    have h2 := hb
    omega
  refine ⟨hlt, ?_⟩
  have hlo : int4Pack a b % 16 = a := by
    show (a + 16 * b) % 16 = a
    have h1 := ha
    have h2 := hb
    omega
  have hhi : int4Pack a b / 16 = b := by
    show (a + 16 * b) / 16 = b
    have h1 := ha
    have h2 := hb
    omega
  simp only [int4Unpack, hlo, hhi]

/-- Ошибка тернарного квантования строки при scale s
(_best_mse_ternary, Надя.txt:404: `err = Σ (row − q·s)²`). -/
noncomputable def ternErr {n : ℕ} (row : Fin n → ℝ) (q : Fin n → ℤ) (s : ℝ) : ℝ :=
  ∑ i, (row i - (q i : ℝ) * s) ^ 2

/-- Лучший MSE scale СУЩЕСТВУЕТ: на непустом конечном списке кандидатов
есть scale, ошибка которого не хуже любого другого кандидата
(контракт argmin-поиска _best_mse_ternary, Надя.txt:402-410). -/
theorem exists_best_mse_scale {n : ℕ} (row : Fin n → ℝ) (q : ℝ → Fin n → ℤ)
    (cands : Finset ℝ) (hne : cands.Nonempty) :
    ∃ s ∈ cands, ∀ c ∈ cands, ternErr row (q s) s ≤ ternErr row (q c) c := by
  obtain ⟨s, hs, hmin⟩ := cands.exists_min_image (fun c => ternErr row (q c) c) hne
  exact ⟨s, hs, fun c hc => hmin c hc⟩

end BitAlloc

/-! ## §Schedules — cosine HybridMuon и норма Muon-шага -/

section Schedules

/-- Cosine-расписание HybridMuon (Надя.txt:136):
sched(t) = 0.15 + 0.85·½(1 + cos(π·min(t,T)/T)). -/
noncomputable def cosineSched (T t : ℝ) : ℝ :=
  3 / 20 + 17 / 20 * ((1 + Real.cos (Real.pi * min t T * T⁻¹)) / 2)

theorem cosine_sched_bounds (T t : ℝ) :
    3 / 20 ≤ cosineSched T t ∧ cosineSched T t ≤ 1 := by
  unfold cosineSched
  have hlo := Real.neg_one_le_cos (Real.pi * min t T * T⁻¹)
  have hhi := Real.cos_le_one (Real.pi * min t T * T⁻¹)
  constructor <;> linarith

/-- sched(0) = 1: расписание стартует с полного learning rate. -/
theorem cosine_sched_start (T : ℝ) (hT : 0 < T) : cosineSched T 0 = 1 := by
  unfold cosineSched
  rw [min_eq_left (by linarith), mul_zero, zero_mul, Real.cos_zero]
  ring

/-- sched(t) = 0.15 для t ≥ T: финиш на полу learning rate. -/
theorem cosine_sched_end (T t : ℝ) (hT : 0 < T) (ht : T ≤ t) :
    cosineSched T t = 3 / 20 := by
  unfold cosineSched
  rw [min_eq_right ht]
  have hdiv : Real.pi * T * T⁻¹ = Real.pi := by field_simp
  rw [hdiv, Real.cos_pi]
  ring

/-- Монотонное затухание: для 0 ≤ t₁ ≤ t₂ sched(t₂) ≤ sched(t₁). -/
theorem cosine_sched_mono (T t₁ t₂ : ℝ) (hT : 0 < T) (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂) :
    cosineSched T t₂ ≤ cosineSched T t₁ := by
  have hT0 : (0 : ℝ) ≤ Real.pi * T⁻¹ := by positivity
  have hm : min t₁ T ≤ min t₂ T := min_le_min h₁₂ le_rfl
  have hπ₁ : 0 ≤ Real.pi * min t₁ T * T⁻¹ := by positivity
  have hπ₂ : Real.pi * min t₂ T * T⁻¹ ≤ Real.pi := by
    have h1 : min t₂ T ≤ T := min_le_right _ _
    calc Real.pi * min t₂ T * T⁻¹ = (Real.pi * T⁻¹) * min t₂ T := by ring
      _ ≤ (Real.pi * T⁻¹) * T := mul_le_mul_of_nonneg_left h1 hT0
      _ = Real.pi := by field_simp
  have hπ₂0 : 0 ≤ Real.pi * min t₂ T * T⁻¹ := by
    have hm : 0 ≤ min t₂ T := le_min (h₁.trans h₁₂) hT.le
    exact mul_nonneg (mul_nonneg Real.pi_pos.le hm) (inv_nonneg.mpr hT.le)
  have hmul : Real.pi * min t₁ T * T⁻¹ ≤ Real.pi * min t₂ T * T⁻¹ := by
    have : (Real.pi * T⁻¹) * min t₁ T ≤ (Real.pi * T⁻¹) * min t₂ T :=
      mul_le_mul_of_nonneg_left hm hT0
    linarith
  have hcos : Real.cos (Real.pi * min t₂ T * T⁻¹) ≤ Real.cos (Real.pi * min t₁ T * T⁻¹) := by
    by_cases heq : Real.pi * min t₁ T * T⁻¹ = Real.pi * min t₂ T * T⁻¹
    · rw [heq]
    · have hanti : AntitoneOn Real.cos (Set.Icc 0 Real.pi) :=
        Real.strictAntiOn_cos.antitoneOn
      have hm₂ : Real.pi * min t₂ T * T⁻¹ ∈ Set.Icc (0 : ℝ) Real.pi :=
        Set.mem_Icc.mpr ⟨hπ₂0, hπ₂⟩
      have hm₁ : Real.pi * min t₁ T * T⁻¹ ∈ Set.Icc (0 : ℝ) Real.pi :=
        Set.mem_Icc.mpr ⟨hπ₁, hmul.trans hπ₂⟩
      exact hanti hm₁ hm₂ hmul
  have h0 : (0 : ℝ) ≤ 17 / 20 := by norm_num
  have hcos' := mul_le_mul_of_nonneg_left hcos h0
  unfold cosineSched
  linarith

/-- Muon-шаг (Надя.txt:143: `p -= (lr·sched·sc)·orth`): норма изменения
весов за шаг ≤ lr·sched·sc·c, где c — верхняя граница нормы
полярной матрицы (гипотеза; PolarExpressCert C545 не воспроизведён). -/
theorem muon_step_norm_bound {n : Type} [Fintype n] (a c : ℝ) (ha : 0 ≤ a)
    (p orth : EuclideanSpace ℝ n) (horth : ‖orth‖ ≤ c) :
    ‖(p - a • orth) - p‖ ≤ a * c := by
  have h : (p - a • orth) - p = -(a • orth) := by abel
  rw [h, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left horth ha

end Schedules


/-! ## §LCB — paired_gain и вероятность ложного GROW -/

section LCB

open Hagi.Probability Hagi.Theory.HoldoutRisk

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- Разность paired_gain `d = before − after` (Надя.txt:110),
центрированная в [0,1]: f = (d + B)/(2B). -/
theorem paired_mean_dev_bound {k : ℕ} (hk : 0 < k) {B : ℝ} (hB : 0 < B)
    (d : Ω → ℝ) (hd : ∀ ω, -B ≤ d ω ∧ d ω ≤ B) (r : ℝ) (hr : 0 < r) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => popMean d + r ≤ holdoutMean d ωs)
      ≤ concConfidenceTwoSided (r / (2 * B)) k := by
  have hshift : ∀ ωs : Fin k → Ω,
      holdoutMean (fun ω => (d ω + B) / (2 * B)) ωs
        = (holdoutMean d ωs + B) / (2 * B) := by
    intro ωs
    unfold holdoutMean
    have hkr : ((k : ℕ) : ℝ) ≠ 0 := mod_cast ne_of_gt hk
    have hB2 : (2 * B) ≠ 0 := by positivity
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hshift' : popMean (fun ω => (d ω + B) / (2 * B)) = (popMean d + B) / (2 * B) := by
    unfold popMean
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := mod_cast Fintype.card_ne_zero (α := Ω)
    have hB2 : (2 * B) ≠ 0 := by positivity
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  have himp : ∀ ωs : Fin k → Ω,
      (popMean d + r ≤ holdoutMean d ωs) →
      r / (2 * B) ≤ |holdoutMean (fun ω => (d ω + B) / (2 * B)) ωs
          - popMean (fun ω => (d ω + B) / (2 * B))| := by
    intro ωs h
    have hB2 : (0 : ℝ) < 2 * B := by positivity
    have hsub : holdoutMean d ωs + B - (popMean d + B) = holdoutMean d ωs - popMean d := by
      ring
    rw [hshift, hshift', ← sub_div, hsub]
    have hnn : 0 ≤ holdoutMean d ωs - popMean d := by linarith
    rw [abs_div, abs_of_pos hB2, abs_of_nonneg hnn, div_le_div_iff₀ hB2 hB2]
    nlinarith [hB2, hnn]
  have hf : ∀ ω, 0 ≤ (d ω + B) / (2 * B) ∧ (d ω + B) / (2 * B) ≤ 1 := by
    intro ω
    obtain ⟨h1, h2⟩ := hd ω
    have hB2 : (0 : ℝ) < 2 * B := by positivity
    constructor
    · apply div_nonneg <;> linarith [hB2.le]
    · exact (div_le_one hB2).mpr (by linarith)
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb _ _ himp
  exact hmono.trans (holdout_concentration hk hf _ (by positivity))

/-- ГЕЙТ ingest_continual (Надя.txt:884-890): GROW iff lcb > 0, где lcb =
mean(d) − радиус. Радиус в коде — z·σ̂/√n по ВЫБОРОЧНОМУ σ̂ (z = 1.5,
случайная величина); здесь радиус r детерминированный — честная модель.
Если истинный gain неположителен (popMean d ≤ 0), вероятность ложного
GROW ≤ 2·exp(−2k(r/(2B))²). -/
theorem paired_lcb_false_grow_bound {k : ℕ} (hk : 0 < k) {B : ℝ} (hB : 0 < B)
    (d : Ω → ℝ) (hd : ∀ ω, -B ≤ d ω ∧ d ω ≤ B) (r : ℝ) (hr : 0 < r)
    (hμ : popMean d ≤ 0) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => 0 < holdoutMean d ωs - r ∧ popMean d ≤ 0)
      ≤ concConfidenceTwoSided (r / (2 * B)) k := by
  have himp : ∀ ωs : Fin k → Ω,
      (0 < holdoutMean d ωs - r ∧ popMean d ≤ 0) → popMean d + r ≤ holdoutMean d ωs := by
    intro ωs hgrow
    linarith [hgrow.1]
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb _ _ himp
  exact hmono.trans (paired_mean_dev_bound hk hB d hd r hr)

end LCB

/-! ## §Bypass — символьный закон = предел сжатия -/

section Bypass

variable {X : Type*} [Fintype X]

omit [Fintype X] in
/-- Длина идеального кодера для вероятности 1 равна нулю:
`⌈−log₂ 1⌉₊ = ⌈0⌉₊ = 0`. -/
theorem idealLen_eq_zero_of_prob_one (q : X → ℝ) (x : X) (hx : q x = 1) :
    idealLen q x = 0 := by
  unfold idealLen log2
  simp [hx]

/-- EXACT_BYPASS (Надя.txt:695-750): если предиктор q — распределение,
ставящее вероятность 1 на каждом байте, возможном по закону (носитель
p), то CE в битах равен нулю, идеальная длина кода равна нулю и
энтропия данных равна нулю — символьный закон достигает
теоретического предела сжатия. -/
theorem bypass_reaches_compression_limit (p q : X → ℝ) [Nonempty X]
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ x, 0 < p x → q x = 1) (hqnn : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) :
    ceBits p q = 0 ∧ expLen p (idealLen q) = 0 ∧ entBits p = 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, 0 < p x₀ := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ x, p x = 0 := fun x => le_antisymm (hcon x) (hp x)
    have hp0 : p = fun _ => 0 := funext hz
    rw [hp0] at hp1
    simp at hp1
  have hsupp : ∀ x, p x > 0 → x = x₀ := by
    intro x hx
    by_contra hne
    have hq₀ : q x₀ = 1 := hq x₀ hx₀
    have hqx : q x = 1 := hq x hx
    have hsum : (1 : ℝ) + 1 ≤ ∑ y ∈ ({x₀, x} : Finset X), q y := by
      simp [Finset.sum_insert (fun hm => hne (Finset.mem_singleton.mp hm).symm), hq₀, hqx]
    have hle : ∑ y ∈ ({x₀, x} : Finset X), q y ≤ ∑ y, q y := by
      rw [← Finset.sum_sdiff (Finset.subset_univ ({x₀, x} : Finset X))]
      linarith [Finset.sum_nonneg (s := Finset.univ \ {x₀, x}) (fun y _ => hqnn y)]
    have h2 : (1 : ℝ) + 1 ≤ ∑ y, q y := hsum.trans hle
    linarith [hq1, h2]
  have hpx : ∀ x, p x = 0 ∨ p x = 1 := by
    intro x
    by_cases hx : 0 < p x
    · right
      have hpz : ∀ y, y ≠ x → p y = 0 := by
        intro y hy
        have hy0 : ¬ 0 < p y := fun hy0 => hy ((hsupp y hy0).trans (hsupp x hx).symm)
        linarith [hp y]
      have hs : (∑ y, p y) = p x := by
        apply Finset.sum_eq_single x
        · intro y _ hy
          exact hpz y hy
        · intro h
          exact absurd (Finset.mem_univ x) h
      linarith
    · left
      linarith [hp x]
  have hlen : ∀ x, p x * (idealLen q x : ℝ) = 0 := by
    intro x
    by_cases hx : 0 < p x
    · rw [idealLen_eq_zero_of_prob_one q x (hq x hx)]
      simp
    · have hp0 : p x = 0 := le_antisymm (by linarith [hp x]) (hp x)
      rw [hp0, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · have hce : ∑ v, p v * Real.log (q v) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : 0 < p x
      · rw [hq x hx, Real.log_one, mul_zero]
      · have hp0 : p x = 0 := le_antisymm (by linarith [hp x]) (hp x)
        rw [hp0, zero_mul]
    unfold ceBits ceDef
    rw [hce, neg_zero, zero_div]
  · unfold expLen
    exact Finset.sum_eq_zero fun x _ => hlen x
  · unfold entBits entDef
    have hz : ∑ x, p x * Real.log (p x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rcases hpx x with h | h
      · rw [h, zero_mul]
      · simp [h]
    rw [hz, neg_zero, zero_div]

end Bypass

end Hagi.Theory.NadyaOptimal

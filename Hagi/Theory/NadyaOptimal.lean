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
# NadyaOptimal — идеи «HAGI v2 Optimal» и их носители в primes (C666)

Источник (READ-ONLY): `C:/HAGI_v2/checkpoints/Надя.txt` @2026-11-24,
961 строк Python «HAGI v2 Optimal — Compact Self-Growing Neuro-Symbolic
Byte Model». Формализованы только идеи с честным носителем; остальное —
карточки в STATUS.md (C666).

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
* §WidthGrowth: полный function-preserving WIDTH-рост grow_width
  (Надя.txt:350-410) на послойном носителе `WParams` (nh = 1, hd = d):
  `rmsnorm_scale_inv` (gain ×√(d0/d1), eps ×(d0/d1)), T1
  `attn_score_scale_preserved` (W_q ×√(hd1/hd0) ⇒ score/√hd и
  softmax-веса сохраняются), T2 `rotary_old_pairs_unchanged`
  (f1 = concat(f0, новые) ⇒ старые пары вращаются идентично), T3
  `wlogits_width_preserved` (правило `WGrowth` ⇒ logits_new = logits_old
  ТОЧНО). WIDTH-рост — второй вид роста рядом с DEPTH-ростом
  `trunk_function_preserving` (FunctionPreservingGrowth).
* §LCB: paired_gain (Надя.txt:109-112) — гейт ingest_continual
  (Надя.txt:884-890, GROW iff lcb > 0): вероятность ложного GROW
  через Hoeffding (`holdout_concentration`) при ограниченных разностях
  и детерминированном радиусе (`paired_lcb_false_grow_bound`).
* §Bypass: EXACT_BYPASS (Надя.txt:695-750) — one-hot предиктор ⇒ CE = 0,
  идеальная длина кода = 0 = энтропия (`bypass_reaches_compression_limit`;
  мост ExactBypass C541 ↔ ArchiverCodeLength C653).

Арithmetic coder (Надя.txt:460-560) не формализован — карточка C653;
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

/-! ## §WidthGrowth — инвариант RMSNorm при дополнении нулями -/

section WidthGrowth

/-- Средний квадрат координат: mean(x²) по ширине d
(_rmsnorm, Надя.txt:51: `np.mean(x * x, axis=-1)`). -/
noncomputable def rmsMs {d : ℕ} (x : Fin d → ℝ) : ℝ := (∑ i, x i ^ 2) / (d : ℝ)

/-- Нормированный вывод с gain: `x / √(mean(x²) + ε) · g`
(Надя.txt:51-52). -/
noncomputable def rmsOut (ε : ℝ) {d : ℕ} (g x : Fin d → ℝ) (i : Fin d) : ℝ :=
  x i / Real.sqrt (rmsMs x + ε) * g i

/-- Дополнение нулями: mean(y²) по ширине d1 = (d0/d1)·mean(x²). -/
theorem rmsMs_pad (d0 d1 : ℕ) (hd0 : 0 < d0) (hdd : d0 ≤ d1) (x : Fin d0 → ℝ)
    (y : Fin d1 → ℝ)
    (hy : ∀ i : Fin d1, y i = if h : (i : ℕ) < d0 then x ⟨i, h⟩ else 0) :
    rmsMs y = ((d0 : ℝ) / d1) * rmsMs x := by
  have hsum : (∑ i : Fin d1, y i ^ 2) = ∑ i : Fin d0, x i ^ 2 := by
    have hcv : ∀ (d : ℕ) (hd : 0 < d) (z : Fin d → ℝ),
          (∑ i : Fin d, z i ^ 2)
            = ∑ i ∈ Finset.range d, z ⟨i % d, Nat.mod_lt i hd⟩ ^ 2 := by
      intro d hd z
      calc (∑ i : Fin d, z i ^ 2)
          = ∑ i : Fin d, z ⟨(i : ℕ) % d, Nat.mod_lt i hd⟩ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi : (⟨(i : ℕ) % d, Nat.mod_lt i hd⟩ : Fin d) = i := by
              apply Fin.ext
              exact Nat.mod_eq_of_lt i.isLt
            rw [hi]
        _ = ∑ i ∈ Finset.range d, z ⟨i % d, Nat.mod_lt i hd⟩ ^ 2 :=
            Fin.sum_univ_eq_sum_range
              (fun i => z ⟨i % d, Nat.mod_lt i hd⟩ ^ 2) d
    rw [hcv d1 (by omega) y, hcv d0 hd0 x]
    have hsub : (∑ i ∈ Finset.range d1, y ⟨i % d1, Nat.mod_lt i (by omega)⟩ ^ 2)
        = ∑ i ∈ Finset.range d0, y ⟨i % d1, Nat.mod_lt i (by omega)⟩ ^ 2 := by
      apply Eq.symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr hdd)
      intro i hi1 hi
      have hi0 : i < d1 := Finset.mem_range.mp hi1
      have hni : ¬ i < d0 := fun h => hi (Finset.mem_range.mpr h)
      have he : (⟨i % d1, Nat.mod_lt i (by omega)⟩ : Fin d1) = ⟨i, hi0⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hi0
      rw [he, hy ⟨i, hi0⟩, dif_neg hni]
      ring
    rw [hsub]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : i < d1 := lt_of_lt_of_le (Finset.mem_range.mp hi) hdd
    have he1 : (⟨i % d1, Nat.mod_lt i (by omega)⟩ : Fin d1) = ⟨i, hi0⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hi0
    have he2 : (⟨i % d0, Nat.mod_lt i (by omega)⟩ : Fin d0)
        = ⟨i, Finset.mem_range.mp hi⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (Finset.mem_range.mp hi)
    rw [he1, he2, hy ⟨i, hi0⟩, dif_pos (Finset.mem_range.mp hi)]
  unfold rmsMs
  rw [hsum]
  field_simp

/-- ЯДРО grow_width (Надя.txt:361-367): при дополнении нулями,
масштабе gain ×√(d0/d1) и eps ×(d0/d1) нормированный вывод старых
координат СОХРАНЯЕТСЯ ТОЧНО. -/
theorem rmsnorm_scale_inv (d0 d1 : ℕ) (hd0 : 0 < d0) (hdd : d0 ≤ d1) (ε : ℝ)
    (x g : Fin d0 → ℝ) (y g1 : Fin d1 → ℝ)
    (hy : ∀ i : Fin d1, y i = if h : (i : ℕ) < d0 then x ⟨i, h⟩ else 0)
    (hg1 : ∀ i : Fin d0, g1 (Fin.castLE hdd i) = g i * Real.sqrt ((d0 : ℝ) / d1))
    (i : Fin d0) :
    rmsOut (ε * ((d0 : ℝ) / d1)) g1 y (Fin.castLE hdd i) = rmsOut ε g x i := by
  have hd1 : (0 : ℝ) < d1 := by
    have h : 0 < d1 := lt_of_lt_of_le hd0 hdd
    exact_mod_cast h
  have hr : 0 ≤ (d0 : ℝ) / d1 := div_nonneg (mod_cast hd0.le) (by positivity)
  have hsq : Real.sqrt ((d0 : ℝ) / d1) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos (mod_cast hd0) hd1)
  have hpad := rmsMs_pad d0 d1 hd0 hdd x y hy
  have hden : rmsMs y + ε * ((d0 : ℝ) / d1)
      = ((d0 : ℝ) / d1) * (rmsMs x + ε) := by rw [hpad]; ring
  have hyi : y (Fin.castLE hdd i) = x i := by
    have hlt : ((Fin.castLE hdd i : Fin d1) : ℕ) < d0 := by
      simp [Fin.castLE]
    rw [hy (Fin.castLE hdd i), dif_pos hlt]
    apply congrArg
    apply Fin.ext
    simp [Fin.castLE]
  unfold rmsOut
  rw [hden, Real.sqrt_mul hr, hyi, hg1 i]
  field_simp

/-! #### Носители дополнения нулями -/

/-- Дополнение вектора нулями до ширины «d1». -/
noncomputable def padTo {d0 : ℕ} (d1 : ℕ) (x : Fin d0 → ℝ) : Fin d1 → ℝ :=
  fun i => if h : (i : ℕ) < d0 then x ⟨i, h⟩ else 0

/-- Сумма по дополненному вектору = сумме по старому (новые координаты — нули). -/
theorem sum_pad (d0 d1 : ℕ) (hd0 : 0 < d0) (hdd : d0 ≤ d1) (f : Fin d0 → ℝ) (f1 : Fin d1 → ℝ)
    (hf : f1 = padTo d1 f) : (∑ i : Fin d1, f1 i) = ∑ i : Fin d0, f i := by
  have key : ∀ (n : ℕ) (hn : 0 < n) (g : Fin n → ℝ),
      (∑ i : Fin n, g i) = ∑ i ∈ Finset.range n, g ⟨i % n, Nat.mod_lt i hn⟩ := by
    intro n hn g
    calc (∑ i : Fin n, g i)
        = ∑ i : Fin n, g ⟨(i : ℕ) % n, Nat.mod_lt i hn⟩ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : (⟨(i : ℕ) % n, Nat.mod_lt i hn⟩ : Fin n) = i := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt i.isLt
          rw [hi]
      _ = ∑ i ∈ Finset.range n, g ⟨i % n, Nat.mod_lt i hn⟩ :=
          Fin.sum_univ_eq_sum_range (fun i => g ⟨i % n, Nat.mod_lt i hn⟩) n
  have h1 : 0 < d1 := lt_of_lt_of_le hd0 hdd
  rw [key d1 h1 f1, key d0 hd0 f, hf]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hdd) ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : i < d0 := Finset.mem_range.mp hi
    have hi1 : i < d1 := lt_of_lt_of_le hi0 hdd
    have he : (⟨i % d1, Nat.mod_lt i h1⟩ : Fin d1) = ⟨i, hi1⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hi1
    rw [he, padTo, dif_pos hi0]
    show f (⟨i, hi0⟩ : Fin d0) = f ⟨i % d0, Nat.mod_lt i hd0⟩
    exact congrArg f (Fin.ext (Nat.mod_eq_of_lt hi0).symm)
  · intro i hi1 hi
    have hin : i < d1 := Finset.mem_range.mp hi1
    have he : (⟨i % d1, Nat.mod_lt i h1⟩ : Fin d1) = ⟨i, hin⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hin
    rw [he]
    simp only [padTo, dif_neg (fun h => hi (Finset.mem_range.mpr h))]

/-- Сумма по дополненному (позади масштаб «c») вектору = «c» · старая сумма. -/
theorem sum_pad_scale (d0 d1 : ℕ) (hd0 : 0 < d0) (hdd : d0 ≤ d1) (c : ℝ) (f : Fin d0 → ℝ)
    (f1 : Fin d1 → ℝ)
    (hf : f1 = padTo d1 (fun i => c * f i)) : (∑ i : Fin d1, f1 i) = c * ∑ i : Fin d0, f i := by
  rw [sum_pad d0 d1 hd0 hdd _ f1 hf, Finset.mul_sum]

/-- Критерий ««f1» = дополнение «f» нулями»: совпадение на старых
координатах + нули на новых. -/
theorem eq_padTo {d0 d1 : ℕ} (hdd : d0 ≤ d1) (f : Fin d0 → ℝ) (f1 : Fin d1 → ℝ)
    (hold : ∀ i : Fin d0, f1 (Fin.castLE hdd i) = f i)
    (hnew : ∀ i : Fin d1, d0 ≤ (i : ℕ) → f1 i = 0) : f1 = padTo d1 f := by
  funext i
  by_cases h : (i : ℕ) < d0
  · have hc : (Fin.castLE hdd ⟨(i : ℕ), h⟩ : Fin d1) = i := rfl
    calc f1 i = f1 (Fin.castLE hdd ⟨(i : ℕ), h⟩) := by rw [hc]
      _ = f ⟨(i : ℕ), h⟩ := hold ⟨(i : ℕ), h⟩
      _ = padTo d1 f i := by simp only [padTo, dif_pos h]
  · rw [padTo, dif_neg h, hnew i (by omega)]

/-- Матрица «вход → выход», дополненная по входу: старые строки × «c»,
новые строки — нули. -/
noncomputable def rowPad {d0 : ℕ} (d1 : ℕ) (c : ℝ) (W : Fin d0 → Fin n → ℝ) :
    Fin d1 → Fin n → ℝ :=
  fun j i => if h : (j : ℕ) < d0 then c * W ⟨j, h⟩ i else 0

/-- Столбец матрицы «W» (вход → выход), умноженный на дополненный вектор:
результат = «c» · старое произведение. -/
theorem mulvec_rowPad {d0 d1 : ℕ} (hd0 : 0 < d0) (hdd : d0 ≤ d1) (c : ℝ)
    (W : Fin d0 → Fin n → ℝ) (x : Fin d0 → ℝ) (x1 : Fin d1 → ℝ) (hx : x1 = padTo d1 x)
    (i : Fin n) :
    (∑ j : Fin d1, rowPad d1 c W j i * x1 j) = c * ∑ j : Fin d0, W j i * x j := by
  refine sum_pad_scale d0 d1 hd0 hdd c _ _ ?_
  apply eq_padTo hdd
  · intro j
    simp only [rowPad, hx, padTo, Fin.coe_castLE, dif_pos j.isLt]
    ring
  · intro j hj
    simp only [rowPad]
    rw [dif_neg (by omega)]
    ring

/-- Матрица «вход → выход», дополненная по обеим осям: старый блок × «c»,
новые строки и столбцы — нули (Надя.txt:384-391: «Wb[:] = 0», блок «[:d0, :hd0] = Ws·sc»). -/
noncomputable def matPadS {d0 n0 : ℕ} (d1 n1 : ℕ) (c : ℝ) (W : Fin d0 → Fin n0 → ℝ) :
    Fin d1 → Fin n1 → ℝ :=
  fun j i => if h : (j : ℕ) < d0 then if h' : (i : ℕ) < n0 then c * W ⟨j, h⟩ ⟨i, h'⟩ else 0 else 0

theorem mulvec_matPadS {d0 n0 d1 n1 : ℕ} (hd0 : 0 < d0) (hdd : d0 ≤ d1) (c : ℝ)
    (W : Fin d0 → Fin n0 → ℝ) (x : Fin d0 → ℝ) (x1 : Fin d1 → ℝ) (hx : x1 = padTo d1 x)
    (t : Fin n1) :
    (∑ j : Fin d1, matPadS d1 n1 c W j t * x1 j)
      = if h : (t : ℕ) < n0 then c * ∑ j : Fin d0, W j ⟨t, h⟩ * x j else 0 := by
  by_cases h : (t : ℕ) < n0
  · have hm : ∀ j : Fin d1, matPadS d1 n1 c W j t = rowPad d1 c (fun j _ => W j ⟨t, h⟩) j t := by
      intro j
      by_cases hj : (j : ℕ) < d0
      · simp only [matPadS, rowPad, dif_pos hj, dif_pos h]
      · simp only [matPadS, rowPad, dif_neg hj]
    simp only [hm]
    have hd : (if h' : (t : ℕ) < n0 then c * ∑ j : Fin d0, W j ⟨t, h'⟩ * x j else 0)
        = c * ∑ j : Fin d0, W j ⟨t, h⟩ * x j := dif_pos h
    exact (mulvec_rowPad hd0 hdd c (fun j _ => W j ⟨t, h⟩) x x1 hx t).trans hd.symm
  · have hz : ∀ j : Fin d1, matPadS d1 n1 c W j t = 0 := by
      intro j
      by_cases hj : (j : ℕ) < d0
      · simp only [matPadS, dif_pos hj, dif_neg h]
      · simp only [matPadS, dif_neg hj]
    simp only [hz, zero_mul, Finset.sum_const_zero, dif_neg h]

/-- Значение дополнения на старой координате. -/
theorem padTo_castLE {d0 d1 : ℕ} (hdd : d0 ≤ d1) (x : Fin d0 → ℝ) (i : Fin d0) :
    padTo d1 x (Fin.castLE hdd i) = x i := by
  simp only [padTo, Fin.coe_castLE, dif_pos i.isLt]

/-! #### Rotary: старые пары не меняются -/

/-- Индекс пары для координаты j < 2 · half. -/
noncomputable def rotIdx {half : ℕ} (j : Fin (2 * half)) : Fin half :=
  ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩

/-- Партнёр по паре: «j + 1» для чётного j, «j − 1» для нечётного. -/
noncomputable def rotMate {half : ℕ} (j : Fin (2 * half)) : Fin (2 * half) :=
  if h : (j : ℕ) % 2 = 0 then ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
  else ⟨(j : ℕ) - 1, by omega⟩

/-- Rotary на плоском векторе (Надя.txt:198-208: «out[2i] = t0·cos − t1·sin»,
«out[2i+1] = t0·sin + t1·cos»). -/
noncomputable def rotV {half : ℕ} (c s : Fin half → ℝ) (x : Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  fun j => x j * c (rotIdx j)
    + (if (j : ℕ) % 2 = 0 then -x (rotMate j) * s (rotIdx j) else x (rotMate j) * s (rotIdx j))

/-- Rotary линеен по масштабу вектора. -/
theorem rotV_smul {half : ℕ} (c s : Fin half → ℝ) (x : Fin (2 * half) → ℝ) (a : ℝ) :
    rotV c s (fun j => a * x j) = fun j => a * rotV c s x j := by
  funext j
  simp only [rotV]
  split <;> ring

/-- **T2**: при дополнении вектора нулями и дополнении нулями таблиц
cos/sin rotary старых координат идентичен, новые — нули
(Надя.txt:400-404: «f1 = concat(f0, новые)» ⇒ для старых пар
«cos_m/sin_m» совпадают). -/
theorem rotary_old_pairs_unchanged {half0 : ℕ} {half1 : ℕ} (hh : half0 ≤ half1)
    (c0 s0 : Fin half0 → ℝ) (c1 s1 : Fin half1 → ℝ)
    (hc : c1 = padTo half1 c0) (hs : s1 = padTo half1 s0)
    (x : Fin (2 * half0) → ℝ) (j : Fin (2 * half1)) :
    rotV c1 s1 (padTo (2 * half1) x) j
      = if h : (j : ℕ) < 2 * half0 then rotV c0 s0 x ⟨(j : ℕ), h⟩ else 0 := by
  have hj := j.isLt
  have hridx : rotIdx j = ⟨(j : ℕ) / 2, (by omega : (j : ℕ) / 2 < half1)⟩ := rfl
  by_cases hlt : (j : ℕ) < 2 * half0
  · have hpair0 : (j : ℕ) / 2 < half0 := by omega
    have hpair1 : (j : ℕ) / 2 < half1 := lt_of_lt_of_le hpair0 hh
    have hpc : (⟨(j : ℕ) / 2, hpair1⟩ : Fin half1) = Fin.castLE hh ⟨(j : ℕ) / 2, hpair0⟩ := by
      apply Fin.ext; rfl
    have hc1 : c1 ⟨(j : ℕ) / 2, hpair1⟩ = c0 ⟨(j : ℕ) / 2, hpair0⟩ := by
      have h1 : c1 ⟨(j : ℕ) / 2, hpair1⟩ = c1 (Fin.castLE hh ⟨(j : ℕ) / 2, hpair0⟩) := rfl
      rw [h1, hc, padTo]
      exact dif_pos hpair0
    have hs1 : s1 ⟨(j : ℕ) / 2, hpair1⟩ = s0 ⟨(j : ℕ) / 2, hpair0⟩ := by
      have h1 : s1 ⟨(j : ℕ) / 2, hpair1⟩ = s1 (Fin.castLE hh ⟨(j : ℕ) / 2, hpair0⟩) := rfl
      rw [h1, hs, padTo]
      exact dif_pos hpair0
    simp only [rotV, padTo, dif_pos hlt]
    by_cases hp : (j : ℕ) % 2 = 0
    · have hm1 : (j : ℕ) + 1 < 2 * half0 := by omega
      have hm1' : (j : ℕ) + 1 < 2 * half1 := by omega
      have he1 : rotMate j = ⟨(j : ℕ) + 1, hm1'⟩ := by simp [rotMate, hp]
      rw [he1]
      simp only [rotMate, hp, dif_pos hm1]
      have hr0 : rotIdx ⟨(j : ℕ), hlt⟩ = ⟨(j : ℕ) / 2, hpair0⟩ := rfl
      rw [hridx, hc1, hs1, hr0]
      simp
    · have hm1 : (j : ℕ) - 1 < 2 * half0 := by omega
      have hm1' : (j : ℕ) - 1 < 2 * half1 := by omega
      have he1 : rotMate j = ⟨(j : ℕ) - 1, hm1'⟩ := by simp [rotMate, hp]
      rw [he1]
      simp only [rotMate, hp, dif_pos hm1]
      have hr0 : rotIdx ⟨(j : ℕ), hlt⟩ = ⟨(j : ℕ) / 2, hpair0⟩ := rfl
      rw [hridx, hc1, hs1, hr0]
      simp
  · rw [dif_neg hlt]
    simp only [rotV]
    have hc0 : c1 (rotIdx j) = 0 := by
      have hr : rotIdx j = ⟨(j : ℕ) / 2, by omega⟩ := rfl
      have hco : (((rotIdx j : Fin half1) : ℕ)) = (j : ℕ) / 2 := rfl
      have hj' := j.isLt
      rw [hr, hc, padTo]
      exact dif_neg (by omega)
    have hs0 : s1 (rotIdx j) = 0 := by
      have hr : rotIdx j = ⟨(j : ℕ) / 2, by omega⟩ := rfl
      have hco : (((rotIdx j : Fin half1) : ℕ)) = (j : ℕ) / 2 := rfl
      have hj' := j.isLt
      rw [hr, hs, padTo]
      exact dif_neg (by omega)
    rw [hc0, hs0]
    split <;> ring

/-! #### T1: attention score и softmax-веса сохраняются -/

/-- **T1**: после роста head-ширины hd0 → hd1 с масштабом W_q ×√(hd1/hd0)
(Надя.txt:383: «qsc = sqrt(hd1 / hd0)») скалярное произведение rotated K·Q,
делённое на √hd, СОХРАНЯЕТСЯ: новые координаты K и Q — нули (новые
столбцы W_k/W_q нулевые), старые координаты Q умножены на «c», и
«c/√hd1 = 1/√hd0». -/
theorem attn_score_scale_preserved (hd0 hd1 : ℕ) (hhd0 : 0 < hd0) (hhd : hd0 ≤ hd1)
    (Kt Qt : Fin hd0 → ℝ) (Kt1 Qt1 : Fin hd1 → ℝ)
    (hK : Kt1 = padTo hd1 Kt)
    (hQ : Qt1 = padTo hd1 (fun i => Real.sqrt ((hd1 : ℝ) / hd0) * Qt i)) :
    (∑ i : Fin hd1, Kt1 i * Qt1 i) / Real.sqrt hd1
      = (∑ i : Fin hd0, Kt i * Qt i) / Real.sqrt hd0 := by
  have h1 : (0 : ℝ) < hd1 := by
    have h : 0 < hd1 := lt_of_lt_of_le hhd0 hhd
    exact_mod_cast h
  have hs : Real.sqrt ((hd1 : ℝ) / hd0) = Real.sqrt hd1 / Real.sqrt hd0 :=
    Real.sqrt_div (le_of_lt h1) hd0
  have hsum : (∑ i : Fin hd1, Kt1 i * Qt1 i)
      = Real.sqrt ((hd1 : ℝ) / hd0) * ∑ i : Fin hd0, Kt i * Qt i := by
    refine sum_pad_scale hd0 hd1 hhd0 hhd _ _ _ ?_
    apply eq_padTo hhd
    · intro i
      rw [hK, hQ, padTo_castLE, padTo_castLE]
      ring
    · intro i hi
      rw [hK, hQ]
      have hni : ¬ ((i : ℕ) < hd0) := by omega
      simp only [padTo, dif_neg hni]
      ring
  rw [hsum, hs]
  have hs0 : Real.sqrt hd0 ≠ 0 := Real.sqrt_ne_zero'.mpr (mod_cast hhd0)
  have hs1 : Real.sqrt hd1 ≠ 0 := Real.sqrt_ne_zero'.mpr h1
  field_simp

/-- Выход attention (∑ w·V) при равных весах и дополненных нулями V:
старые координаты сохраняются, новые — нули. -/
theorem attn_out_pad (d0 d1 : ℕ) (hdd : d0 ≤ d1) (w w1 : Fin M → ℝ)
    (hw : w1 = w) (V : Fin M → Fin d0 → ℝ) (V1 : Fin M → Fin d1 → ℝ)
    (hV : ∀ m, V1 m = padTo d1 (V m)) :
    (fun i => ∑ m, w1 m * V1 m i) = padTo d1 (fun i => ∑ m, w m * V m i) := by
  apply eq_padTo hdd
  · intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hw, hV m, padTo_castLE]
  · intro i hi
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [hV m]
    have hni : ¬ ((i : ℕ) < d0) := by omega
    simp only [padTo, dif_neg hni, mul_zero]

/-- Остаточный слой x0 + attn·W_o при дополненных attn/x0 и блочно
дополненном W_o (новые строки и столбцы — нули, Надя.txt:389-391). -/
theorem h1_pad (d0 d1 : ℕ) (hd0 : 0 < d0) (hdd : d0 ≤ d1) (x0 : Fin d0 → ℝ)
    (x01 : Fin d1 → ℝ) (hx0 : x01 = padTo d1 x0) (a : Fin d0 → ℝ)
    (a1 : Fin d1 → ℝ) (ha : a1 = padTo d1 a) (W : Fin d0 → Fin d0 → ℝ)
    (W1 : Fin d1 → Fin d1 → ℝ) (hW : W1 = matPadS d1 d1 1 W) :
    (fun i => x01 i + ∑ i', a1 i' * W1 i' i)
      = padTo d1 (fun i => x0 i + ∑ i', a i' * W i' i) := by
  apply eq_padTo hdd
  · intro i
    rw [hx0]
    simp only [padTo_castLE]
    refine congrArg _ ?_
    have hs := sum_pad_scale d0 d1 hd0 hdd 1 (fun i' => a i' * W i' i)
      (fun i' => a1 i' * W1 i' (Fin.castLE hdd i)) ?_
    simp only [one_mul] at hs
    exact hs
    apply eq_padTo hdd
    · intro i'
      rw [ha, hW]
      simp only [matPadS, Fin.coe_castLE, dif_pos i'.isLt, dif_pos i.isLt, padTo_castLE, one_mul]
    · intro i' hi
      rw [hW]
      have hni : ¬ ((i' : ℕ) < d0) := by omega
      simp [matPadS, ha, hni]
  · intro i hi
    have hni : ¬ ((i : ℕ) < d0) := by omega
    rw [hx0]
    simp only [padTo, dif_neg hni, zero_add]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [hW]
    simp only [matPadS]
    split <;> ring

/-! #### T3: послойный носитель grow_width (nh = 1 ⇒ hd = d = 2·half) -/

/-- Параметры одноголового блока «Hagi v2 Optimal» (Надя.txt:215-254):
loc-матрица по срезам, две RMSNorm, attention (rotary + alibi),
swish-FFN, выход в 256 логитов. -/
structure WParams (half h M L : ℕ) where
  /-- rms-eps (при росте ×(d0/d1), Надя.txt:369). -/
  eps : ℝ
  /-- gain первой RMSNorm (Надя.txt:226). -/
  rms1 : Fin (2 * half) → ℝ
  /-- gain второй RMSNorm (Надя.txt:249). -/
  rms2 : Fin (2 * half) → ℝ
  /-- смещение логитов. -/
  b2 : Fin 256 → ℝ
  /-- W_loc: (срез, вход, выход). -/
  wloc : Fin L → Fin (2 * half) → Fin (2 * half) → ℝ
  /-- W_q: (вход, выход). -/
  wq : Fin (2 * half) → Fin (2 * half) → ℝ
  /-- W_k: (вход, выход). -/
  wk : Fin (2 * half) → Fin (2 * half) → ℝ
  /-- W_v: (вход, выход). -/
  wv : Fin (2 * half) → Fin (2 * half) → ℝ
  /-- W_o: (вход, выход). -/
  wo : Fin (2 * half) → Fin (2 * half) → ℝ
  /-- W_g: (вход, выход). -/
  wg : Fin (2 * half) → Fin h → ℝ
  /-- W_u: (вход, выход). -/
  wu : Fin (2 * half) → Fin h → ℝ
  /-- W_d: (вход, выход). -/
  wd : Fin h → Fin (2 * half) → ℝ
  /-- W_out: (вход, логит). -/
  wout : Fin (2 * half) → Fin 256 → ℝ
  /-- cos/sin последней позиции для Q (Надя.txt:234). -/
  csl : Fin half → ℝ
  ssl : Fin half → ℝ
  /-- cos/sin по позициям для K (Надя.txt:189-190). -/
  csm : Fin M → Fin half → ℝ
  ssm : Fin M → Fin half → ℝ
  /-- alibi-смещение (Надя.txt:191). -/
  alibi : Fin M → ℝ

/-- Масштаб gain RMSNorm при росте d0 → d1: √(d0/d1) (Надя.txt:370). -/
noncomputable def dScale (d0 d1 : ℕ) : ℝ := Real.sqrt (((d0 : ℕ) : ℝ) / ((d1 : ℕ) : ℝ))

/-- Масштаб W_q при росте hd0 → hd1: √(hd1/hd0) (Надя.txt:383). -/
noncomputable def qScale (hd0 hd1 : ℕ) : ℝ := Real.sqrt ((hd1 : ℝ) / hd0)

/-- swish: x·sigmoid(x) (Надя.txt:251-253; клип [−20, 20] не формализован). -/
noncomputable def swish (x : ℝ) : ℝ := x / (1 + Real.exp (-x))

/-- x0 = loc_in @ W_loc (Надя.txt:221). -/
noncomputable def wX0 {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) : Fin (2 * half) → ℝ :=
  fun i => ∑ s, ∑ j, P.wloc s j i * v s j

/-- Первая RMSNorm (Надя.txt:226). -/
noncomputable def wN1 {half h M L : ℕ} (P : WParams half h M L) (x : Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  rmsOut P.eps P.rms1 x

/-- Вторая RMSNorm (Надя.txt:249). -/
noncomputable def wN2 {half h M L : ℕ} (P : WParams half h M L) (x : Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  rmsOut P.eps P.rms2 x

/-- Q = x0_n @ W_q (Надя.txt:231). -/
noncomputable def wQ {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) : Fin (2 * half) → ℝ :=
  fun i => ∑ j, P.wq j i * wN1 P (wX0 P v) j

/-- K = C_n @ W_k (Надя.txt:232). -/
noncomputable def wK {half h M L : ℕ} (P : WParams half h M L)
    (c : Fin M → Fin (2 * half) → ℝ) (m : Fin M) : Fin (2 * half) → ℝ :=
  fun i => ∑ j, P.wk j i * wN1 P (c m) j

/-- V = C_n @ W_v (Надя.txt:233). -/
noncomputable def wV {half h M L : ℕ} (P : WParams half h M L)
    (c : Fin M → Fin (2 * half) → ℝ) (m : Fin M) : Fin (2 * half) → ℝ :=
  fun i => ∑ j, P.wv j i * wN1 P (c m) j

/-- Rotary K по позиции m (Надя.txt:240). -/
noncomputable def wKr {half h M L : ℕ} (P : WParams half h M L)
    (c : Fin M → Fin (2 * half) → ℝ) (m : Fin M) : Fin (2 * half) → ℝ :=
  rotV (P.csm m) (P.ssm m) (wK P c m)

/-- Rotary Q по последней позиции (Надя.txt:235-238). -/
noncomputable def wQr {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) : Fin (2 * half) → ℝ :=
  rotV P.csl P.ssl (wQ P v)

/-- Score = (K·Q)/√hd + alibi (Надя.txt:241-244). -/
noncomputable def wScore {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) (m : Fin M) : ℝ :=
  (∑ i, wKr P c m i * wQr P v i) / Real.sqrt ((2 * half : ℕ) : ℝ) + P.alibi m

/-- Softmax-веса attention. -/
noncomputable def wW {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) (m : Fin M) : ℝ :=
  softDef (wScore P v c) m

/-- attn = w @ V (Надя.txt:245-246). -/
noncomputable def wAttn {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  fun i => ∑ m, wW P v c m * wV P c m i

/-- h1 = x0 + attn @ W_o (Надя.txt:247). -/
noncomputable def wH1 {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  fun i => wX0 P v i + ∑ i', wAttn P v c i' * P.wo i' i

/-- gp = h1_n @ W_g (Надя.txt:250). -/
noncomputable def wG {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) : Fin h → ℝ :=
  fun t => ∑ j, P.wg j t * wN2 P (wH1 P v c) j

/-- up = h1_n @ W_u (Надя.txt:253). -/
noncomputable def wU {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) : Fin h → ℝ :=
  fun t => ∑ j, P.wu j t * wN2 P (wH1 P v c) j

/-- swish(gp) (Надя.txt:252). -/
noncomputable def wSw {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) (t : Fin h) : ℝ :=
  swish (wG P v c t)

/-- h2 = h1 + (swish·up) @ W_d (Надя.txt:254). -/
noncomputable def wH2 {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) :
    Fin (2 * half) → ℝ :=
  fun i => wH1 P v c i + ∑ t, wSw P v c t * wU P v c t * P.wd t i

/-- logits = h2 @ W_out + b2 (Надя.txt:269). -/
noncomputable def wLogits {half h M L : ℕ} (P : WParams half h M L)
    (v : Fin L → Fin (2 * half) → ℝ) (c : Fin M → Fin (2 * half) → ℝ) : Fin 256 → ℝ :=
  fun o => ∑ j, P.wout j o * wH2 P v c j + P.b2 o

/-- Правило роста ширины grow_width (Надя.txt:361-410) как предикат на
параметрах: eps ×(d0/d1), gain ×√(d0/d1), W_q ×√(hd1/hd0), остальные
матрицы — блочное дополнение нулями, rotary-таблицы — concat. -/
structure WGrowth {half0 half1 h0 h1 M L : ℕ} (P0 : WParams half0 h0 M L)
    (P1 : WParams half1 h1 M L) : Prop where
  /-- half растёт. -/
  le : half0 ≤ half1
  /-- старая ширина ненулевая. -/
  pos : 0 < half0
  /-- FFN-ширина растёт. -/
  hle : h0 ≤ h1
  /-- старая FFN-ширина ненулевая. -/
  hpos : 0 < h0
  /-- eps ×(d0/d1). -/
  eps : P1.eps = P0.eps * (((2 * half0 : ℕ) : ℝ) / ((2 * half1 : ℕ) : ℝ))
  /-- gain rms1 ×√(d0/d1). -/
  rms1 : P1.rms1 = padTo (2 * half1) (fun i => dScale (2 * half0) (2 * half1) * P0.rms1 i)
  /-- gain rms2 ×√(d0/d1). -/
  rms2 : P1.rms2 = padTo (2 * half1) (fun i => dScale (2 * half0) (2 * half1) * P0.rms2 i)
  /-- b2 без изменения. -/
  b2 : P1.b2 = P0.b2
  /-- W_loc: блочное дополнение нулями. -/
  wloc : ∀ s, P1.wloc s = matPadS (2 * half1) (2 * half1) 1 (P0.wloc s)
  /-- W_q: старый блок ×√(hd1/hd0). -/
  wq : P1.wq = matPadS (2 * half1) (2 * half1) (qScale (2 * half0) (2 * half1)) (P0.wq)
  /-- W_k: блочное дополнение нулями. -/
  wk : P1.wk = matPadS (2 * half1) (2 * half1) 1 (P0.wk)
  /-- W_v: блочное дополнение нулями. -/
  wv : P1.wv = matPadS (2 * half1) (2 * half1) 1 (P0.wv)
  /-- W_o: блочное дополнение нулями. -/
  wo : P1.wo = matPadS (2 * half1) (2 * half1) 1 (P0.wo)
  /-- W_g: блочное дополнение нулями. -/
  wg : P1.wg = matPadS (2 * half1) h1 1 (P0.wg)
  /-- W_u: блочное дополнение нулями. -/
  wu : P1.wu = matPadS (2 * half1) h1 1 (P0.wu)
  /-- W_d: блочное дополнение нулями. -/
  wd : P1.wd = matPadS h1 (2 * half1) 1 (P0.wd)
  /-- W_out: новые строки нулевые. -/
  wout : P1.wout = matPadS (2 * half1) 256 1 (P0.wout)
  /-- cos последней позиции: concat нулями. -/
  csl : P1.csl = padTo half1 P0.csl
  /-- sin последней позиции: concat нулями. -/
  ssl : P1.ssl = padTo half1 P0.ssl
  /-- cos по позициям: concat нулями. -/
  csm : ∀ m, P1.csm m = padTo half1 (P0.csm m)
  /-- sin по позициям: concat нулями. -/
  ssm : ∀ m, P1.ssm m = padTo half1 (P0.ssm m)
  /-- alibi без изменения. -/
  alibi : P1.alibi = P0.alibi

/-- **T3 (main)**: при правиле роста `WGrowth` логиты grown-модели на
дополненных нулями входах равны логитам старой модели ТОЧНО. -/
theorem wlogits_width_preserved {half0 half1 h0 h1 M L : ℕ} {P0 : WParams half0 h0 M L}
    {P1 : WParams half1 h1 M L} (hG : WGrowth P0 P1)
    (v : Fin L → Fin (2 * half0) → ℝ) (c : Fin M → Fin (2 * half0) → ℝ) (o : Fin 256) :
    wLogits P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) o
      = wLogits P0 v c o := by
  have hh : half0 ≤ half1 := hG.le
  have hpos : (0 : ℕ) < half0 := hG.pos
  have hd0 : (0 : ℕ) < 2 * half0 := by omega
  have hle : 2 * half0 ≤ 2 * half1 := by omega
  -- (x0)
  have hx0 : wX0 P1 (fun s => padTo (2 * half1) (v s))
      = padTo (2 * half1) (wX0 P0 v) := by
    apply eq_padTo hle
    · intro i
      show (∑ s, ∑ j, P1.wloc s j (Fin.castLE hle i) * padTo (2 * half1) (v s) j) = wX0 P0 v i
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hG.wloc s]
      have hpi : ((Fin.castLE hle i : Fin (2 * half1)) : ℕ) < 2 * half0 := by simpa using i.isLt
      have hsm := mulvec_matPadS hd0 hle 1 (P0.wloc s) (v s) (padTo (2 * half1) (v s))
        rfl (Fin.castLE hle i)
      rw [dif_pos hpi] at hsm
      have he : (⟨(Fin.castLE hle i : ℕ), hpi⟩ : Fin (2 * half0)) = i := Fin.ext rfl
      simp only [one_mul, he] at hsm
      exact hsm
    · intro i hi
      show (∑ s, ∑ j, P1.wloc s j i * padTo (2 * half1) (v s) j) = 0
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hG.wloc s]
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      have hsm := mulvec_matPadS hd0 hle 1 (P0.wloc s) (v s) (padTo (2 * half1) (v s))
        rfl i
      rw [dif_neg hni] at hsm
      exact hsm
  -- (norm x0 / norm C)
  have hg1 : ∀ j : Fin (2 * half0),
      P1.rms1 (Fin.castLE hle j) = P0.rms1 j *
      Real.sqrt (((2 * half0 : ℕ) : ℝ) / ((2 * half1 : ℕ) : ℝ)) := by
    intro j
    rw [hG.rms1, padTo_castLE]
    unfold dScale
    ring
  have hx0n : wN1 P1 (wX0 P1 (fun s => padTo (2 * half1) (v s)))
      = padTo (2 * half1) (wN1 P0 (wX0 P0 v)) := by
    apply eq_padTo hle
    · intro i
      have hy : ∀ i : Fin (2 * half1), wX0 P1 (fun s => padTo (2 * half1) (v s)) i
          = if h : (i : ℕ) < 2 * half0 then wX0 P0 v ⟨i, h⟩ else 0 := by
        intro i
        rw [hx0]
        rfl
      simp only [wN1, hG.eps]
      exact rmsnorm_scale_inv (2 * half0) (2 * half1) hd0 hle P0.eps (wX0 P0 v) P0.rms1
        (wX0 P1 (fun s => padTo (2 * half1) (v s))) P1.rms1 hy hg1 i
    · intro i hi
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      simp only [wN1, rmsOut]
      rw [hx0, hG.rms1]
      simp only [padTo, dif_neg hni]
      ring
  have hcn : ∀ m, wN1 P1 (padTo (2 * half1) (c m))
      = padTo (2 * half1) (wN1 P0 (c m)) := by
    intro m
    apply eq_padTo hle
    · intro i
      simp only [wN1, hG.eps]
      exact rmsnorm_scale_inv (2 * half0) (2 * half1) hd0 hle P0.eps (c m) P0.rms1
        (padTo (2 * half1) (c m)) P1.rms1 (fun i => rfl) hg1 i
    · intro i hi
      simp only [wN1, rmsOut]
      rw [hG.rms1]
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      simp only [padTo, dif_neg hni]
      ring
  -- (линейный слой с блочным дополнением)
  have hlin : ∀ (W0 : Fin (2 * half0) → Fin (2 * half0) → ℝ)
      (W1 : Fin (2 * half1) → Fin (2 * half1) → ℝ) (s : ℝ)
      (x0 : Fin (2 * half0) → ℝ) (x1 : Fin (2 * half1) → ℝ),
      W1 = matPadS (2 * half1) (2 * half1) s W0 → x1 = padTo (2 * half1) x0 →
      (fun i => ∑ j, W1 j i * x1 j)
        = padTo (2 * half1) (fun i => s * ∑ j, W0 j i * x0 j) := by
    intro W0 W1 s x0 x1 hW hx
    apply eq_padTo hle
    · intro i
      have hpi : ((Fin.castLE hle i : Fin (2 * half1)) : ℕ) < 2 * half0 := by simpa using i.isLt
      have hsm := mulvec_matPadS hd0 hle s W0 x0 x1 hx (Fin.castLE hle i)
      rw [dif_pos hpi] at hsm
      show (∑ j, W1 j (Fin.castLE hle i) * x1 j) = s * ∑ j, W0 j i * x0 j
      rw [hW]
      exact hsm
    · intro i hi
      have hsm := mulvec_matPadS hd0 hle s W0 x0 x1 hx i
      rw [dif_neg (by omega)] at hsm
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      simp only [hW]
      exact hsm
  -- (Q, K, V)
  have hq : wQ P1 (fun s => padTo (2 * half1) (v s))
      = padTo (2 * half1) (fun i => qScale (2 * half0) (2 * half1) * wQ P0 v i) := by
    simp only [wQ]
    exact hlin _ _ _ _ _ hG.wq hx0n
  have hk : ∀ m, wK P1 (fun m => padTo (2 * half1) (c m)) m
      = padTo (2 * half1) (wK P0 c m) := by
    intro m
    unfold wK
    exact (hlin _ _ 1 _ _ hG.wk (hcn m)).trans (funext fun i => by simp only [padTo]; split <;>
      simp)
  have hv : ∀ m, wV P1 (fun m => padTo (2 * half1) (c m)) m
      = padTo (2 * half1) (wV P0 c m) := by
    intro m
    unfold wV
    exact (hlin _ _ 1 _ _ hG.wv (hcn m)).trans (funext fun i => by simp only [padTo]; split <;>
      simp)
  -- (rotary)
  have hkr : ∀ m, wKr P1 (fun m => padTo (2 * half1) (c m)) m
      = padTo (2 * half1) (wKr P0 c m) := by
    intro m
    apply eq_padTo hle
    · intro i
      simp only [wKr]
      have hr := rotary_old_pairs_unchanged hh (P0.csm m) (P0.ssm m) (P1.csm m) (P1.ssm m)
        (hG.csm m) (hG.ssm m) (wK P0 c m) (Fin.castLE hle i)
      rw [dif_pos (by simp)] at hr
      rw [hk m]
      exact hr
    · intro i hi
      simp only [wKr]
      have hr := rotary_old_pairs_unchanged hh (P0.csm m) (P0.ssm m) (P1.csm m) (P1.ssm m)
        (hG.csm m) (hG.ssm m) (wK P0 c m) i
      rw [dif_neg (by omega)] at hr
      rw [hk m]
      exact hr
  have hqr : wQr P1 (fun s => padTo (2 * half1) (v s))
      = padTo (2 * half1) (fun i => qScale (2 * half0) (2 * half1) * wQr P0 v i) := by
    apply eq_padTo hle
    · intro i
      simp only [wQr]
      have hr := rotary_old_pairs_unchanged hh P0.csl P0.ssl P1.csl P1.ssl hG.csl hG.ssl
        (fun i => qScale (2 * half0) (2 * half1) * wQ P0 v i) (Fin.castLE hle i)
      rw [dif_pos (by simp)] at hr
      rw [hq]
      have hs := rotV_smul P0.csl P0.ssl (wQ P0 v) (qScale (2 * half0) (2 * half1))
      exact hr.trans (congrFun hs _)
    · intro i hi
      simp only [wQr]
      have hr := rotary_old_pairs_unchanged hh P0.csl P0.ssl P1.csl P1.ssl hG.csl hG.ssl
        (fun i => qScale (2 * half0) (2 * half1) * wQ P0 v i) i
      rw [dif_neg (by omega)] at hr
      rw [hq]
      exact hr
  -- (score → weights)
  have hscore : ∀ m, (∑ i, wKr P1 (fun m => padTo (2 * half1) (c m)) m i
        * wQr P1 (fun s => padTo (2 * half1) (v s)) i) / Real.sqrt ((2 * half1 : ℕ) : ℝ)
      = (∑ i, wKr P0 c m i * wQr P0 v i) / Real.sqrt ((2 * half0 : ℕ) : ℝ) := fun m =>
    attn_score_scale_preserved _ _ hd0 hle _ _ _ _ (hkr m) hqr
  have hsum : wScore P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = wScore P0 v c := by
    funext m
    simp only [wScore]
    rw [hscore m, hG.alibi]
  have hw : ∀ m, wW P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) m
      = wW P0 v c m := fun m => by simp only [wW]; rw [hsum]
  have hattn : wAttn P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = padTo (2 * half1) (wAttn P0 v c) := by
    unfold wAttn
    exact attn_out_pad _ _ hle _ _ (funext hw) _ _ hv
  -- (h1, norm h1)
  have hh1 : wH1 P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = padTo (2 * half1) (wH1 P0 v c) :=
    h1_pad _ _ hd0 hle _ _ hx0 _ _ hattn _ _ hG.wo
  have hg2 : ∀ j : Fin (2 * half0),
      P1.rms2 (Fin.castLE hle j) = P0.rms2 j *
      Real.sqrt (((2 * half0 : ℕ) : ℝ) / ((2 * half1 : ℕ) : ℝ)) := by
    intro j
    rw [hG.rms2, padTo_castLE]
    unfold dScale
    ring
  have hh1n : wN2 P1 (wH1 P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)))
      = padTo (2 * half1) (wN2 P0 (wH1 P0 v c)) := by
    apply eq_padTo hle
    · intro i
      have hy : ∀ i : Fin (2 * half1), wH1 P1 (fun s => padTo (2 * half1) (v s))
          (fun m => padTo (2 * half1) (c m)) i
          = if h : (i : ℕ) < 2 * half0 then wH1 P0 v c ⟨i, h⟩ else 0 := by
        intro i
        rw [hh1]
        rfl
      simp only [wN2, hG.eps]
      exact rmsnorm_scale_inv (2 * half0) (2 * half1) hd0 hle P0.eps (wH1 P0 v c) P0.rms2
        (wH1 P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)))
        P1.rms2 hy hg2 i
    · intro i hi
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      simp only [wN2, rmsOut]
      rw [hh1, hG.rms2]
      simp only [padTo, dif_neg hni]
      ring
  -- (FFN)
  have hid : ∀ (W0 : Fin (2 * half0) → Fin h0 → ℝ) (W1 : Fin (2 * half1) → Fin h1 → ℝ),
      W1 = matPadS (2 * half1) h1 1 W0 →
      (fun t => ∑ j, W1 j t * wN2 P1 (wH1 P1 (fun s => padTo (2 * half1) (v s))
        (fun m => padTo (2 * half1) (c m))) j)
        = padTo h1 (fun t => ∑ j, W0 j t * wN2 P0 (wH1 P0 v c) j) := by
    intro W0 W1 hW
    funext t
    rw [hW]
    have hsm := mulvec_matPadS hd0 hle 1 W0 _ _ hh1n t
    by_cases ht : (t : ℕ) < h0
    · rw [dif_pos ht] at hsm
      simp only [one_mul] at hsm
      rw [padTo, dif_pos ht]
      exact hsm
    · rw [dif_neg ht] at hsm
      rw [padTo, dif_neg ht]
      exact hsm
  have hgp : wG P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = padTo h1 (wG P0 v c) := by
    unfold wG
    exact hid _ _ hG.wg
  have hup : wU P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = padTo h1 (wU P0 v c) := by
    unfold wU
    exact hid _ _ hG.wu
  have hsw : ∀ t, wSw P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) t
        * wU P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) t
      = padTo h1 (fun t => wSw P0 v c t * wU P0 v c t) t := by
    intro t
    simp only [wSw]
    by_cases ht : (t : ℕ) < h0
    · have hg1' : wG P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) t
          = wG P0 v c ⟨t, ht⟩ := by rw [hgp, padTo]; exact dif_pos ht
      have hu1' : wU P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) t
          = wU P0 v c ⟨t, ht⟩ := by rw [hup, padTo]; exact dif_pos ht
      rw [hg1', hu1', padTo]
      simp only [dif_pos ht]
    · have hg1' : wG P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m)) t
        = 0 := by
        rw [hgp, padTo]
        exact dif_neg ht
      rw [hg1']
      simp only [swish, zero_div, zero_mul, padTo, dif_neg ht]
  -- (h2)
  have hh2 : wH2 P1 (fun s => padTo (2 * half1) (v s)) (fun m => padTo (2 * half1) (c m))
      = padTo (2 * half1) (wH2 P0 v c) := by
    apply eq_padTo hle
    · intro i
      simp only [wH2]
      rw [hh1, padTo_castLE]
      refine congrArg _ ?_
      refine sum_pad h0 h1 hG.hpos hG.hle _ _ ?_
      funext t
      by_cases ht : (t : ℕ) < h0
      · rw [hsw t, hG.wd, padTo]
        simp only [matPadS, Fin.coe_castLE, dif_pos ht, dif_pos i.isLt, one_mul]
        rw [padTo, dif_pos ht]
      · rw [hsw t, hG.wd]
        simp only [matPadS, dif_neg ht, mul_zero]
        rw [padTo, dif_neg ht]
    · intro i hi
      have hni : ¬ ((i : ℕ) < 2 * half0) := by omega
      simp only [wH2]
      rw [hh1]
      simp only [padTo, dif_neg hni, zero_add]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [hG.wd]
      simp only [matPadS, dif_neg hni]
      split <;> ring
  -- (logits)
  simp only [wLogits]
  rw [hG.b2]
  have hlo := mulvec_matPadS hd0 hle 1 P0.wout (wH2 P0 v c) _ hh2 o
  rw [dif_pos o.isLt, one_mul] at hlo
  rw [hG.wout, hlo]


end WidthGrowth

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

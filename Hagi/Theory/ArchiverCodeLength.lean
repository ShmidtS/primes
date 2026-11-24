import Hagi.Probability.FiniteLogScore
import Mathlib

/-!
# ArchiverCodeLength — длина кода против энтропии

Код-факт (HAGI_v2 READ-ONLY @b3740e0, hagi/archiver.py): byte LM —
вероятностная модель 32-бит range coder с 16-бит CDF (`probs_to_cdf`
archiver.py:33-39: freq = max(1, round(P·65200)), остаток до 65536 —
ни один байт не получает нулевую вероятность); `encode_step` :52-70,
`decode_step` :96-118; контейнер `HAGI3 | u32 len | mode`, coded
выбирается, только если строго короче stored (:188). Docstring :1-4
утверждает: archive size within o(1) of -log2 P(data) ⇒ ratio IS CE.

ЧТО ЗДЕСЬ ДОКАЗАНО (L2, модель идеального кодера; НЕ модель реального
range coder):

* `codelength_ge_entropy_of_kraft` — Kraft ⇒ H(p) ≤ E[len] (биты):
  из Σ 2^{-len} ≤ 1 и Gibbs (через `ceDef_self_le_of_support`).
* `codelength_ge_entropy_of_uniquelyDecodable` — гипотеза Kraft
  выводится из Mathlib Kraft–McMillan для uniquely decodable кода.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.ArchiverCodeLength

open Hagi.Prelude
open Hagi.Probability.FiniteLogScore
open scoped BigOperators

variable {X : Type*} [Fintype X]

/-- Ожидаемая длина кода `len` (в битах) под `p`. -/
noncomputable def expLen (p : X → ℝ) (len : X → ℕ) : ℝ := ∑ x, p x * (len x : ℝ)

/-- Энтропия в битах: `entDef / log 2`. -/
noncomputable def entBits (p : X → ℝ) : ℝ := entDef p / Real.log 2

/-- Cross-entropy в битах: `ceDef / log 2`. -/
noncomputable def ceBits (p q : X → ℝ) : ℝ := ceDef p q / Real.log 2

theorem one_div_two_pow (n : ℕ) : (1 / (2 : ℝ)) ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
  have h : (-(n : ℝ) : ℝ) = ((-n : ℤ) : ℝ) := by push_cast; ring
  rw [h, Real.rpow_intCast]
  simp

theorem log_two_rpow_neg (n : ℕ) : Real.log ((2 : ℝ) ^ (-(n : ℝ))) = -(n : ℝ) * Real.log 2 :=
  Real.log_rpow (by norm_num) _

theorem log_two_pos : (0 : ℝ) < Real.log 2 :=
  Real.log_pos (show (1 : ℝ) < 2 by norm_num)

/-- Kraft ⇒ H(p) ≤ E[len] (биты). -/
theorem codelength_ge_entropy_of_kraft
    (p : X → ℝ) (len : X → ℕ) [Nonempty X]
    (hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1)
    (hkraft : ∑ x, (1 / (2 : ℝ)) ^ (len x) ≤ 1) :
    entBits p ≤ expLen p len := by
  classical
  have hK0 : 0 < ∑ x, (1 / (2 : ℝ)) ^ (len x) :=
    Finset.sum_pos (fun x _ => pow_pos (by norm_num) _) Finset.univ_nonempty
  set K : ℝ := ∑ x, (1 / (2 : ℝ)) ^ (len x) with hKdef
  set q : X → ℝ := fun x => (1 / (2 : ℝ)) ^ (len x) / K with hqdef
  have hq : ∀ x, 0 ≤ q x := fun x => by
    rw [hqdef]; positivity
  have hsum_q : ∑ x, q x = 1 := by
    rw [hqdef, ← Finset.sum_div]; exact div_self (ne_of_gt hK0)
  have hpq : ∀ x, 0 < p x → 0 < q x := fun x _ => by
    rw [hqdef]; positivity
  have hgibbs := ceDef_self_le_of_support p q hp hq hsum_p hsum_q hpq
  have hce : ceDef p q = Real.log 2 * expLen p len + Real.log K := by
    have h1 : ∀ x ∈ Finset.univ,
        p x * Real.log (q x) = p x * (-(len x : ℝ) * Real.log 2 - Real.log K) := by
      intro x _
      rw [hqdef, Real.log_div (by positivity) (ne_of_gt hK0),
        one_div_two_pow, log_two_rpow_neg]
    unfold ceDef expLen
    have hrew : ∀ x ∈ Finset.univ,
        -(p x * Real.log (q x)) = Real.log 2 * (p x * (len x : ℝ)) + p x * Real.log K :=
      fun x _ => by rw [h1 x (Finset.mem_univ x)]; ring
    calc -(∑ x ∈ Finset.univ, p x * Real.log (q x))
        = ∑ x ∈ Finset.univ, -(p x * Real.log (q x)) := (Finset.sum_neg_distrib _).symm
      _ = ∑ x ∈ Finset.univ, (Real.log 2 * (p x * (len x : ℝ)) + p x * Real.log K) :=
          Finset.sum_congr rfl hrew
      _ = Real.log 2 * ∑ x ∈ Finset.univ, p x * (len x : ℝ) + Real.log K := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum_p, one_mul, Finset.mul_sum]
  rw [hce] at hgibbs
  have hlogK : Real.log K ≤ 0 := Real.log_nonpos (le_of_lt hK0) hkraft
  change entDef p / Real.log 2 ≤ ∑ x, p x * (len x : ℝ)
  rw [div_le_iff₀ log_two_pos]
  change -∑ x, p x * Real.log (p x) ≤ (∑ x, p x * (len x : ℝ)) * Real.log 2
  have hg : -∑ x, p x * Real.log (p x)
      ≤ ∑ x, Real.log 2 * (p x * (len x : ℝ)) + Real.log K := by
    have h := hgibbs
    rw [show expLen p len = ∑ x, p x * (len x : ℝ) from rfl, Finset.mul_sum] at h
    exact h
  rw [Finset.sum_mul]
  have heq : ∑ x, p x * (len x : ℝ) * Real.log 2
      = ∑ x, Real.log 2 * (p x * (len x : ℝ)) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [heq]
  linarith

/-- Kraft–McMillan: uniquely decodable код удовлетворяет Kraft. -/
theorem codelength_ge_entropy_of_uniquelyDecodable
    (p : X → ℝ) (enc : X → List Bool) [Nonempty X]
    (henc : Function.Injective enc)
    (hud : InformationTheory.IsUniquelyDecodable (Set.range enc))
    (hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1) :
    entBits p ≤ expLen p (fun x => (enc x).length) := by
  classical
  apply codelength_ge_entropy_of_kraft p _ hp hsum_p
  have himg : ((Finset.univ.image enc : Finset (List Bool)) : Set (List Bool))
      = Set.range enc := by simp
  have hk := InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := Finset.univ.image enc) (by rw [himg]; exact hud)
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hk
  have h2 : ∑ w ∈ Finset.univ.image enc, (1 / (2 : ℝ)) ^ w.length
      = ∑ x ∈ Finset.univ, (1 / (2 : ℝ)) ^ (enc x).length :=
    Finset.sum_image (fun a _ b _ hab => henc hab)
  rw [← h2]
  exact hk

/-- log₂. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Длина идеального кодера: `⌈−log₂ q x⌉₊`. -/
noncomputable def idealLen (q : X → ℝ) (x : X) : ℕ := ⌈-log2 (q x)⌉₊

/-- Кодовая длина идеального кодера удовлетворяет Kraft-слагаемому:
`(1/2)^idealLen ≤ q`. -/
theorem one_div_two_pow_idealLen_le (q : ℝ) (hq : 0 < q) :
    (1 / (2 : ℝ)) ^ ⌈-log2 q⌉₊ ≤ q := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hce : -log2 q ≤ ((⌈-log2 q⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h1 : (2 : ℝ) ^ (-((⌈-log2 q⌉₊ : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-(-log2 q)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(-log2 q)) = q := by
    rw [neg_neg, log2, Real.rpow_def_of_pos (by norm_num)]
    have hl : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
    have hq0 : q ≠ 0 := ne_of_gt hq
    rw [show Real.log 2 * (Real.log q / Real.log 2) = Real.log q by field_simp]
    exact Real.exp_log hq
  rw [one_div_two_pow]
  exact h1.trans_eq h2

/-- Идеальный кодер `⌈−log₂ p̂⌉₊` удовлетворяет Kraft. -/
theorem idealLen_kraft (q : X → ℝ) (hq : ∀ x, 0 < q x)
    (hsum_q : ∑ x, q x = 1) : ∑ x, (1 / (2 : ℝ)) ^ idealLen q x ≤ 1 := by
  calc ∑ x, (1 / (2 : ℝ)) ^ idealLen q x ≤ ∑ x, q x :=
        Finset.sum_le_sum fun x _ => one_div_two_pow_idealLen_le _ (hq x)
    _ = 1 := hsum_q

/-- Нижняя граница для идеального кодера: H(p) ≤ E_p[⌈−log₂ p̂⌉₊]. -/
theorem idealLen_ge_entropy (p q : X → ℝ) [Nonempty X]
    (hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hsum_q : ∑ x, q x = 1) :
    entBits p ≤ expLen p (idealLen q) :=
  codelength_ge_entropy_of_kraft p _ hp hsum_p (idealLen_kraft q hq hsum_q)

/-- L2b: идеальный кодер платит не больше CE + 1 бит. -/
theorem idealLen_le_ce_add_one (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum_p : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hq1 : ∀ x, q x ≤ 1) :
    expLen p (idealLen q) ≤ ceBits p q + 1 := by
  have hlt (x : X) : (idealLen q x : ℝ) < -log2 (q x) + 1 := by
    have hq0 : 0 ≤ -log2 (q x) := by
      have h1 : Real.log (q x) ≤ 0 := Real.log_nonpos (le_of_lt (hq x)) (hq1 x)
      unfold log2
      have h2 : 0 ≤ -(Real.log (q x)) := neg_nonneg.mpr h1
      have h3 := div_nonneg h2 (le_of_lt log_two_pos)
      rwa [neg_div] at h3
    have := Nat.ceil_lt_add_one hq0
    exact_mod_cast this
  have hs : ∑ x, p x * (idealLen q x : ℝ) ≤ ∑ x, p x * (-log2 (q x) + 1) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le_of_lt (hlt x)) (hp x)
  have hce : (∑ x, p x * (-log2 (q x) + 1)) = ceBits p q + 1 := by
    have hterm (x : X) : p x * (-log2 (q x) + 1) = -(p x * Real.log (q x)) / Real.log 2 + p x := by
      rw [log2, mul_add, mul_one]
      have hl : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
      field_simp
    unfold ceBits
    change ∑ x, p x * (-log2 (q x) + 1) = ceDef p q / Real.log 2 + 1
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_add_distrib,
      ← Finset.sum_div, hsum_p]
    unfold ceDef
    rw [Finset.sum_neg_distrib]
  change ∑ x, p x * (idealLen q x : ℝ) ≤ ceBits p q + 1
  exact hs.trans_eq hce

/-- CE в битах = H + KL/log 2 (мост к `klDef_eq_ceDef_sub_of_support`). -/
theorem ceBits_eq_entBits_add_kl (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpq : ∀ x, 0 < p x → 0 < q x) :
    ceBits p q = entBits p + klDef p q / Real.log 2 := by
  have h := klDef_eq_ceDef_sub_of_support p q hp hpq
  have h2 : ceDef p q - ceDef p p = klDef p q := h.symm
  have hce : ceDef p p = entDef p := rfl
  rw [hce] at h2
  unfold ceBits entBits
  have hk : klDef p q / Real.log 2 = (ceDef p q - entDef p) / Real.log 2 := by rw [h2]
  rw [hk, sub_div]
  ring

/-- L3: p̂ = p ⇒ KL = 0, идеальный кодер платит H(p) плюс меньше бита:
`H(p) ≤ E_p[⌈−log₂ p⌉₊] ≤ H(p) + 1`. -/
theorem idealLen_self_bounds (p : X → ℝ) [Nonempty X]
    (hp : ∀ x, 0 < p x) (hsum_p : ∑ x, p x = 1) :
    entBits p ≤ expLen p (idealLen p) ∧ expLen p (idealLen p) ≤ entBits p + 1 := by
  refine ⟨idealLen_ge_entropy p p (fun x => le_of_lt (hp x)) hsum_p hp hsum_p, ?_⟩
  have hle1 : ∀ x, p x ≤ 1 := fun x => by
    have h := Finset.single_le_sum (f := p) (fun y _ => le_of_lt (hp y)) (Finset.mem_univ x)
    rw [hsum_p] at h
    exact h
  have h := idealLen_le_ce_add_one p p (fun x => le_of_lt (hp x)) hsum_p hp hle1
  have hk : klDef p p = 0 := by
    unfold Hagi.Prelude.klDef
    apply Finset.sum_eq_zero
    intro x _
    rw [div_self (ne_of_gt (hp x)), Real.log_one, mul_zero]
  have hce := ceBits_eq_entBits_add_kl p p (fun x => le_of_lt (hp x)) (fun x _ => hp x)
  rw [hk, zero_div, add_zero] at hce
  rw [hce] at h
  exact h

end Hagi.Theory.ArchiverCodeLength

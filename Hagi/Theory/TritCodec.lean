/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
set_option linter.style.openClassical false

/-!
# The trit codec bridge — 5 trits per byte

The codec (`hagi/trunk_ops.py:375`:
packed 5-trit/byte, «3^5=243<=2^8») packs a group of
five ternary digits into one byte:

* code: `tritPack t = Σ tᵢ · 3^i` (pack_trits5, trunk_ops.py:386);
* decode: digit `i = (v / 3^i) % 3` (unpack_trits5,
  trunk_ops.py:404-408).

Since `3^5 = 243 ≤ 256 = 2^8`, every 5-trit group fits in one byte.
This module proves the codec core only:

* `tritPack_lt_243` — the `code < 243` guard (trunk_ops.py:391)
  always holds;
* `trit_roundtrip` — decode ∘ encode = id (unpack (pack t) = t);
* `tritPack_injective` — distinct groups get distinct codes
  (a free corollary of the round-trip).

Adaptive context is out of scope here (see AdaptiveContext).
-/

namespace Hagi.Theory.TritCodec

/-- pack_trits5 (trunk_ops.py:386): код группы 5 тритов —
смешанная система, `Σ tᵢ · 3^i` (позиция i имеет вес 3^i). -/
def tritPack (t : Fin 5 → Fin 3) : ℕ :=
  ∑ j ∈ Finset.range 5,
    (t ⟨j % 5, Nat.mod_lt j (by norm_num : (0 : ℕ) < 5)⟩ : ℕ) * 3 ^ j

/-- unpack_trits5 (trunk_ops.py:404-408): цифра i = `(v / 3^i) % 3`. -/
def tritUnpack (v : ℕ) : Fin 5 → Fin 3 := fun i =>
  ⟨v / 3 ^ (i : ℕ) % 3, by
    have h := Nat.mod_lt (v / 3 ^ (i : ℕ)) (by norm_num : (0 : ℕ) < 3)
    omega⟩

/-! ## Ключевая арифметика позиционного кода -/

/-- Младшая часть суммы: для цифр < 3 сумма `∑_{j<i} c j · 3^j < 3^i`. -/
theorem sum_range_pow_lt : ∀ (i : ℕ) (c : ℕ → ℕ), (∀ j, j < i → c j < 3) →
    (∑ j ∈ Finset.range i, c j * 3 ^ j) < 3 ^ i := by
  intro i
  induction i with
  | zero => intro c _; simp
  | succ i ih =>
    intro c hc
    have hlt := ih c (fun j hj => hc j (Nat.lt_succ_of_lt hj))
    rw [Finset.sum_range_succ]
    have hci : c i < 3 := hc i (Nat.le_refl _)
    have hmul : c i * 3 ^ i ≤ 2 * 3 ^ i :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : 3 ^ (i + 1) = 3 * 3 ^ i := by ring
    rw [h3]
    omega

/-- Позиционная декомпозиция: цифра i восстанавливается из кода
делением и взятием остатка (`(v / 3^i) % 3`, unpack_trits5). -/
theorem digit_of_sum (k i : ℕ) (c : ℕ → ℕ) (hc : ∀ j, j < k → c j < 3)
    (hik : i < k) :
    (∑ j ∈ Finset.range k, c j * 3 ^ j) / 3 ^ i % 3 = c i := by
  -- хвост: выделяем цифру i и выносим 3^(i+1) из старших членов
  have htail : ∑ x ∈ Finset.range (k - i), c (i + x) * 3 ^ (i + x)
      = c i * 3 ^ i
        + 3 ^ (i + 1) * ∑ j ∈ Finset.range (k - i - 1),
            c (i + 1 + j) * 3 ^ j := by
    have hsplit1 : k - i = (k - i - 1) + 1 := by omega
    rw [hsplit1, Finset.sum_range_succ']
    have hfac : ∀ x ∈ Finset.range (k - i - 1),
        c (i + (x + 1)) * 3 ^ (i + (x + 1))
            = 3 ^ (i + 1) * (c (i + 1 + x) * 3 ^ x) := by
      intro x _; rw [show i + (x + 1) = i + 1 + x from by omega, pow_add]
      ring
    rw [Finset.sum_congr rfl hfac, Finset.mul_sum]
    have hidx2 : k - i - 1 + 1 - 1 = k - i - 1 := by omega
    rw [Nat.add_zero, hidx2]
    exact Nat.add_comm _ _
  -- полная декомпозиция: low + 3^i · (c i + 3 · d)
  have hsplit : (∑ j ∈ Finset.range k, c j * 3 ^ j)
      = (∑ j ∈ Finset.range i, c j * 3 ^ j)
        + 3 ^ i * (c i + 3 * ∑ j ∈ Finset.range (k - i - 1),
            c (i + 1 + j) * 3 ^ j) := by
    have hadd : k = i + (k - i) := by omega
    have hidx : i + (k - i) - i - 1 = k - i - 1 := by omega
    rw [hadd, Finset.sum_range_add, hidx, htail]
    ring
  have hlow : (∑ j ∈ Finset.range i, c j * 3 ^ j) < 3 ^ i :=
    sum_range_pow_lt i c (fun j hj => hc j (by omega))
  have hci : c i < 3 := hc i hik
  -- единственность div/mod
  obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique (b := 3 ^ i) (by norm_num)).mpr
    ⟨hsplit.symm, hlow⟩
  rw [hd]
  omega

/-! ## Ядро кодека -/

/-- GUARD ВСЕГДА ЗАКРЫТ: код любой 5-тритной группы < 243 = 3⁵
(assert trunk_ops.py:391 недостижим, каждая группа — один байт). -/
theorem tritPack_lt_243 (t : Fin 5 → Fin 3) : tritPack t < 243 := by
  have h5 : (3 : ℕ) ^ 5 = 243 := by norm_num
  have hlt := sum_range_pow_lt 5
    (fun j => (t ⟨j % 5, Nat.mod_lt j (by norm_num : (0 : ℕ) < 5)⟩ : ℕ))
    (fun j _ => Fin.is_lt _)
  rw [h5] at hlt
  exact hlt

/-- ROUND-TRIP: unpack (pack t) = t — кодирование группы 5 тритов
и последующее декодирование восстанавливает группу точно
(trunk_ops.py:395, позиционная система без потерь). -/
theorem trit_roundtrip (t : Fin 5 → Fin 3) :
    tritUnpack (tritPack t) = t := by
  ext i
  show (tritPack t) / 3 ^ (i : ℕ) % 3 = (t i : ℕ)
  rw [tritPack,
    digit_of_sum 5 (i : ℕ)
      (fun j => (t ⟨j % 5, Nat.mod_lt j (by norm_num : (0 : ℕ) < 5)⟩ : ℕ))
      (fun j _ => Fin.is_lt _) (by omega)]
  have hmod : (⟨(i : ℕ) % 5, Nat.mod_lt (i : ℕ)
      (by norm_num : (0 : ℕ) < 5)⟩ : Fin 5) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.is_lt)
  rw [hmod]

/-- ИНЪЕКТИВНОСТЬ: разные 5-тритные группы дают разные коды
(base-3 единственность при фиксированной длине группы = 5). -/
theorem tritPack_injective (t₁ t₂ : Fin 5 → Fin 3)
    (h : tritPack t₁ = tritPack t₂) : t₁ = t₂ := by
  rw [← trit_roundtrip t₁, ← trit_roundtrip t₂, h]

end Hagi.Theory.TritCodec

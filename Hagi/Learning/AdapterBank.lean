/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
open Matrix

/-!
# AdapterBank — адаптеры низкого ранга: тождество при рождении и цена параметров

`trunk_ops.py`: `LowRankAdapter(d, r)`: `A = N(0,1)/√d` формы `r×d`, `B = 0`
формы `d×r`, выход `f + B·(A·f)`; `AdapterBank(d, r = 2)` — по адаптеру на
домен, приём через `paired_margin_eb` (HAGI_v2 414ede5, PROPOSAL 13).

* `adapterOut A B f = f + B·(A·f)`;
* `adapter_init_identity` — при `B = 0` адаптер тождественен: новый адаптер не
  меняет выход ствола (влияние растёт только обучением `B`);
* `rank_one_cheap_iff` — ранг 1 не дороже полной `m×n` (`m, n ≥ 1`) ⇔ `m, n ≥ 2`;
* `rank_two_cheap` — ранг 2 (default банка) при `d ≥ 4`: `2·2d ≤ d²`.
-/

namespace Hagi.Learning.AdapterBank

/-- Адаптер низкого ранга: `f ↦ f + B·(A·f)`, `A : r×d`, `B : d×r`, `B = 0` при
инициализации. -/
noncomputable def adapterOut {d r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (f : Fin d → ℝ) : Fin d → ℝ :=
  f + B *ᵥ (A *ᵥ f)
/-- При `B = 0` адаптер — тождество: новый адаптер не меняет выход ствола. -/
theorem adapter_init_identity {d r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ)
    (f : Fin d → ℝ) : adapterOut A (0 : Matrix (Fin d) (Fin r) ℝ) f = f := by
  unfold adapterOut
  simp [Matrix.mulVec]
/-- Ранг 1 не дороже полной матрицы `m×n` (`m, n ≥ 1`) ⇔ обе стороны `≥ 2`
(при `m = n = 1` полная матрица дешевле). -/
theorem rank_one_cheap_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    1 * (m + n) ≤ m * n ↔ 2 ≤ m ∧ 2 ≤ n := by
  have hcast : ((1 * (m + n) : ℕ) : ℤ) = (m:ℤ) + n ∧ ((m * n : ℕ) : ℤ) = (m:ℤ) * n := by
    constructor <;> push_cast <;> ring
  constructor
  · intro h
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m <;> simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.add_comm,
        Nat.mul_one, le_refl] at h ⊢ <;> omega
    · rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · interval_cases n <;> simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.add_comm,
          Nat.mul_one, le_refl] at h ⊢ <;> omega
      · exact ⟨hm2, hn2⟩
  · rintro ⟨h2m, h2n⟩
    have e1 : (0:ℤ) < (m:ℤ) - 1 := by exact_mod_cast (show 0 < m - 1 by omega)
    have e2 : (0:ℤ) < (n:ℤ) - 1 := by exact_mod_cast (show 0 < n - 1 by omega)
    have : (m:ℤ) + n ≤ (m:ℤ) * n := by nlinarith [mul_pos e1 e2]
    have h2 : ((1 * (m + n) : ℕ) : ℤ) ≤ ((m * n : ℕ) : ℤ) := by
      rw [hcast.1, hcast.2]; exact this
    exact_mod_cast h2
/-- Число параметров адаптера ранга 2 при `d ≥ 4` не больше `d²`: `2·2d ≤ d²`. -/
theorem rank_two_cheap (d : ℕ) (hd : 4 ≤ d) : 2 * (d + d) ≤ d * d := by
  have e : (2:ℤ) < d := by exact_mod_cast (show 2 < d by omega)
  have : ((2:ℤ)) * ((d:ℤ) + d) ≤ (d:ℤ) * d := by nlinarith
  exact_mod_cast this

end Hagi.Learning.AdapterBank

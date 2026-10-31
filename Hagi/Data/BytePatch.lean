import Mathlib

/-!
# BytePatch (источник №77: Cartesia "From Tokens to Bytes"
# — byte-level H-Net; байтовые патчи вместо токенов)

Вход из N байтов группируется в патчи по p байтов —
последовательность сокращается до ⌈N/p⌉ позиций.

1. `patch_cover`: p·⌈N/p⌉ ≥ N — патчи покрывают вход;
2. `patch_le_raw`: при p ≥ 1 патчей не больше, чем байтов;
3. `patch_real_bound`: ⌈N/p⌉ ≤ N/p + 1 — компактность;
4. `patch_attn_saving`: экономия квадратичного внимания
   (⌈N/p⌉² < N² при p ≥ 2, N ≥ 2p).
-/

namespace Hagi.Data.BytePatch

/-- Число патчей размера p для N байтов. -/
noncomputable def patchCount (N p : ℕ) : ℕ := ⌈(N : ℝ) / p⌉₊

/-- ПОКРЫТИЕ: p·⌈N/p⌉ ≥ N — все байты представлены. -/
theorem patch_cover (N p : ℕ) (hp : 0 < p) :
    N ≤ p * patchCount N p := by
  have hRp : (0:ℝ) < p := by exact_mod_cast hp
  have hceil : ((N : ℝ) / p) ≤ ((patchCount N p : ℝ)) :=
    Nat.le_ceil _
  have hkey : (N : ℝ) ≤ (p : ℝ) * ((patchCount N p : ℝ)) := by
    calc (N : ℝ) = p * ((N : ℝ) / p) := by field_simp
      _ ≤ p * ((patchCount N p : ℝ)) :=
          mul_le_mul_of_nonneg_left hceil (le_of_lt hRp)
  have hfinal : (N : ℝ) ≤ ((p * patchCount N p : ℕ) : ℝ) := by
    push_cast
    linarith [hkey]
  exact_mod_cast hfinal

/-- НЕ УДЛИНЯЕТ: при p ≥ 1 патчей не больше, чем байтов. -/
theorem patch_le_raw (N p : ℕ) (hp : 0 < p) :
    patchCount N p ≤ N := by
  have hRp : (0:ℝ) < p := by exact_mod_cast hp
  have hNn : (0:ℝ) ≤ N := by positivity
  have hnm : N * 1 ≤ N * p := Nat.mul_le_mul_left N hp
  have h1 : (N:ℝ) / p ≤ (N:ℝ) := by
    rw [div_le_iff₀ hRp]
    have hcast : ((N * p : ℕ) : ℝ) = (N:ℝ) * p := by push_cast; ring
    have hh : ((N * 1 : ℕ) : ℝ) ≤ ((N * p : ℕ) : ℝ) := by exact_mod_cast hnm
    simp only [Nat.mul_one] at hh
    linarith [hh, hNn, hRp]
  exact Nat.ceil_le.mpr h1

/-- КОМПАКТНОСТЬ (вещественная форма): ⌈N/p⌉ ≤ N/p + 1. -/
theorem patch_real_bound (N p : ℕ) :
    (patchCount N p : ℝ) < (N:ℝ) / p + 1 :=
  Nat.ceil_lt_add_one (a := (N:ℝ)/p) (by positivity)

/-- ЭКОНОМИЯ КВАДРАТИЧНОГО ВНИМАНИЯ: при p ≥ 2 и N ≥ 2p
квадратичная стоимость внимания на патчах строго меньше
сырой: (⌈N/p⌉)² < N². -/
theorem patch_attn_saving (N p : ℕ) (hp : 2 ≤ p) (hN : 2 * p ≤ N) :
    (patchCount N p : ℝ)^2 < (N : ℝ)^2 := by
  have hRp : (0:ℝ) < p := by exact_mod_cast (Nat.lt_of_lt_of_le (by omega) hp)
  have hNpos : (0:ℝ) < N := by
    have : (0:ℕ) < N := by omega
    exact_mod_cast this
  have hdiv2 : ((N:ℝ) / p) ≤ (N:ℝ) / 2 := by
    have hnat : N * 2 ≤ N * p := Nat.mul_le_mul_left N hp
    have hrc : ((N * 2 : ℕ) : ℝ) ≤ ((N * p : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hc1 : ((N * 2 : ℕ) : ℝ) = (N:ℝ) * 2 := by push_cast; ring
    have hc2 : ((N * p : ℕ) : ℝ) = (N:ℝ) * p := by push_cast; ring
    rw [hc1, hc2] at hrc
    exact (div_le_div_iff₀ hRp (by norm_num : (0:ℝ) < 2)).mpr hrc

  have hpc : (patchCount N p : ℝ) < (N:ℝ) / p + 1 := patch_real_bound N p
  have h4 : (4:ℝ) ≤ N := by
    have : (4:ℕ) ≤ N := by omega
    exact_mod_cast this
  have hNn2 : (0:ℝ) ≤ N := le_of_lt hNpos
  have hhalf : ((N:ℝ))/2 ≤ N - 2 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [h4]
  have hlt : (patchCount N p : ℝ) < (N:ℝ) := by
    linarith [hpc, hdiv2, hhalf]
  have hPCnn : (0:ℝ) ≤ (patchCount N p : ℝ) := Nat.cast_nonneg _
  have hint1 : (0:ℝ) ≤ (patchCount N p : ℝ) * (N - patchCount N p) :=
    mul_nonneg hPCnn (by linarith)
  have hint2 : (0:ℝ) ≤ (N:ℝ) * (N - patchCount N p) :=
    mul_nonneg hNn2 (by linarith)
  nlinarith [hint1, hint2]

end Hagi.Data.BytePatch

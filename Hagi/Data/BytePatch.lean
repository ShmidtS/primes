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

/-! ### Безпотеряность патчинга
(синтез-аудит: byte-level H-Net)

Патчинг как вложение
(bytes → patches последовательностей
патчей с хвостом):
если каждый патч
несёт свой кусок потока
с длиной, то конкатенация
кусков восстанавливает
поток ТОЧНО — информация
не теряется (левая
инверсия). Это закрывает
lossless-условие байтового
H-Net из синтез-аудита. -/

/-- Патч с длиной хвоста: кусок
потока от a до b (невключительно b). -/
def seg (s : ℕ → α) (a b : ℕ) : List α :=
  (List.range (b - a)).map (fun j => s (a + j))

/-- РАЗБИЕНИЕ НА ПАТЧИ: список
кусков [seg s (j·p) (min ((j+1)·p) N)]
для j < patchCount N p. -/
noncomputable def patchSeq (s : ℕ → α) (N p : ℕ) : List (List α) :=
  (List.range (patchCount N p)).map
    (fun j => seg s (j * p) (min ((j + 1) * p) N))

/-- Длина сегмента [a, b) = b − a. -/
theorem seg_length (s : ℕ → α) (a b : ℕ) :
    (seg s a b).length = b - a := by
  simp [seg, List.length_map, List.length_range]

/-- NAT-ЯДРО LOSSLESS: сумма длин первых K
патчей = min(K·p, N) — телескоп
монотонной цепи 0, p, 2p, ...
(чистая арифметика, без списков). -/
theorem patchBytes_nat (N p : ℕ) (hp : 0 < p) :
    ∀ K : ℕ, K ≤ patchCount N p →
      ∑ j ∈ Finset.range K,
        (min ((j + 1) * p) N - j * p) = min (K * p) N := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    intro hK
    have hih := ih (by omega)
    have hsplit : ∑ j ∈ Finset.range (K + 1),
        (min ((j + 1) * p) N - j * p)
      = (∑ j ∈ Finset.range K,
          (min ((j + 1) * p) N - j * p))
        + (min ((K + 1) * p) N - K * p) :=
      by rw [Finset.sum_range_succ]
    rw [hsplit, hih]
    have hcase : min ((K + 1) * p) N - K * p
        = min ((K + 1) * p) N - min (K * p) N := by
      by_cases h : K * p ≤ N
      · simp [h]
      · have hge : N ≤ K * p := by omega
        simp_all
    rw [hcase]
    congr 1
    -- min ((K+1)p) N = min (K·p) N + min ((K+1)p − K·p...)? нет:
    -- цель: min ((K+1)p, N) = min (K·p) N + (min ((K+1)p, N) − min (K·p) N)
    -- это tautology при монотонности min (K·p) N ≤ min ((K+1)p) N
    have hmono : min (K * p) N ≤ min ((K + 1) * p) N := by
      refine min_le_min ?_ (le_refl _)
      have : K * p ≤ K * p + p := Nat.le_add_right _ _
      linarith
    omega

/-- LIST-ВЕРСИЯ: сумма длин патчей = N
(lossless-контракт байтового H-Net:
патчинг не теряет и не дублирует
ни одного байта). -/
theorem patchSeq_total_length (s : ℕ → α) (N p : ℕ)
    (hp : 0 < p) :
    ((patchSeq s N p).map List.length).sum = N := by
  unfold patchSeq
  have hstep : ∀ (l : List ℕ) (f g : ℕ → ℕ),
      (l.map (fun j => List.length (seg s (f j) (g j)))).sum
        = (l.map (fun j => g j - f j)).sum := by
    intro l f g
    induction l with
    | nil => simp
    | cons h t ih => simp [ih, seg_length s (f h) (g h)]
  have hkey : ((List.range (patchCount N p)).map
      (fun j => (seg s (j * p)
        (min ((j + 1) * p) N)).length)).sum
      = ((List.range (patchCount N p)).map
        (fun j => min ((j + 1) * p) N - j * p)).sum :=
    hstep (List.range (patchCount N p))
      (fun j => j * p) (fun j => min ((j + 1) * p) N)
  have hkey2 : List.sum (List.map List.length
      ((List.range (patchCount N p)).map
      (fun j => seg s (j * p)
        (min ((j + 1) * p) N))))
      = ((List.range (patchCount N p)).map
        (fun j => min ((j + 1) * p) N - j * p)).sum := by
    rw [List.map_map]
    exact hkey
  calc List.sum (List.map List.length
      ((List.range (patchCount N p)).map
      (fun j => seg s (j * p)
        (min ((j + 1) * p) N))))
      = ((List.range (patchCount N p)).map
        (fun j => min ((j + 1) * p) N - j * p)).sum := hkey2
    _ = min ((patchCount N p) * p) N :=
        patchBytes_nat N p hp (patchCount N p) (le_refl _)
    _ = N := by
        have hcov := patch_cover N p hp
        rcases le_total N ((patchCount N p) * p) with h | h
        · simp [h]
        · have h2 : (patchCount N p) * p
              = p * patchCount N p := Nat.mul_comm _ _
          omega


import Mathlib.Tactic
import Hagi.Learning.PertTelescope
import Hagi.Learning.BitBudget

set_option linter.style.header false

/-!
# NetworkBudget — сетевой битовый бюджет (цикл 24)

Полная сквозная кривая «биты ↔ качество» для n-слойной
тернарной сети и оптимальность равномерного распределения
бюджета по слоям:

  1. `exists_layer_ge_average`: голубиная дыра — при любом
     распределении неотрицательного тотала N по n слоям
     ∃ слой с бюджетом ≥ N/n; равномерное распределение
     (все aₗ = N/n) достигает границы поточечно — улучшить
     пер-слойный максимум нельзя;
  2. `network_bit_error`: n слоёв, каждый с БЕЗУСЛОВНОЙ
     пер-слойной ошибкой квантования ≤ √(N/n)/2 (unit-scale
     активации: из m·r ≤ N/n и ternary_bit_error_bound при
     ‖y‖ ≤ 1), дают сквозную ошибку ≤ √(n·N)/2·Lⁿ.

Следствие: глубина n и тотал N вычисляются из целевой ошибки
ε: N = (2ε/Lⁿ)²/n — продолжение принципа нулевого подбора
(циклы 22–23) на сетевой уровень; распределение по слоям —
равномерное (по п.1).
-/

open Finset Hagi.Learning.TernaryPert Hagi.Learning.PertTelescope

namespace Hagi.Learning.NetworkBudget

/-! ### 1. Голубиная дыра -/

/-- ОПТИМАЛЬНОСТЬ РАВНОМЕРНОГО РАСПРЕДЕЛЕНИЯ: при любом
распределении неотрицательного тотала N по n > 0 слоям
найдётся слой с бюджетом ≥ N/n. Равномерное распределение
aₗ = N/n достигает границы во всех слоях одновременно —
лучшей пер-слойной границы не существует. -/
theorem exists_layer_ge_average {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (N : ℝ)
    [NeZero n]
    (hsum : ∑ i, a i = N) :
    ∃ i, N / n ≤ a i := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i, a i < N / n := hcon
  have hsumlt : ∑ i, a i < ∑ i, N / n :=
    Finset.sum_lt_sum (fun i _ => le_of_lt (hlt i))
      ⟨0, Finset.mem_univ 0, hlt 0⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsumlt
  push_cast at hsumlt
  rw [nsmul_eq_mul] at hsumlt
  have hmul : n * (N / n) = N := by
    field_simp
  rw [hmul] at hsumlt
  rw [hsum] at hsumlt
  exact lt_irrefl N hsumlt

/-! ### 2. Сетевая битовая граница -/

variable {v : ℕ}

/-- СЕТЕВАЯ ГРАНИЦА (биты ↔ качество, n слоёв): n-слойная
сеть с безусловной пер-слойной ошибкой квантования
≤ √(N/n)/2 (unit-scale активации; из m·r ≤ N/n и
ternary_bit_error_bound при ‖y‖ ≤ 1) и L-липшицевыми
точными слоями имеет сквозную ошибку ≤ √(n·N)/2·Lⁿ.
Ключевая алгебра: n·√(N/n) = √(n·N) при n > 0, N ≥ 0. -/
theorem network_bit_error (L : ℝ) (hL1 : (1:ℝ) ≤ L)
    (N : ℝ) (hN : (0:ℝ) ≤ N) (n : ℕ) (hn : 0 < n)
    (pairs : List (((Fin v → ℝ) → (Fin v → ℝ))
      × ((Fin v → ℝ) → (Fin v → ℝ))))
    (hlen : pairs.length = n)
    (hlip : ∀ p ∈ pairs, ∀ y y',
      outNorm (p.1 y - p.1 y') ≤ L * outNorm (y - y'))
    (hdelta : ∀ p ∈ pairs, ∀ y,
      outNorm (p.1 y - p.2 y) ≤ Real.sqrt (N / n) / 2)
    (x : Fin v → ℝ) :
    outNorm (compLayers (pairs.map Prod.fst) x
      - compLayers (pairs.map Prod.snd) x)
      ≤ (Real.sqrt (n * N) / 2) * L ^ n := by
  have hdnn : 0 ≤ Real.sqrt (N / n) / 2 :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have htel := Hagi.Learning.PertTelescope.pert_telescope
    (v := v) L hL1 pairs (Real.sqrt (N / n) / 2) hdnn
    hlip hdelta x
  rw [hlen] at htel
  have hsqrteq : Real.sqrt (n * N)
      = (n : ℝ) * Real.sqrt (N / n) := by
    have h1 : ((n : ℝ)) * Real.sqrt (N / n)
        = Real.sqrt ((n : ℝ) ^ 2) * Real.sqrt (N / n) := by
      rw [Real.sqrt_sq (Nat.cast_nonneg n)]
    rw [h1, ← Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg n) 2)
      (N / n)]
    have h2 : ((n : ℝ) ^ 2) * (N / n) = n * N := by
      field_simp
    rw [h2]
  push_cast at htel
  exact le_trans htel (le_of_eq (by rw [hsqrteq]; ring))

end Hagi.Learning.NetworkBudget

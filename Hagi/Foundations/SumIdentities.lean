import Mathlib

/-!
# Sum identities: проекционные тождества сумм

Канонический дом (аудит v9 §3.2): разложение суммы квадратов
отклонений от константы — variance/Koenig–Huygens-тождество,
используемое нормализациями (LayerNorm, RMSNorm, SwitchMoE)
и RL-нормировками (GRPO). Живёт в нижнем слое, чтобы
архитектурные модули не зависели от RL (аудит v9, находка 9).
-/

namespace Hagi.Foundations.SumIdentities

open Finset

variable {n : ℕ}

/-- Сумма отклонений от среднего равна нулю. -/
theorem sum_sub_mean_zero (r : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, (r i - (∑ j, r j) / n) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hS : ∑ i, (r i - (∑ j, r j) / n)
      = (∑ i, r i) - n * ((∑ j, r j) / n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const]
    simp
  have hc : n * ((∑ j, r j) / n) = ∑ j, r j := by
    rw [mul_comm, div_mul_cancel₀ _ hn']
  rw [hS, hc, sub_self]

/-- Разложение: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)². -/
theorem sq_decomp (r : Fin n → ℝ) (hn : 0 < n) (c : ℝ) :
    ∑ i, (r i - c) ^ 2
      - ∑ i, (r i - (∑ j, r j) / n) ^ 2
      = n * ((∑ j, r j) / n - c) ^ 2 := by
  have hz : ∑ i, (r i - (∑ j, r j) / n) = 0 :=
    sum_sub_mean_zero r hn
  set m : ℝ := (∑ j, r j) / n with hm
  have hpe : ∀ i, (r i - c) ^ 2 - (r i - m) ^ 2
      = 2 * (r i - m) * (m - c) + (m - c) ^ 2 := by
    intro i
    ring
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hpe i)]
  rw [Finset.sum_add_distrib]
  have hterm1 : ∑ i, 2 * (r i - m) * (m - c) = 0 := by
    rw [show (0:ℝ) = 2 * (m - c) * ∑ i, (r i - m) from by
        rw [hz]
        ring]
    rw [Finset.mul_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => r i - m)
      (a := 2 * (m - c))]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hterm1, Finset.sum_const]
  simp [Finset.card_univ, Fintype.card_fin]

end Hagi.Foundations.SumIdentities

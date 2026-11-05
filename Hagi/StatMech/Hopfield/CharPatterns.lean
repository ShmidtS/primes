import Mathlib.Tactic
import Hagi.StatMech.Hopfield.Model
import Hagi.Learning.HadamardParseval

set_option linter.style.header false

/-!
# CharPatterns — память Хопфилда на характерах (цикл 30)

Замыкание ПАМЯТЬ ↔ АРХИТЕКТУРА: паттерны памяти = характеры
Адамара (базис доменов HRCN). Тогда энергия любой конфигурации
ВЫЧИСЛЯЕТСЯ ТОЧНО через Parseval (цикл 26):
  Σ_w ⟨χ_w, v⟩² = 2^k·‖v‖²  ⇒
  E_char(v) = Σ_w ⟨χ_w, v⟩²/(2·2^k) = ‖v‖²/2.
Для спиновых конфигураций (‖σ‖² = N = 2^k):
  E_char(σ) = N/2 ДЛЯ ВСЕХ σ — ПЛОСКИЙ ЛАНДШАФТ.

Ёмкостный вывод: полный базис характеров как паттерны памяти
НЕ ДИСКРИМИНИРУЕТ конфигурации (энергия константна) — партицион
вычисляется точно: Z = 2^N·e^{βN/2}, свободная энергия =
log 2 + β/2. Память, несущая информацию, должна быть
ПОДмножеством/переобученной комбинацией доменов (спектральный
выбор цикла 27): нулевые домены — нулевой бюджет, ненулевые —
пропорционально энергии. Хвост: связь с Model.energy —
канонический reindex Fin (2^k) ≃ куб.
-/

open Finset Hagi.Core

namespace Hagi.StatMech.Hopfield.CharPatterns

open Hagi.StatMech.Hopfield Hagi.Learning.HadamardProjectors
  Hagi.Learning.HadamardParseval

variable {k : ℕ}

/-- Спины на кубе (cube-форма Model.spins). -/
def cubSpins (σ : (Fin k → ZMod 2) → Bool) :
    (Fin k → ZMod 2) → ℝ := fun i => if σ i then 1 else -1

/-- Матрица паттернов-характеров: строки — χ_w, w ∈ куб. -/
noncomputable def sylvesterRR (k : ℕ) :
    Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  Matrix.of fun w i => charRowR w i

/-- Энергия памяти на характерах (куб-форма Model.energy):
E_char(v) = Σ_w (χ_w ⬝ᵥ v)²/(2·2^k). -/
noncomputable def charEnergy (v : (Fin k → ZMod 2) → ℝ) : ℝ :=
  ∑ w, (dotProduct (charRowR w) v) ^ 2 / (2 * (2 ^ k : ℕ))

/-- ТОЧНАЯ энергия: E_char(v) = ‖v‖²/2 — прямой вывод из
Parseval (Σ_w ⟨χ_w,v⟩² = 2^k·‖v‖²). Характерная память
сохраняет ровно половину энергии сигнала для ЛЮБОГО входа. -/
theorem charEnergy_eq (v : (Fin k → ZMod 2) → ℝ) :
    charEnergy v = dotProduct v v / 2 := by
  unfold charEnergy
  -- Σ_w ⟨χw,v⟩² = 2^k · Σ_w ‖P_w v‖² = 2^k·‖v‖²
  have hnorm : ∀ w : Fin k → ZMod 2,
      (dotProduct (charRowR w) v) ^ 2
        = (2 ^ k : ℕ) * dotProduct (charProjR w v) (charProjR w v) := by
    intro w
    rw [charProjR_norm_sq]
    have h2 : ((2:ℕ)^k : ℝ) ≠ 0 := by positivity
    field_simp
  have hsum : ∑ w, (dotProduct (charRowR w) v) ^ 2
      = (2 ^ k : ℕ) * dotProduct v v := by
    rw [Finset.sum_congr rfl (fun w _ => hnorm w), ← Finset.mul_sum,
      parseval v]
  have hNpos : (0:ℝ) < ((2:ℕ)^k : ℝ) := by positivity
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hsum2 : ∑ w, (dotProduct (charRowR w) v) ^ 2 / (2 * (2 ^ k : ℕ))
      = ((2 ^ k : ℕ) * dotProduct v v) / (2 * (2 ^ k : ℕ)) := by
    rw [← Finset.sum_div, hsum]
  rw [hsum2]
  field_simp

/-- Спиновая норма: ⟨σ, σ⟩ = N = 2^k. -/
theorem spins_dot_self (σ : (Fin k → ZMod 2) → Bool) :
    dotProduct (cubSpins σ) (cubSpins σ) = (((2:ℕ)^k : ℕ) : ℝ) := by
  have hterm : ∀ i, (cubSpins σ i) * (cubSpins σ i) = 1 := by
    intro i
    unfold cubSpins
    rcases σ i with _ | _
    · simp
    · simp
  have hcard : ∑ i : Fin k → ZMod 2, (1:ℝ)
      = ((2:ℕ)^k : ℝ) := by
    simp
  unfold dotProduct
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), hcard]
  push_cast
  congr 1

/-- ПЛОСКИЙ ЛАНДШАФТ: энергия спиновой конфигурации в
характерной памяти = N/2 для ВСЕХ конфигураций. Полный базис
доменов как паттерны — нулевая дискриминация: партицион
точно 2^N·e^{βN/2}. -/
theorem charEnergy_spins_flat (σ : (Fin k → ZMod 2) → Bool) :
    charEnergy (cubSpins σ) = ((2 ^ k : ℕ) : ℝ) / 2 := by
  rw [charEnergy_eq, spins_dot_self]

end Hagi.StatMech.Hopfield.CharPatterns

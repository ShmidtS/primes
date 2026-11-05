import Mathlib.Tactic
import Hagi.StatMech.Hopfield.Concentration

set_option linter.style.header false

/-!
# LowerBound — двусторонний зажим партициона Хопфилда (цикл 29)

Верхняя граница Z (цикл 28: Z ≤ 2^N·e^{β‖J‖²_F/2})
дополняется нижней через СВИДЕТЕЛЯ-МАКСИМУМ: на конечном кубе
существует σ* с E(σ) ≤ E(σ*) для всех σ, откуда
  Z = Σ_σ e^{βE(σ)} ≥ e^{βE(σ*)}.
Двусторонний зажим свободной энергии:
  β·E(σ*)/N ≤ (1/N)·log Z ≤ log 2 + β·‖J‖²_F/(2N).
Ёмкость: слева — энергия лучшего паттерна (вычисляемый
свидетель), справа — норма. Обе границы конструктивны.
-/

open Finset Hagi.Core

namespace Hagi.StatMech.Hopfield.LowerBound

open Hagi.StatMech.Hopfield Hagi.StatMech.Hopfield.Concentration

/-- Свидетель-максимум: на непустом конечном кубе есть
конфигурация с максимальной энергией. -/
theorem exists_max_energy {N K : ℕ} (hN : 0 < N)
    (J : Matrix (Fin K) (Fin N) ℝ) :
    ∃ σ₀ : Fin N → Bool, ∀ σ : Fin N → Bool,
      energy N K J σ ≤ energy N K J σ₀ := by
  have hne : Nonempty (Fin N → Bool) := ⟨fun _ => false⟩
  exact Finite.exists_max (energy N K J)

/-- НИЖНЯЯ ГРАНИЦА: партицион не меньше вклада свидетеля:
Z ≥ e^{β·E(σ₀)} для любой (в т.ч. максимальной) конфигурации. -/
theorem partition_ge_witness {N K : ℕ} (beta : ℝ)
    (J : Matrix (Fin K) (Fin N) ℝ) (σ₀ : Fin N → Bool) :
    Real.exp (beta * energy N K J σ₀) ≤ partition N K beta J := by
  unfold partition
  have hsingle : Real.exp (beta * energy N K J σ₀)
      ≤ ∑ σ : Fin N → Bool, Real.exp (beta * energy N K J σ) :=
    Finset.single_le_sum
      (f := fun σ : Fin N → Bool => Real.exp (beta * energy N K J σ))
      (fun σ _ => Real.exp_nonneg _)
      (Finset.mem_univ σ₀)
  exact hsingle

/-- НИЖНЯЯ ГРАНИЦА СВОБОДНОЙ ЭНЕРГИИ через максимум:
(1/N)·log Z ≥ β·E(σ*)/N. -/
theorem freeEnergy_ge_max {N K : ℕ} [NeZero N] (beta : ℝ)
    (J : Matrix (Fin K) (Fin N) ℝ) :
    ∃ σ₀ : Fin N → Bool,
      beta * energy N K J σ₀ / ((N:ℕ):ℝ)
        ≤ freeEnergyDensity N K beta J := by
  have hN : (0:ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨σ₀, hmax⟩ := exists_max_energy hN J
  refine ⟨σ₀, ?_⟩
  have hw := partition_ge_witness beta J σ₀
  have hZpos : 0 < partition N K beta J := partition_pos N K beta J
  have hlog : Real.log (Real.exp (beta * energy N K J σ₀))
      ≤ Real.log (partition N K beta J) :=
    Real.log_le_log (Real.exp_pos _) hw
  unfold freeEnergyDensity
  have hNpos : (0:ℝ) < ((N:ℕ):ℝ) := by exact_mod_cast hN
  rw [Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hNpos.le
  rwa [← div_le_div_iff₀ hNpos] at hmul

/-- ДВУСТОРОННИЙ ЗАЖИМ свободной энергии памяти:
β·E(σ*)/N ≤ (1/N)·log Z ≤ log 2 + β·‖J‖²_F/(2N).
Слева — лучший паттерн (конструктивный свидетель), справа —
норма матрицы паттернов. Ёмкость вычисляется с двух сторон. -/
theorem freeEnergy_sandwich {N K : ℕ} [NeZero N] (beta : ℝ)
    (hβ : 0 ≤ beta) (J : Matrix (Fin K) (Fin N) ℝ) :
    ∃ σ₀ : Fin N → Bool,
      beta * energy N K J σ₀ / ((N:ℕ):ℝ)
        ≤ freeEnergyDensity N K beta J
      ∧ freeEnergyDensity N K beta J
        ≤ Real.log 2 + beta * frobSq J / (2 * ((N:ℕ):ℝ)) := by
  obtain ⟨σ₀, h1⟩ := freeEnergy_ge_max beta J
  exact ⟨σ₀, h1, freeEnergy_le beta hβ J⟩

end Hagi.StatMech.Hopfield.LowerBound

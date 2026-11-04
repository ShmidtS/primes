import Mathlib.Tactic

/-!
# Hopfield Model — конечный объём (StatMech слой)

Классическая модель Хопфилда: конфигурации {−1,+1}^N
(кодировка Fin N → Bool), матрица паттернов J (K×N),
energy E(σ;J) = ‖J·σ‖²/(2N) (в статье гамильтониан
H = −E; партицион Z = Σ exp(β·E(σ)) эквивалентен статье с
обратной температурой β). Термодинамический предел НЕ
заявляется доказанным — это конечный слой.
-/

namespace Hagi.StatMech.Hopfield

/-- Спин-значение кодировки: false = −1, true = +1. -/
def spinOf (b : Bool) : ℝ := if b then 1 else -1

/-- Спиновая конфигурация как ℝ-вектор. -/
def spins {N : ℕ} (σ : Fin N → Bool) : Fin N → ℝ :=
  fun i => spinOf (σ i)

/-- Энергия согласия (в статье −гамильтониан):
E(σ;J) = Σ_k (J·σ)_k² / (2N) ≥ 0. -/
noncomputable def energy (N K : ℕ) (J : Matrix (Fin K) (Fin N) ℝ)
    (σ : Fin N → Bool) : ℝ :=
  ∑ k, (J.mulVec (spins σ) k) ^ 2 / (2 * N : ℝ)

/-- Партицион-функция: Z = Σ_σ exp(β·E(σ;J)). -/
noncomputable def partition (N K : ℕ) (beta : ℝ)
    (J : Matrix (Fin K) (Fin N) ℝ) : ℝ :=
  ∑ σ : (Fin N → Bool), Real.exp (beta * energy N K J σ)

/-- Конечная свободная энергия на спин: (1/N)·log Z.
Термодинамический предел давления НЕ заявляется. -/
noncomputable def freeEnergyDensity (N K : ℕ) (beta : ℝ)
    (J : Matrix (Fin K) (Fin N) ℝ) : ℝ :=
  Real.log (partition N K beta J) / N

section BasicFacts

/-- Партицион-функция строго положительна. -/
theorem partition_pos (N K : ℕ) (beta : ℝ)
    (J : Matrix (Fin K) (Fin N) ℝ) : 0 < partition N K beta J := by
  unfold partition
  refine Finset.sum_pos' (fun σ _ => Real.exp_nonneg _)
    ⟨fun _ => true, Finset.mem_univ _, Real.exp_pos _⟩

/-- Нижняя граница: Z ≥ 2^N при β ≥ 0 (все члены ≥ 1). -/
theorem partition_ge_univ (N K : ℕ) (beta : ℝ)
    (hβ : 0 ≤ beta) (J : Matrix (Fin K) (Fin N) ℝ) :
    2 ^ N ≤ partition N K beta J := by
  have hper : ∀ σ : Fin N → Bool,
      (1:ℝ) ≤ Real.exp (beta * energy N K J σ) := by
    intro σ
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hβ (by
      unfold energy
      positivity)
  have hcard : ∑ σ : (Fin N → Bool), (1:ℝ) = 2 ^ N := by
    simp
  calc partition N K beta J
      = ∑ σ : (Fin N → Bool), Real.exp (beta * energy N K J σ) :=
        rfl
    _ ≥ ∑ σ : (Fin N → Bool), (1:ℝ) :=
        Finset.sum_le_sum (fun σ _ => hper σ)
    _ = 2 ^ N := hcard

end BasicFacts

end Hagi.StatMech.Hopfield

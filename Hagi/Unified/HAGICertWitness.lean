/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.ArchitectureTheorem

set_option linter.style.header false

/-!
# Свидетель невакуумности HAGICert (этап 7 рецензии)

Рецензия просила примеры-свидетели невакуумности для
`CorePremises` (есть: `Unified.Nonvacuity`) и `HAGICert`.
Этот модуль даёт второй: КОНКРЕТНЫЙ горизонт-1 сертификат с
явными числами.

Свидетель — арифметика (честно отмечено в рецензии): он
доказывает совместимость посылок (включая окно
C₀(1+γk)^T ≤ C*, в котором hpl_up ∧ hpl_lo не противоречат
росту), а не качество реального обучения.

Параметры: σ = 1/2, C* = 2, C₀ = 1 → C₁ = 3/2;
γ = ρ = k = 1/2, D₀ = D₁ = 1, ξ = 1/8, ηT = 1, g₀ = 1/2;
risk/best/r/ε0/R — нулевые, ρe = 1/2.
-/

open Finset

namespace Hagi.HAGICertWitness

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

noncomputable def witnessState (cap df : ℝ) : Hagi.GrowthState X where
  weightDim := 0
  weights := fun _ => 0
  params := 0
  experts := 0
  energy := 0
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := df
  capability := cap
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  growGain := 0
  growCost := 0
  growRisk := 0
  growEnergy := 0
  mergeEnergy := 0
  mergeRisk := 0
  jointEnergy := 0
  jointRisk := 0
  jointCost := 0
  quantErr := 0
  compressEnergy := 0
  compressRisk := 0

/-- Траектория-свидетель: C₀ = 1, C₁ = 3/2, дальше C₀. -/
noncomputable def witnessTraj : ℕ → Hagi.GrowthState X :=
  fun t => if t = 0 then witnessState 1 1
    else if t = 1 then witnessState (3/2) 1
    else witnessState 1 1

private theorem eq_zero_of_mem_range_one {t : ℕ} (ht : t ∈ Finset.range 1) :
    t = 0 := by
  have h1 := Finset.mem_range.mp ht
  omega

/-- **Свидетель невакуумности HAGICert на горизонте T = 1**:
все поля сертификата выполняются на конкретной траектории с
явными числами (в том числе hpl_up ∧ hpl_lo внутри окна
C₀(1+γk) ≤ C*). -/
theorem hagicert_nonvacuous :
    ∃ (S : ℕ → Hagi.GrowthState X) (g : ℕ → ℝ)
      (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
      (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ),
      HAGICert S g risk best r γ ρ k ξ ηT Cstar σ ε0 ρe R T := by
  refine ⟨witnessTraj, fun _ => 1/2, fun _ _ => 0, fun _ => 0,
    fun _ => 0, 1/2, 1/2, 1/2, 1/8, 1, 2, 1/2, 0, 1/2, 0, 1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t <;> simp only [witnessTraj, witnessState] <;> norm_num
  case refine_2 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t
    simp only [witnessTraj, witnessState, usableFrontier]
    norm_num
  case refine_3 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t
    simp only [witnessTraj, witnessState, usableFrontier]
    norm_num
  case refine_4 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t
    simp only [witnessTraj, witnessState, usableFrontier]
    norm_num
  case refine_5 => norm_num
  case refine_6 =>
    simp only [witnessTraj, witnessState, usableFrontier]
    norm_num
  case refine_7 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t
    simp only [witnessTraj, witnessState]
    norm_num
  case refine_8 =>
    intro t ht
    have h1 := Finset.mem_range.mp ht
    interval_cases t
    simp only [witnessTraj, witnessState]
    norm_num
  case refine_9 => norm_num
  case refine_10 => norm_num
  case refine_11 => norm_num
  case refine_12 =>
    simp only [witnessTraj, witnessState]
    norm_num
  case refine_13 =>
    intro t ht
    norm_num
  case refine_14 => norm_num
  case refine_15 => norm_num
  case refine_16 => norm_num
  case refine_17 => norm_num

end Hagi.HAGICertWitness

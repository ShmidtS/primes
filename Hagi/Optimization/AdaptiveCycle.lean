/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Optimization.InexactContraction
import Hagi.Optimization.SubspaceGrowth
import Hagi.Optimization.DirectionPacking
import Hagi.Energy.Variational

set_option linter.style.header false

namespace Hagi.Optimization

open InnerProductSpace

/-!
# AdaptiveCycle — полный адаптивный цикл HAGI

Сводная теорема программы «три геометрии»: внешний цикл
(рост подпространства по остатку проекции, конечность
C₀/δ расширений из `growth_finite`) × внутренний цикл
(пересчёт до останова: сжатие с полом квантования и явный
K-горизонт из `inexact_contraction_halt`). Полный цикл
«расширение → пересчёт → останов» ограничен:
(N расширений)·δ ≤ C₀ и на каждом расширении внутренняя
ошибка достигает допуска τ за конечный горизонт K.
-/

/-- **Полный адаптивный цикл: граница числа расширений.**
Если метрика покрытия неотрицательна и каждое принятое
расширение улучшает её минимум на δ > 0, то любое число
принятых расширений N ≤ C₀/δ — рост архитектуры конечен.
Вместе с `inexact_contraction_halt` (внутренний пересчёт
останавливается за явный K-горизонт на каждом расширении)
это замыкает полный цикл «расширение → пересчёт → останов»
геометрически адаптивной HAGI. -/
theorem adaptive_cycle_expansions (C : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hstepC : ∀ k : ℕ, C (k+1) ≤ C k - δ) (hC : ∀ j : ℕ, 0 ≤ C j)
    (N : ℕ) :
    (N:ℝ) ≤ C 0 / δ := by
  have h := growth_finite C δ hδ hstepC hC N
  exact (le_div_iff₀ hδ).mpr h


/-- **Архитектурный контракт адаптивной HAGI («три
геометрии»)**: единая сводная теорема, связывающая все три
геометрических контроллера:

1. **Упаковка** (`welch_min_dimension`): размерность d
   вмещает M различимых направлений с смешением μ только
   при M/(1+(M−1)μ²) ≤ d;
2. **Рост** (`adaptive_cycle_expansions`): число расширений
   архитектуры конечно, N ≤ C₀/δ;
3. **Сходимость** (`inexact_contraction_halt`): внутренний
   пересчёт достигает допуска τ за явный горизонт K при
   квантованном полу ε/(1−q).

Вместе: растущая модель с ограниченной размерностью по
измеримой нагрузке, конечным числом расширений и
сертифицированным остановом. -/
theorem adaptive_hagi_contract {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {d : ℕ} [FiniteDimensional ℝ F]
    (_b : OrthonormalBasis (Fin d) ℝ F) {M : ℕ} (u : Fin M → F)
    (hu : ∀ i, ‖u i‖ = 1) (μ : ℝ) (hμ : ∀ i k, i ≠ k → |⟪u i, u k⟫_ℝ| ≤ μ)
    (hM : 2 ≤ M) (hd : 0 < d) (hμ0 : 0 ≤ μ)
    (C : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hCstep : ∀ k : ℕ, C (k+1) ≤ C k - δ) (hC : ∀ j : ℕ, 0 ≤ C j) (N : ℕ)
    (x : ℕ → ℝ) (q ε τ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k : ℕ, x (k+1) ≤ q * x k + ε)
    (B : ℝ) (hB0 : 0 < B) (hB : x 0 ≤ B) (K : ℕ)
    (hK : q ^ (K : ℝ) < (τ - ε / (1 - q)) / B) :
    (M:ℝ) / (1 + ((M:ℝ) - 1) * μ^2) ≤ (d:ℝ)
      ∧ (N:ℝ) ≤ C 0 / δ
      ∧ x K < τ :=
  ⟨welch_min_dimension _b u hu μ hμ hM hd hμ0,
   adaptive_cycle_expansions C δ hδ hCstep hC N,
   inexact_contraction_halt x q ε τ hq0 hq1 hε hstep B hB0 hB K hK⟩


/-- **Полный архитектурный контракт адаптивной HAGI (четыре
оси)**: расширение `adaptive_hagi_contract` термодинамической
осью — если коридор температур непуст (s/τ ≤ ε/log n), то
существует T, дающая одновременно различимость и качество.
Четыре оси: размерность (Уэлч) × конечный рост × honest
останов × термодинамический коридор. -/
theorem adaptive_hagi_contract_thermal {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {d : ℕ} [FiniteDimensional ℝ F]
    (_b : OrthonormalBasis (Fin d) ℝ F) {M : ℕ} (u : Fin M → F)
    (hu : ∀ i, ‖u i‖ = 1) (μ : ℝ) (hμ : ∀ i k, i ≠ k → |⟪u i, u k⟫_ℝ| ≤ μ)
    (hM : 2 ≤ M) (hd : 0 < d) (hμ0 : 0 ≤ μ)
    (C : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hCstep : ∀ k : ℕ, C (k+1) ≤ C k - δ) (hC : ∀ j : ℕ, 0 ≤ C j) (N : ℕ)
    (x : ℕ → ℝ) (q ε τ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k : ℕ, x (k+1) ≤ q * x k + ε)
    (B : ℝ) (hB0 : 0 < B) (hB : x 0 ≤ B) (K : ℕ)
    (hK : q ^ (K : ℝ) < (τ - ε / (1 - q)) / B)
    {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → ℝ)
    (s : ℝ) (hs : 0 < s) (hτ : 0 < τ) (hε2 : 0 < ε)
    (hn : 2 ≤ Fintype.card ι)
    (hcorridor : s / τ ≤ ε / Real.log ((Fintype.card ι : ℕ):ℝ)) :
    (M:ℝ) / (1 + ((M:ℝ) - 1) * μ^2) ≤ (d:ℝ)
      ∧ (N:ℝ) ≤ C 0 / δ
      ∧ x K < τ
      ∧ ∃ T : ℝ, 0 < T
          ∧ (∀ i j, |L j - L i| ≤ s →
              |Real.log (Hagi.Prelude.softDef (fun x => -L x / T) i)
                - Real.log (Hagi.Prelude.softDef (fun x => -L x / T) j)| ≤ τ)
          ∧ (∃ m : ℝ, (∀ i, m ≤ L i)
              ∧ (∑ i, Hagi.Prelude.softDef (fun x => -L x / T) i * L i
                  ≤ m + T * Real.log ((Fintype.card ι : ℕ):ℝ))
              ∧ T * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε) := by
  have hc := adaptive_hagi_contract _b u hu μ hμ hM hd hμ0 C δ hδ hCstep hC N
    x q ε τ hq0 hq1 hε hstep B hB0 hB K hK
  exact ⟨hc.1, hc.2.1, hc.2.2,
    Hagi.Energy.temperature_corridor L s τ ε hs hτ hε2 hn hcorridor⟩

end Hagi.Optimization

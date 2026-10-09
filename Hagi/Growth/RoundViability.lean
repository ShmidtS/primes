/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainDecomposition

/-!
# RoundViability — критерий stop/continue для цикла

Критерий по измеряемой энергии разногласия `devEnergy dev`
свежего семейства экспертов:

* `round_exhausted`: если `devEnergy dev = 0` и `GainOp`, то
  `ρ·D − ξ ≤ D'` и `η·devEnergy dev = 0`;
* `round_viable`: при `GainOp` с эффективностью `η_p·η_s`,
  точном шаге, `ρ ≥ γk`, конусе и пороге
  `γk²·C + (1−ρ)k·C + ξ ≤ (η_p·η_s)·devEnergy dev` следует
  `k·C' ≤ D'`;
* `cycle_criterion`: импликация из `devEnergy dev = 0` в вывод
  `round_exhausted`.
-/

namespace Hagi

open Finset

variable {N : ℕ} [NeZero N] {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- Если `devEnergy dev = 0` и `GainOp D D' dev ρ η ξ`, то
`ρ·D − ξ ≤ D'` и `η·devEnergy dev = 0`. -/
theorem round_exhausted (D D' : ℝ) (ρ η ξ : ℝ) (dev : Fin N → V)
    (hzero : devEnergy dev = 0)
    (hop : GainOp D D' dev ρ η ξ) :
    ρ * D - ξ ≤ D' ∧ η * devEnergy dev = 0 := by
  refine ⟨?_, ?_⟩
  · have h : ρ * D + η * devEnergy dev - ξ ≤ D' := hop
    rw [hzero, mul_zero, add_zero] at h
    exact h
  · rw [hzero, mul_zero]

/-- Если `C' = C + γ·D`, `GainOp D D' dev ρ (η_p·η_s) ξ`,
`γ·k ≤ ρ`, `k·C ≤ D`, `γ·k²·C + (1−ρ)·k·C + ξ
≤ (η_p·η_s)·devEnergy dev` и `0 < devEnergy dev`,
то `k·C' ≤ D'` (обёртка `gainop_cone_step`). -/
theorem round_viable (C D C' D' : ℝ) (γ ρ k ξ η_p η_s : ℝ)
    (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ (η_p * η_s) ξ)
    (hrhogk : γ * k ≤ ρ) (hcone : k * C ≤ D)
    (hthresh : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ (η_p * η_s) * devEnergy dev)
    (hcompat : 0 < devEnergy dev) :
    k * C' ≤ D' :=
  gainop_cone_step C D C' D' γ ρ k ξ (η_p * η_s) dev hstep hop
    hrhogk hcone hthresh

/-- Из `GainOp D D' dev ρ η ξ` и `devEnergy dev = 0` следует
`ρ·D − ξ ≤ D'` и `η·devEnergy dev = 0`. -/
theorem cycle_criterion (D D' : ℝ) (ρ η ξ : ℝ) (dev : Fin N → V)
    (hop : GainOp D D' dev ρ η ξ) :
    devEnergy dev = 0 → ρ * D - ξ ≤ D' ∧ η * devEnergy dev = 0 :=
  fun hzero => round_exhausted D D' ρ η ξ dev hzero hop


end Hagi

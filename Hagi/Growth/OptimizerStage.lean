/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainDecomposition

/-!
# OptimizerStage — оптимизатор как отдельная стадия конверсии

Цепочка
`E_dev →η_p→ G_policy →η_o→ G_update →η_s→ G_cap`.

* `etaOpt`: `etaOpt D_grad D_update = D_update / D_grad`;
* `gain_chain_opt`: если `G_policy = η_p·E_dev`,
  `G_update = η_o·G_policy`, `G_cap = η_s·G_update`, то
  `G_cap = (η_p·η_o·η_s)·E_dev`;
* `any_stage_kills_gain`: при `0 ≤ E_dev` и тех же посылках,
  если одна из η ≤ 0 при неотрицательных остальных, то
  `G_cap ≤ 0`.
-/

namespace Hagi

/-- Отношение конверсии оптимизатора:
`etaOpt D_grad D_update = D_update / D_grad`. -/
noncomputable def etaOpt (D_grad D_update : ℝ) : ℝ :=
  D_update / D_grad

/-- Если `G_policy = η_p·E_dev`, `G_update = η_o·G_policy` и
`G_cap = η_s·G_update`, то `G_cap = (η_p·η_o·η_s)·E_dev`. -/
theorem gain_chain_opt (E_dev G_policy G_update G_cap
    η_p η_o η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_update = η_o * G_policy)
    (h3 : G_cap = η_s * G_update) :
    G_cap = (η_p * η_o * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2] at h3
  rw [h3]
  ring

/-- Если `0 ≤ E_dev`, выполняются посылки `gain_chain_opt` и
одна из `η_p`, `η_o`, `η_s` ≤ 0 при неотрицательных
остальных, то `G_cap ≤ 0`. -/
theorem any_stage_kills_gain (E_dev G_policy G_update G_cap
    η_p η_o η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_update = η_o * G_policy)
    (h3 : G_cap = η_s * G_update)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_o ∧ 0 ≤ η_s)
      ∨ (0 ≤ η_p ∧ η_o ≤ 0 ∧ 0 ≤ η_s)
      ∨ (0 ≤ η_p ∧ 0 ≤ η_o ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_o * η_s) * E_dev :=
    gain_chain_opt E_dev G_policy G_update G_cap η_p η_o η_s
      h1 h2 h3
  rcases hzero with ⟨hp, ho, hs⟩ | ⟨hp, ho, hs⟩ | ⟨hp, ho, hs⟩
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg ho hs]
    nlinarith [hchain, hE, hprod]
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg hp hs]
    nlinarith [hchain, hE, hprod]
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg hp ho]
    nlinarith [hchain, hE, hprod]

end Hagi

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.MergeCancellation
import Hagi.Growth.RatioTakeoff
import Hagi.Growth.StateBinding
set_option linter.style.header false

/-!
# GainOperator — оператор превращения disagreement в прирост

Модель цикла: dev-энергия `devEnergy dev = ∑‡dev_k‡²`; оператор
с эффективностью η (`GainOp`: `D' ≥ ρ·D + η·E_dev − ξ`);
производство `C' = C + γ·D`.

* `gainop_cone_step`: при точном шаге, `GainOp`, `ρ ≥ γk`,
  конусе `kC ≤ D` и пороге
  `γk²·C + (1−ρ)k·C + ξ ≤ η·E_dev` следует `kC' ≤ D'`;
* `gainop_pairwise_bridge`: тот же вывод с порогом в попарной
  форме `η·(∑_{i,j}‡W_i − W_j‡²)/(2N)` (тождество
  `pairwise_variance_identity`);
* `gainop_ignition`: если условия выполнены на каждом цикле и
  старт в конусе, то `ConeRatio` инвариантен и
  `C₀·(1+γk)^T ≤ C_T` (композиция с `ratio_takeoff`).

Существование оператора с `η > 0` на реальном runtime — посылка
(в модуле он не строится); метрика η здесь безразмерно смешивает
энергии весов и наты.
-/

open Finset InnerProductSpace

namespace Hagi.Growth

variable {N : ℕ} [NeZero N] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Энергия dev-канала: `devEnergy dev = Σ_k ‖dev k‖^2`. -/
def devEnergy (dev : Fin N → V) : ℝ := ∑ k, ‖dev k‖ ^ 2

/-- `GainOp D D' dev ρ η ξ` означает
`ρ·D + η·devEnergy dev − ξ ≤ D'`. -/
def GainOp (D D' : ℝ) (dev : Fin N → V) (ρ η ξ : ℝ) : Prop :=
  ρ * D + η * devEnergy dev - ξ ≤ D'

/-- Если `C' = C + γ·D`, `GainOp D D' dev ρ η ξ`, `γ·k ≤ ρ`,
`k·C ≤ D` и `γ·k²·C + (1−ρ)·k·C + ξ ≤ η·devEnergy dev`,
то `k·C' ≤ D'`. -/
theorem gainop_cone_step (C D C' D' : ℝ) (γ ρ k ξ η : ℝ)
    (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone : k * C ≤ D)
    (hsuff : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev) :
    k * C' ≤ D' := by
  have hD : ρ * D + η * devEnergy dev - ξ ≤ D' := hop
  -- ключевая алгебра: D' − kC' ≥ (ρ−γk)(D−kC) ≥ 0
  have hkey : ρ * D + η * devEnergy dev - ξ - k * (C + γ * D)
      = (ρ - γ * k) * (D - k * C)
        + (η * devEnergy dev - (γ * k ^ 2 * C
          + (1 - ρ) * k * C + ξ)) := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D - k * C) := by
    have hsub : (0:ℝ) ≤ D - k * C := by linarith [hcone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ) ≤ η * devEnergy dev
      - (γ * k ^ 2 * C + (1 - ρ) * k * C + ξ) :=
    sub_nonneg.mpr hsuff
  have h3 : D' - k * C'
      ≥ (ρ - γ * k) * (D - k * C)
        + (η * devEnergy dev - (γ * k ^ 2 * C
          + (1 - ρ) * k * C + ξ)) := by
    rw [hstep]
    have hkey' : ρ * D + η * devEnergy dev - ξ - k * (C + γ * D)
        = (ρ - γ * k) * (D - k * C)
          + (η * devEnergy dev - (γ * k ^ 2 * C
            + (1 - ρ) * k * C + ξ)) := by
      field_simp
      ring
    linarith [hkey', hD]
  linarith

/-- Тот же вывод, что `gainop_cone_step`, с порогом в
попарной форме: если `mergeDecomp W M dev` и
`γ·k²·C + (1−ρ)·k·C + ξ
≤ η·((Σ_i Σ_j ‖W i − W j‖^2)/(2N))`, то `k·C' ≤ D'`. -/
theorem gainop_pairwise_bridge (C D C' D' : ℝ) (γ ρ k ξ η : ℝ)
    (W : Fin N → V) (M : V) (dev : Fin N → V)
    (hd : mergeDecomp W M dev)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone : k * C ≤ D)
    (hpair : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * ((∑ i, ∑ j, ‖W i - W j‖ ^ 2) / (2 * (N : ℝ)))) :
    k * C' ≤ D' := by
  have hiden : ∑ i, ∑ j, ‖W i - W j‖ ^ 2
      = (2 * (N : ℝ)) * devEnergy dev :=
    pairwise_variance_identity W M dev hd
  have hsuff : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev := by
    rw [hiden] at hpair
    have hz : (2:ℝ) * (N:ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < 2 * (N:ℝ) :=
        mul_pos (by norm_num) (Nat.cast_pos.mpr
          (Nat.pos_of_ne_zero (NeZero.ne N)))
      exact ne_of_gt hpos
    have hsimp : ((2:ℝ) * (N:ℝ)) * devEnergy dev
        / ((2:ℝ) * (N:ℝ)) = devEnergy dev :=
      by
        rw [mul_comm ((2:ℝ) * (N:ℝ)) (devEnergy dev)]
        exact mul_div_cancel_right₀ (devEnergy dev) hz
    rw [hsimp] at hpair
    exact hpair
  exact gainop_cone_step C D C' D' γ ρ k ξ η dev hstep hop
    hrhogk hcone hsuff

/-! ### Инвариант и takeoff от оператора -/

/-- Если на каждом цикле выполнены точный шаг, `GainOp`,
`ρ ≥ γk`, порог из `gainop_cone_step` и старт в конусе,
то `ConeRatio` инвариантен и
`(S 0).capability * (1 + γ·k) ^ T ≤ (S T).capability`. -/
theorem gainop_ignition {Xs : Type*}
    [NormedAddCommGroup Xs] [InnerProductSpace ℝ Xs]
    (S : ℕ → GrowthState Xs)
    (dev : ℕ → Fin N → V) (γ ρ k ξ η : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hstep : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (hop : ∀ t, GainOp (usableFrontier (S t))
      (usableFrontier (S (t + 1))) (dev t) ρ η ξ)
    (hrhogk : γ * k ≤ ρ)
    (hcone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (hsuff : ∀ t, γ * k ^ 2 * (S t).capability
      + (1 - ρ) * k * (S t).capability + ξ
      ≤ η * devEnergy (dev t))
    (T : ℕ) :
    ConeRatio (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) k
    ∧ (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability := by
  have hcone : ConeRatio (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) k := by
    intro t
    induction t with
    | zero => exact hcone0
    | succ t ih =>
        exact gainop_cone_step (S t).capability
          (usableFrontier (S t)) (S (t + 1)).capability
          (usableFrontier (S (t + 1))) γ ρ k ξ η (dev t)
          (hstep t) (hop t) hrhogk ih (hsuff t)
  exact ⟨hcone, ratio_takeoff (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k hγ hk hstep hcone T⟩

end Hagi.Growth

namespace Hagi
export Hagi.Growth (devEnergy GainOp gainop_cone_step gainop_pairwise_bridge gainop_ignition)
end Hagi



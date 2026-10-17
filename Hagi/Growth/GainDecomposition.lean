/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.MergeCancellation
import Hagi.Growth.RatioTakeoff
import Hagi.Growth.StateBinding
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

/-!
# GainDecomposition — разложение GainOp на измеримые стадии

Разложение конверсии disagreement → capability на две стадии:
`η_policy = G_policy / E_dev`, `η_state = G_cap / G_policy`.

* `gain_chain`: если `G_policy = η_p * E_dev` и
  `G_cap = η_s * G_policy`, то `G_cap = (η_p * η_s) * E_dev`;
* `zero_stage_kills_gain`: при `0 ≤ E_dev` и тех же посылках,
  если одна из `η_p`, `η_s` ≤ 0, а другая ≥ 0, то `G_cap ≤ 0`;
  произведения `η_p * η_s`: если он ≤ `(η_p * η_s) * devEnergy dev`,
  то он ≤ `η * devEnergy dev` для `η = η_p * η_s`.
-/

namespace Hagi.Growth

open Finset

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V]

/-- Стадия 1: `etaPolicy E_dev G_policy = G_policy / E_dev`. -/
noncomputable def etaPolicy (E_dev G_policy : ℝ) : ℝ :=
  G_policy / E_dev

/-- Стадия 2: `etaState G_policy G_cap = G_cap / G_policy`. -/
noncomputable def etaState (G_policy G_cap : ℝ) : ℝ :=
  G_cap / G_policy

/-- Если `G_policy = η_p * E_dev` и `G_cap = η_s * G_policy`,
то `G_cap = (η_p * η_s) * E_dev`. -/
theorem gain_chain (E_dev G_policy G_cap η_p η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_cap = η_s * G_policy) :
    G_cap = (η_p * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2]
  ring

/-- Если `0 ≤ E_dev`, `G_policy = η_p * E_dev`,
`G_cap = η_s * G_policy` и одна из `η_p`, `η_s` ≤ 0 при
другой ≥ 0, то `G_cap ≤ 0`. -/
theorem zero_stage_kills_gain (E_dev G_policy G_cap η_p η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev) (h2 : G_cap = η_s * G_policy)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_s) ∨ (0 ≤ η_p ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_s) * E_dev :=
    gain_chain E_dev G_policy G_cap η_p η_s h1 h2
  rcases hzero with ⟨hp, hs⟩ | ⟨hp, hs⟩
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith

end Hagi.Growth


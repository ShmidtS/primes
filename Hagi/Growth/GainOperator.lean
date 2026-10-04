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
# R130: GainOperator — оператор превращения disagreement в прирост

FORMALIZATION_PLAN Phase A (R130), главный блокер: дефицит γ = 9×
(γ = 0.002 против требуемых 0.018). R129 показал: merge-усреднение
ТОЧНО, антикоррелированная компонента СОХРАНЕНА в dev-канале;
узкое место — оператор T превращения dev-энергии в прирост
frontier. Этот модуль — теорема-условие на T.

**Модель цикла** (все величины измеряемы):
- пул экспертов: `mergeDecomp W M dev` (R129), dev-энергия
  E_dev = Σ‖dev_k‖²;
- оператор T с эффективностью η: D_{t+1} ≥ ρ·D_t + η·E_dev − ξ
  (T превращает долю η dev-энергии в frontier; кандидаты из
  плана: distill-перенос dev, mixer.gain с certified-обучением);
- производство: C_{t+1} = C_t + γ·D_t.

**Теоремы:**

* `gainop_cone_step` — ДОСТАТОЧНОЕ ИЗМЕРЯЕМОЕ УСЛОВИЕ Зажигания:
  η·E_dev ≥ γk²·C + (1−ρ)k·C + ξ  и  ρ ≥ γk  ⟹  шаг конуса
  kC' ≤ D' (ξ-компенсация точная, алгебра R124/R126).
  Эффективная ставка γ_eff = η·E_dev/C — заменяет свободный
  гиперпараметр β сертифицированным измерением.
* `gainop_pairwise_bridge` — то же в терминах ИЗМЕРЯЕМОГО
  попарного рассеяния (R129: Σ_{i,j}‖W_i−W_j‖² = 2N·E_dev):
  порог в pairwise-форме — прямой сигнал GapLaw/twoGap.
* `gainop_ignition` — если операторное условие держится на
  каждом цикле и старт в конусе — ConeRatio инвариантен и
  C_T ≥ C₀(1+γk)^T (composition с `ratio_takeoff` R124):
  γ-дефицит закрыт конструкцией T, а не гиперпараметром.

**Cunningham-форма** (2609.15802, план §1): операторное условие
есть произведение эластичностей петли: ε_T·ε_γ ≥ порога, где
ε_T = η·E_dev/C (эластичность frontier по disagreement) и
ε_γ = γk (эластичность capability по frontier); зажигание ⟺
произведение превышает порог затухания γk²+(1−ρ)k+ξ/C —
самоподдержка по Cunningham как частный случай R124.

**Честные границы:** существование оператора T с η > 0 на
реальном runtime — measured premise (R104: mixer.gain → 0 —
оператор сам выключает канал); дистилляция dev — кандидат с
теоретической поддержкой (teacher_generated_identity R109:
ре-микс не добавляет информации, перенос — да).
-/

open Finset InnerProductSpace

namespace Hagi

variable {N : ℕ} [NeZero N] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Энергия dev-канала: E_dev = Σ_k ‖dev_k‖². -/
def devEnergy (dev : Fin N → V) : ℝ := ∑ k, ‖dev k‖ ^ 2

/-- **Оператор gain**: превращает долю η dev-энергии в
frontier: D' ≥ ρD + η·E_dev − ξ (measured premise —
эффективность оператора T на цикле). -/
def GainOp (D D' : ℝ) (dev : Fin N → V) (ρ η ξ : ℝ) : Prop :=
  ρ * D + η * devEnergy dev - ξ ≤ D'

/-- **Шаг конуса от оператора**: если оператор превращает
dev-энергию в frontier с эффективностью η и выполняется
ИЗМЕРЯЕМОЕ пороговое условие

  η·E_dev ≥ γk²·C + (1−ρ)k·C + ξ

(эквивалентно γ_eff = η·E_dev/C ≥ γk² + (1−ρ)k + ξ/C), и
ρ ≥ γk, то шаг конуса k·C' ≤ D' выполняется: ξ-компенсация
точная. Замыкает γ-дефицит измерением вместо гиперпараметра. -/
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
  -- та же ключевая алгебра R124: D' − kC' ≥ (ρ−γk)(D−kC) ≥ 0
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

/-- **Мост к измеримому рассеянию**: то же пороговое условие
в терминах попарного рассеяния пула

  P = Σ_{i,j}‖W_i − W_j‖² = 2N·E_dev (R129),

напрямую измеряемого на тензорах (GapLaw/twoGap-сигнал):
η·P/(2N) ≥ γk²·C + (1−ρ)k·C + ξ. -/
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

/-- **Зажигание от оператора gain**: если на КАЖДОМ цикле
пул имеет merge-разложение, оператор T с эффективностью η
превращает dev-энергию в frontier (пороговое условие
выполнено) и ρ ≥ γk, то конус D ≥ kC инвариантен и
C_T ≥ C₀(1+γk)^T — γ-дефицит (9×) закрыт КОНСТРУКЦИЕЙ
оператора, а не гиперпараметром: γ_eff = η·E_dev/C
сертифицированно превышает порог затухания. -/
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

end Hagi



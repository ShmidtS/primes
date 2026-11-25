/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/


import Hagi.Theory.MuonDescentW1Rect
import Hagi.Theory.FirstLayerLipBatch

/-!
# MomentumAlign — шаг вдоль произвольного направления, момент `m1`, Muon с моментом

C686. Код (hagi/core.py:1754–1755 @ca52eb4) в `HybridMuon` ведёт EMA-буфер
`m1 = 0.85·m1 + 0.15·gW1` и применяет Newton–Schulz к `m1`, а не к `G`:
`W1 -= (cos_lr·0.7)·newton_schulz_orthogonalize(m1, iters=3)`.
Nesterov-поправки нет, поправки смещения нет (`μ = 0.85`, `1−μ = 0.15`).

* **T1 — направление** (любое `E` со скалярным произведением):
  `dir_drop_of_step` — шаг `z + γ•d` даёт `f (z + γ•d) ≤ f z − (γ·a − Lγ²‖d‖²/2)`,
  `a = −⟪grad z, d⟫`; `dir_drop_le_optimal` — для любого `γ` drop не больше
  `a²/(2L‖d‖²)` (полный квадрат; `nlDrop` — частный случай `d ∝ grad`,
  `dir_drop_is_nlDrop`); `dir_drop_optimal` — `γ* = a/(L‖d‖²)`, drop `a²/(2L‖d‖²)`.
  Для слоя: `w1BatchCE_dir_drop_of_step`, `w1BatchCE_dir_optimal_step_drop`.
* **T2 — момент** `mom μ mPrev G = μ•mPrev + (1−μ)•G`: `momentum_align` —
  `⟪G,m⟫ = (1−μ)‖G‖² + μ⟪G,m_prev⟫`; `momentum_align_cs` — всегда
  `⟪G,m⟫ ≥ (1−μ)‖G‖² − μ‖G‖‖m_prev‖`; `momentum_align_ge` — при
  `0 ≤ ⟪G,m_prev⟫` выравнивание `≥ (1−μ)‖G‖²`; `momentum_align_ge_grad` —
  при `‖G‖² ≤ ⟪G,m_prev⟫` выравнивание `≥ ‖G‖²`; `momentum_residual` —
  `G − m = μ•(G − m_prev)`; `momentum_dir_drop` — шаг вдоль `m`;
  `momentum_dir_drop_le_gd` — certified drop вдоль `m` не превосходит
  `‖G‖²/(2L)` (Коши–Шварц).
* **T3 — Muon с моментом** (носитель слоя `ι → δ → ℝ`, `momStep m k = ns_k m̂`
  — шаг кода, `momStep_apply`): `wfrob_cauchy`, `wfrob_abs_cauchy`,
  `wfrob_triangle`, `momStep_norm_ge_one`; `muon_momentum_bound` —
  `‖m‖_F − ‖G−m‖_F·‖X‖_F ≤ ⟨G, X⟩`; `muon_momentum_third` —
  если `‖G−m‖_F·‖X‖_F ≤ ‖m‖_F/2`, то `‖G‖_F/3 ≤ ⟨G, X⟩`;
  `wfdot_mom_align` — матричная форма `momentum_align`.

Честная граница: `a ≥ (1−μ)‖G‖²` ВСЕГДА неверно (без условия на
`⟪G,m_prev⟫` верна только оценка с Коши–Шварцем) — поэтому «всегда»-форма
здесь с минусом `μ‖G‖‖m_prev‖`; `‖G‖/2`-следствие T3 неверно, доказано
`‖G‖/3`; знак `⟪G−m, X⟫` неизвестен ⇒ остаток — произведение норм; kink,
`cos_lr·0.7` и связь `η` с `γ*` вне утверждения.
-/


set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.MomentumAlign

open scoped BigOperators InnerProductSpace
open Hagi.Theory.NegativeTransfer
open Hagi.Theory.FirstLayerGrad
open Hagi.Theory.FirstLayerLip
open Hagi.Theory.FirstLayerLipBatch
open Hagi.Theory.FunctionPreservingGrowth
open Hagi.Theory.MuonWide
open Hagi.Theory.WideSVD

/-! ### T1: оптимальный шаг вдоль произвольного направления -/

section Dir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`dir_drop_of_step`** (T1): `L`-smooth (`hsm`) ⇒ шаг `z + γ•d` по
ЛЮБОМУ направлению `d` даёт `f (z + γ•d) ≤ f z − (γ·a − L·γ²·‖d‖²/2)`,
`a = −⟪grad z, d⟫` (выравнивание с антиградиентом; `a > 0` ⇔ `d` —
направление спуска). При `d = −grad z` это `nl_drop_bound` (`a = ‖g‖²`). -/

theorem dir_drop_of_step (f : E → ℝ) (grad : E → E) (L γ : ℝ) (z d : E)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2) :
    f (z + γ • d) ≤ f z - (-γ * ⟪grad z, d⟫_ℝ - L * γ ^ 2 * ‖d‖ ^ 2 / 2) := by
  have h := hsm z (z + γ • d)
  have hin : ⟪grad z, z + γ • d - z⟫_ℝ = γ * ⟪grad z, d⟫_ℝ := by
    rw [show z + γ • d - z = γ • d by module, real_inner_smul_right]
  have hnorm : ‖z + γ • d - z‖ ^ 2 = γ ^ 2 * ‖d‖ ^ 2 := by
    rw [show z + γ • d - z = γ • d by module, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hin, hnorm] at h
  rw [show L / 2 * (γ ^ 2 * ‖d‖ ^ 2) = L * γ ^ 2 * ‖d‖ ^ 2 / 2 from by ring] at h
  linarith

/-- **`dir_drop_le_optimal`**: для любого `γ` гарантированный drop вдоль `d`
не превосходит `a²/(2L‖d‖²)` — полный квадрат
`a²/(2L‖d‖²) − (γa − Lγ²‖d‖²/2) = (L/2)·(γ‖d‖ − a/(L‖d‖))²`.
Частный случай `nl_drop_optimal`: при `d = −c•grad z` (`a = c‖g‖²`,
`‖d‖² = c²‖g‖²`) drop `= nlDrop (cγ) L ‖g‖` (`dir_drop_is_nlDrop`). -/

theorem dir_drop_le_optimal (L γ a D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    γ * a - L * γ ^ 2 * D ^ 2 / 2 ≤ a ^ 2 / (2 * L * D ^ 2) := by
  have hs : (L / 2) * (γ * D - a / (L * D)) ^ 2
      = a ^ 2 / (2 * L * D ^ 2) - (γ * a - L * γ ^ 2 * D ^ 2 / 2) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (L / 2) * (γ * D - a / (L * D)) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- **`dir_drop_is_nlDrop`**: при `d = c•grad z` (`g = grad z`) drop вдоль `d`
— это `nlDrop (cγ) L ‖g‖`: `nlDrop` — частный случай направления,
пропорционального градиенту. -/

theorem dir_drop_is_nlDrop (L γ c g : ℝ) :
    γ * (c * g ^ 2) - L * γ ^ 2 * (c ^ 2 * g ^ 2) / 2 = nlDrop (c * γ) L g := by
  unfold nlDrop
  ring

/-- **`dir_drop_optimal`** (T1, MAIN): `d ≠ 0`, `⟪grad z, d⟫ < 0` ⇒
оптимальный шаг вдоль `d` — `γ* = a/(L‖d‖²)`, и он даёт drop
`a²/(2L‖d‖²)`, `a = ⟪grad z, d⟫`. -/

theorem dir_drop_optimal (f : E → ℝ) (grad : E → E) (L : ℝ) (z d : E)
    (hL : 0 < L) (hd : d ≠ 0)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2) :
    f (z + (-⟪grad z, d⟫_ℝ / (L * ‖d‖ ^ 2)) • d)
      ≤ f z - ⟪grad z, d⟫_ℝ ^ 2 / (2 * L * ‖d‖ ^ 2) := by
  have h := dir_drop_of_step f grad L (-⟪grad z, d⟫_ℝ / (L * ‖d‖ ^ 2)) z d hsm
  have hid : -(-⟪grad z, d⟫_ℝ / (L * ‖d‖ ^ 2)) * ⟪grad z, d⟫_ℝ
      - L * (-⟪grad z, d⟫_ℝ / (L * ‖d‖ ^ 2)) ^ 2 * ‖d‖ ^ 2 / 2
      = ⟪grad z, d⟫_ℝ ^ 2 / (2 * L * ‖d‖ ^ 2) := by
    field_simp
    ring
  rw [hid] at h
  exact h

end Dir

/-! ### T2: момент кода `m = μ•m_prev + (1−μ)•G` -/

section Momentum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- EMA-буфер кода (core.py:1754 @ca52eb4): `m1 = μ·m1 + (1−μ)·gW1`,
`μ = 0.85` (без nesterov, без поправки смещения). -/
noncomputable def mom (μ : ℝ) (mPrev G : E) : E := μ • mPrev + (1 - μ) • G

/-- **`momentum_align`** (T2): точное выравнивание момента с градиентом:
`⟪G,m⟫ = (1−μ)‖G‖² + μ⟪G,m_prev⟫`. -/
theorem momentum_align (G mPrev : E) (μ : ℝ) :
    ⟪G, mom μ mPrev G⟫_ℝ = (1 - μ) * ‖G‖ ^ 2 + μ * ⟪G, mPrev⟫_ℝ := by
  rw [mom, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- **`momentum_align_cs`**: ВСЕГДА (любые `μ`, `m_prev`, `G`)
`(1−μ)‖G‖² − |μ|·‖G‖·‖m_prev‖ ≤ ⟪G,m⟫` — Коши–Шварц на `⟪G,m_prev⟫`.
Безусловное `⟪G,m⟫ ≥ (1−μ)‖G‖²` неверно (контрпример — в witness). -/
theorem momentum_align_cs (G mPrev : E) (μ : ℝ) :
    (1 - μ) * ‖G‖ ^ 2 - |μ| * ‖G‖ * ‖mPrev‖ ≤ ⟪G, mom μ mPrev G⟫_ℝ := by
  rw [momentum_align]
  have hab := abs_le.1 (abs_real_inner_le_norm G mPrev)
  have hlo : -(‖G‖ * ‖mPrev‖) ≤ ⟪G, mPrev⟫_ℝ := hab.1
  have hhi : ⟪G, mPrev⟫_ℝ ≤ ‖G‖ * ‖mPrev‖ := hab.2
  have hX : (0 : ℝ) ≤ ‖G‖ * ‖mPrev‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  by_cases hμ : 0 ≤ μ
  · rw [abs_of_nonneg hμ]
    have h1 : μ * (-(‖G‖ * ‖mPrev‖)) ≤ μ * ⟪G, mPrev⟫_ℝ :=
      mul_le_mul_of_nonneg_left hlo hμ
    linarith
  · have hμn : μ < 0 := lt_of_not_ge hμ
    rw [abs_of_neg hμn]
    have h1 := mul_le_mul_of_nonpos_left hhi hμn.le
    have e : - -μ * ‖G‖ * ‖mPrev‖ = μ * (‖G‖ * ‖mPrev‖) := by ring
    linarith

/-- **`momentum_align_ge`**: `0 ≤ μ ≤ 1` и согласованный с градиентом прошлый
момент (`0 ≤ ⟪G,m_prev⟫`) ⇒ `⟪G,m⟫ ≥ (1−μ)‖G‖²`. -/
theorem momentum_align_ge (G mPrev : E) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hagr : 0 ≤ ⟪G, mPrev⟫_ℝ) :
    (1 - μ) * ‖G‖ ^ 2 ≤ ⟪G, mom μ mPrev G⟫_ℝ := by
  rw [momentum_align]
  exact le_add_of_nonneg_right (mul_nonneg hμ0 hagr)

/-- **`momentum_align_ge_grad`**: `0 ≤ μ ≤ 1` и `‖G‖² ≤ ⟪G,m_prev⟫` ⇒
`‖G‖² ≤ ⟪G,m⟫`: момент не хуже градиента по first-order drop. Порог —
`‖G‖²`, а не `0`: при `G = (2,0)`, `m_prev = (1,0)`, `μ = 0.9`
`⟪G,m⟫ = 3.8 < 4`. -/
theorem momentum_align_ge_grad (G mPrev : E) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hagr : ‖G‖ ^ 2 ≤ ⟪G, mPrev⟫_ℝ) :
    ‖G‖ ^ 2 ≤ ⟪G, mom μ mPrev G⟫_ℝ := by
  rw [momentum_align]
  have h : μ * ‖G‖ ^ 2 ≤ μ * ⟪G, mPrev⟫_ℝ := mul_le_mul_of_nonneg_left hagr hμ0
  nlinarith

/-- **`momentum_residual`**: невязка момента `G − m = μ•(G − m_prev)`. -/
theorem momentum_residual (G mPrev : E) (μ : ℝ) :
    G - mom μ mPrev G = μ • (G - mPrev) := by
  rw [mom]
  module


/-- **`momentum_dir_drop`**: цель с дифференциалом `⟪G,·⟫`, шаг вдоль момента
`m` (`m ≠ 0`, `⟪G,m⟫ < 0` — момент направлен против градиента): `γ* = −⟪G,m⟫/(L‖m‖²)`,
drop `⟪G,m⟫²/(2L‖m‖²)`. -/
theorem momentum_dir_drop (f : E → ℝ) (G m z : E) (L : ℝ) (hL : 0 < L)
    (hm : m ≠ 0)
    (hsm : ∀ x y : E, f y ≤ f x + ⟪G, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2) :
    f (z + (-⟪G, m⟫_ℝ / (L * ‖m‖ ^ 2)) • m)
      ≤ f z - ⟪G, m⟫_ℝ ^ 2 / (2 * L * ‖m‖ ^ 2) :=
  dir_drop_optimal f (fun _ => G) L z m hL hm hsm

/-- **`momentum_dir_drop_le_gd`**: certified drop вдоль момента не превосходит
`‖G‖²/(2L)` — drop оптимального градиентного шага (Коши–Шварц:
`⟪G,m⟫² ≤ ‖G‖²‖m‖²`). По гарантированной оценке первого порядка момент не
даёт выигрыша над оптимальным GD-шагом. -/
theorem momentum_dir_drop_le_gd (G m : E) (L : ℝ) (hL : 0 < L) (hm : m ≠ 0) :
    ⟪G, m⟫_ℝ ^ 2 / (2 * L * ‖m‖ ^ 2) ≤ ‖G‖ ^ 2 / (2 * L) := by
  have hab := abs_le.1 (abs_real_inner_le_norm G m)
  have hlo : -(‖G‖ * ‖m‖) ≤ ⟪G, m⟫_ℝ := hab.1
  have hhi : ⟪G, m⟫_ℝ ≤ ‖G‖ * ‖m‖ := hab.2
  have hsq' : ⟪G, m⟫_ℝ ^ 2 ≤ ‖G‖ ^ 2 * ‖m‖ ^ 2 := by
    nlinarith [sq_nonneg (‖G‖ * ‖m‖), mul_nonneg (norm_nonneg G) (norm_nonneg m)]
  have e : ‖G‖ ^ 2 * ‖m‖ ^ 2 / (2 * L * ‖m‖ ^ 2) = ‖G‖ ^ 2 / (2 * L) := by
    field_simp
  exact (div_le_div_of_nonneg_right hsq' (by positivity)).trans_eq e

end Momentum

/-! ### T1 для слоя: шаг `W1 + γ•d` по произвольному направлению -/

section DirLayer

variable {ι δ K τ : Type} [Fintype ι] [Fintype δ] [Fintype K] [Nonempty K] [DecidableEq K]
  [Fintype τ] [Nonempty τ]

/-- **`w1BatchCE_dir_drop_of_step`**: шаг `W1 + γ•d` по ЛЮБОМУ направлению `d`
внутри области активации каждого входа батча даёт drop не меньше
`γ·a − S_batch·γ²·‖d‖²/2`, `a = Σᵢⱼ D_batch i j·d i j` (`D_batch = −∇`). -/
theorem w1BatchCE_dir_drop_of_step (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 d : ι → δ → ℝ) (γ : ℝ)
    (hsame : ∀ t i, reluMask (w1Pre (x t) (fun i j => W1 i j + γ * d i j) i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x (fun i j => W1 i j + γ * d i j)
      ≤ w1BatchCE y b wo x W1
        - (γ * ∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j
          - S_batch wo x * (γ ^ 2 * parNorm d ^ 2) / 2) := by
  have h := w1BatchCE_descent_lemma y b wo x W1 (fun i j => W1 i j + γ * d i j) hsame
  have hexp : ∀ i j, parDiff W1 (fun i j => W1 i j + γ * d i j) i j = γ * d i j := by
    intro i j; unfold parDiff; ring
  have hquad : (∑ i, ∑ j, parDiff W1 (fun i j => W1 i j + γ * d i j) i j ^ 2)
      = γ ^ 2 * parNorm d ^ 2 := by
    simp only [hexp, parNorm_sq]
    exact sum_sq_smul γ d
  have hlin : (∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j
        * parDiff W1 (fun i j => W1 i j + γ * d i j) i j)
      = γ * ∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j := by
    simp only [hexp]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hquad, hlin] at h
  linarith

/-- **`w1BatchCE_dir_optimal_step_drop`** (T1 для слоя): `S_batch > 0`,
`d ≠ 0`, `0 < a` (направление согласовано с антиградиентом) ⇒ оптимальный шаг
вдоль `d`: `γ* = a/(S_batch‖d‖²)`, drop `a²/(2·S_batch·‖d‖²)`,
`a = Σᵢⱼ D_batch i j·d i j`. При `d = D_batch` — `w1BatchCE_optimal_step_drop`
(там `a = ‖D_batch‖²`). -/
theorem w1BatchCE_dir_optimal_step_drop (y : τ → K) (b : ι → ℝ) (wo : ι → K → ℝ)
    (x : τ → δ → ℝ) (W1 d : ι → δ → ℝ)
    (hS : 0 < S_batch wo x) (hd : d ≠ 0)
    (hsame : ∀ t i, reluMask (w1Pre (x t) (fun i j => W1 i j
        + ((∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j)
            / (S_batch wo x * parNorm d ^ 2)) * d i j) i + b i)
      = reluMask (w1Pre (x t) W1 i + b i)) :
    w1BatchCE y b wo x (fun i j => W1 i j
        + ((∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j)
            / (S_batch wo x * parNorm d ^ 2)) * d i j)
      ≤ w1BatchCE y b wo x W1
        - (∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j) ^ 2
          / (2 * S_batch wo x * parNorm d ^ 2) := by
  set a := ∑ i, ∑ j, w1BatchDescentDir y b wo x W1 i j * d i j with ha_def
  set D2 := parNorm d ^ 2 with hD_def
  have hD : 0 < D2 := by
    have hnn : (0 : ℝ) ≤ D2 := sq_nonneg _
    by_contra h0
    have h1 : D2 = 0 := le_antisymm (by linarith) hnn
    have hsum : (∑ i, ∑ j, d i j ^ 2) = 0 := by
      rw [← parNorm_sq, ← hD_def, h1]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hsum
    apply hd
    funext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
      (hz i (Finset.mem_univ i))
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hi j (Finset.mem_univ j))
  have h := w1BatchCE_dir_drop_of_step y b wo x W1 d (a / (S_batch wo x * D2))
    (by intro t i; exact hsame t i)
  have hid : a / (S_batch wo x * D2) * a
      - S_batch wo x * ((a / (S_batch wo x * D2)) ^ 2 * D2) / 2
      = a ^ 2 / (2 * S_batch wo x * D2) := by
    field_simp
    ring
  rw [hid] at h
  exact h

end DirLayer

/-! ### T3: Muon с моментом на носителе слоя `ι → δ → ℝ` -/

section MuonMomentum

open Hagi.Theory.MuonDescentW1Rect

variable {ι δ : Type} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]

omit [DecidableEq ι] [DecidableEq δ] in
/-- `parNorm` и `wfrobSq` — одна и та же Frobenius-норма. -/
theorem parNorm_eq_sqrt_wfrobSq (A : ι → δ → ℝ) : parNorm A = Real.sqrt (wfrobSq A) := rfl

omit [DecidableEq ι] [DecidableEq δ] in
omit [DecidableEq ι] [DecidableEq δ] in
omit [DecidableEq ι] [DecidableEq δ] in
/-- Аддитивность спаривания по первому аргументу. -/
theorem fdot_wide_add_left (A B X : Matrix ι δ ℝ) :
    fdot_wide (A + B) X = fdot_wide A X + fdot_wide B X := by
  simp only [fdot_wide, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] [DecidableEq δ] in
/-- `‖−A‖_F = ‖A‖_F`. -/
theorem wfrobSq_neg (A : Matrix ι δ ℝ) : wfrobSq (-A) = wfrobSq A := by
  simp only [wfrobSq, Matrix.neg_apply, neg_sq]

omit [DecidableEq ι] [DecidableEq δ] in
/-- Симметрия спаривания Фробениуса. -/
theorem fdot_wide_comm (A B : Matrix ι δ ℝ) : fdot_wide A B = fdot_wide B A := by
  simp only [fdot_wide, mul_comm]

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`fdot_wide_self`**: `⟨A,A⟩ = ‖A‖_F²`. -/
theorem fdot_wide_self (A : Matrix ι δ ℝ) : fdot_wide A A = wfrobSq A := by
  simp only [fdot_wide, wfrobSq]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq (A i j)).symm

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`wfrob_cauchy`**: Коши–Шварц для спаривания Фробениуса:
`⟨A,B⟩ ≤ ‖A‖_F·‖B‖_F`. -/
theorem wfrob_cauchy (A B : Matrix ι δ ℝ) :
    fdot_wide A B ≤ Real.sqrt (wfrobSq A) * Real.sqrt (wfrobSq B) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × δ))
    (fun q => A q.1 q.2) (fun q => B q.1 q.2)
  have e1 : (∑ q : ι × δ, A q.1 q.2 * B q.1 q.2) = fdot_wide A B := by
    rw [fdot_wide, Fintype.sum_prod_type]
  have e2 : (∑ q : ι × δ, A q.1 q.2 ^ 2) = wfrobSq A := by
    rw [wfrobSq, Fintype.sum_prod_type]
  have e3 : (∑ q : ι × δ, B q.1 q.2 ^ 2) = wfrobSq B := by
    rw [wfrobSq, Fintype.sum_prod_type]
  rw [e1, e2, e3] at h
  have hnn : (0 : ℝ) ≤ Real.sqrt (wfrobSq A) * Real.sqrt (wfrobSq B) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine le_of_sq_le_sq ?_ hnn
  rw [mul_pow, Real.sq_sqrt (wfrobSq_nonneg A), Real.sq_sqrt (wfrobSq_nonneg B)]
  exact h

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`wfrob_abs_cauchy`**: `|⟨A,B⟩| ≤ ‖A‖_F·‖B‖_F` — двусторонний Коши–Шварц. -/
theorem wfrob_abs_cauchy (A B : Matrix ι δ ℝ) :
    |fdot_wide A B| ≤ Real.sqrt (wfrobSq A) * Real.sqrt (wfrobSq B) := by
  have hneg : fdot_wide (-A) B = -fdot_wide A B := by
    simp only [fdot_wide, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hp := wfrob_cauchy A B
  have hn := wfrob_cauchy (-A) B
  rw [hneg, wfrobSq_neg] at hn
  exact abs_le.2 ⟨by linarith, hp⟩

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`wfrob_triangle`**: `‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F` (через Коши–Шварц). -/
theorem wfrob_triangle (A B : Matrix ι δ ℝ) :
    Real.sqrt (wfrobSq (A + B)) ≤ Real.sqrt (wfrobSq A) + Real.sqrt (wfrobSq B) := by
  have hexp : wfrobSq (A + B) = wfrobSq A + 2 * fdot_wide A B + wfrobSq B := by
    have e : ∀ i j, (A + B) i j ^ 2 = A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2 := by
      intro i j; simp only [Matrix.add_apply]; ring
    simp only [wfrobSq, fdot_wide, e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs := wfrob_cauchy A B
  have hle : wfrobSq (A + B) ≤ (Real.sqrt (wfrobSq A) + Real.sqrt (wfrobSq B)) ^ 2 := by
    rw [hexp, sq]
    nlinarith [Real.sq_sqrt (wfrobSq_nonneg A), Real.sq_sqrt (wfrobSq_nonneg B)]
  calc Real.sqrt (wfrobSq (A + B))
      ≤ Real.sqrt ((Real.sqrt (wfrobSq A) + Real.sqrt (wfrobSq B)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (wfrobSq A) + Real.sqrt (wfrobSq B) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Шаг кода для буфера `m` (core.py:1755: NS применяется к `m1`):
`X = ns_k m̂` на носителе слоя. -/
noncomputable def momStep (m : Matrix ι δ ℝ) (k : ℕ) : Matrix ι δ ℝ :=
  Hagi.Theory.MuonWide.wide_iter k (wnormed m)

theorem momStep_apply (m : Matrix ι δ ℝ) (k : ℕ) (i : ι) (j : δ) :
    momStep m k i j = w1StepR m k i j := rfl

/-- **`momStep_norm_ge_one`**: для `m ≠ 0` шаг кода `X = ns_k m̂` имеет
`‖X‖_F ≥ 1` (`⟨m̂,X⟩ ≥ 1` и Коши–Шварц). -/
theorem momStep_norm_ge_one {m : Matrix ι δ ℝ} (hm : m ≠ 0) (k : ℕ) :
    1 ≤ Real.sqrt (wfrobSq (momStep m k)) := by
  have hs : 0 < Real.sqrt (wfrobSq m) := Real.sqrt_pos.2 (wfrobSq_pos hm)
  have h1 : Real.sqrt (wfrobSq m) ≤ fdot_wide m (momStep m k) :=
    alignment_ge_gradient_any m hm k
  have h2 : fdot_wide (wnormed m) (momStep m k)
      = fdot_wide m (momStep m k) / Real.sqrt (wfrobSq m) := by
    rw [wnormed, fdot_wide_smul_left, one_div, div_eq_inv_mul]
  have h3 : 1 ≤ fdot_wide (wnormed m) (momStep m k) := by
    rw [h2]
    exact (le_div_iff₀ hs).2 (by rw [one_mul]; exact h1)
  have hn : wfrobSq (wnormed m) = 1 := by
    rw [wnormed, wfrobSq_smul, div_pow, one_pow, Real.sq_sqrt (wfrobSq_nonneg m)]
    exact div_mul_cancel₀ 1 (ne_of_gt (wfrobSq_pos hm))
  have hcs := wfrob_cauchy (wnormed m) (momStep m k)
  rw [hn] at hcs
  norm_num at hcs
  exact h3.trans hcs

/-- **`muon_momentum_bound`** (T3, MAIN): `m ≠ 0`, `X = ns_k m̂` — шаг кода
(core.py:1755 применяет NS к `m1`) ⇒
`‖m‖_F − ‖G−m‖_F·‖X‖_F ≤ ⟨G, X⟩`: выравнивание момента (C680/C682,
`alignment_ge_gradient_any`) минус Коши–Шварц на невязке `G − m`. -/
theorem muon_momentum_bound (G m : Matrix ι δ ℝ) (hm : m ≠ 0) (k : ℕ) :
    Real.sqrt (wfrobSq m)
        - Real.sqrt (wfrobSq (G - m)) * Real.sqrt (wfrobSq (momStep m k))
      ≤ fdot_wide G (momStep m k) := by
  have h1 : Real.sqrt (wfrobSq m) ≤ fdot_wide m (momStep m k) :=
    alignment_ge_gradient_any m hm k
  have hsplit : fdot_wide G (momStep m k)
      = fdot_wide m (momStep m k) + fdot_wide (G - m) (momStep m k) := by
    have h : fdot_wide (m + (G - m)) (momStep m k)
        = fdot_wide m (momStep m k) + fdot_wide (G - m) (momStep m k) :=
      fdot_wide_add_left m (G - m) (momStep m k)
    rw [show m + (G - m) = G by abel] at h
    exact h
  have hcs := wfrob_cauchy (G - m) (momStep m k)
  have hlo : -(Real.sqrt (wfrobSq (G - m)) * Real.sqrt (wfrobSq (momStep m k)))
      ≤ fdot_wide (G - m) (momStep m k) := (abs_le.1 (wfrob_abs_cauchy (G - m) (momStep m k))).1
  rw [hsplit]
  linarith

/-- **`muon_momentum_third`**: если момент близок к градиенту,
`‖G−m‖_F·‖X‖_F ≤ ‖m‖_F/2`, то `‖G‖_F/3 ≤ ⟨G, X⟩`: Muon с согласованным
моментом теряет не более трети first-order drop. (Половина невозможна:
`‖G‖ ≤ ‖m‖ + ‖G−m‖ ≤ (3/2)‖m‖`, так как `‖X‖_F ≥ 1`.) -/
theorem muon_momentum_third (G m : Matrix ι δ ℝ) (hm : m ≠ 0) (k : ℕ)
    (hclose : Real.sqrt (wfrobSq (G - m)) * Real.sqrt (wfrobSq (momStep m k))
      ≤ Real.sqrt (wfrobSq m) / 2) :
    Real.sqrt (wfrobSq G) / 3 ≤ fdot_wide G (momStep m k) := by
  have hb := muon_momentum_bound G m hm k
  have hX : (1 : ℝ) ≤ Real.sqrt (wfrobSq (momStep m k)) := momStep_norm_ge_one hm k
  have hbn : (0 : ℝ) ≤ Real.sqrt (wfrobSq (G - m)) := Real.sqrt_nonneg _
  have hmnn : (0 : ℝ) ≤ Real.sqrt (wfrobSq m) := Real.sqrt_nonneg _
  have hres : Real.sqrt (wfrobSq (G - m)) ≤ Real.sqrt (wfrobSq m) / 2 := by
    have h1 : Real.sqrt (wfrobSq (G - m)) * 1
        ≤ Real.sqrt (wfrobSq (G - m)) * Real.sqrt (wfrobSq (momStep m k)) :=
      mul_le_mul_of_nonneg_left hX hbn
    rw [mul_one] at h1
    exact le_trans h1 hclose
  have htri : Real.sqrt (wfrobSq G) ≤ Real.sqrt (wfrobSq m) + Real.sqrt (wfrobSq (G - m)) := by
    have h : Real.sqrt (wfrobSq (m + (G - m)))
        ≤ Real.sqrt (wfrobSq m) + Real.sqrt (wfrobSq (G - m)) :=
      wfrob_triangle m (G - m)
    rw [show m + (G - m) = G by abel] at h
    exact h
  have hres' : 2 * Real.sqrt (wfrobSq (G - m)) ≤ Real.sqrt (wfrobSq m) := by linarith
  have htri' : Real.sqrt (wfrobSq G) ≤ Real.sqrt (wfrobSq m) + Real.sqrt (wfrobSq (G - m)) := by
    have h : Real.sqrt (wfrobSq (m + (G - m)))
        ≤ Real.sqrt (wfrobSq m) + Real.sqrt (wfrobSq (G - m)) :=
      wfrob_triangle m (G - m)
    rw [show m + (G - m) = G by abel] at h
    exact h
  have hinner : Real.sqrt (wfrobSq m) - Real.sqrt (wfrobSq (G - m))
        * Real.sqrt (wfrobSq (momStep m k)) ≤ fdot_wide G (momStep m k) := hb
  have hprod : Real.sqrt (wfrobSq (G - m)) * Real.sqrt (wfrobSq (momStep m k))
      ≤ Real.sqrt (wfrobSq m) / 2 := hclose
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 3)).2
  have hX' : (1 : ℝ) ≤ Real.sqrt (wfrobSq (momStep m k)) := hX
  have hbn' : (0 : ℝ) ≤ Real.sqrt (wfrobSq (G - m)) := hbn
  nlinarith [hprod, hres', htri', hinner, hX', hbn']

omit [DecidableEq ι] [DecidableEq δ] in
/-- **`wfdot_mom_align`**: выравнивание момента на носителе слоя:
`⟨G, μ•m_prev + (1−μ)•G⟩ = (1−μ)‖G‖_F² + μ⟪G,m_prev⟫` (матричная форма
`momentum_align`). -/
theorem wfdot_mom_align (G mPrev : Matrix ι δ ℝ) (μ : ℝ) :
    fdot_wide G (μ • mPrev + (1 - μ) • G)
      = (1 - μ) * wfrobSq G + μ * fdot_wide G mPrev := by
  rw [fdot_wide_comm, fdot_wide_add_left, fdot_wide_smul_left, fdot_wide_smul_left,
    fdot_wide_comm mPrev G, fdot_wide_comm G G, fdot_wide_self]
  ring

end MuonMomentum

end Hagi.Theory.MomentumAlign

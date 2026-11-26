/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Training.AlternatingJoint
import Hagi.Theory.BlockLipschitz
import Hagi.Theory.ProvenTrunk

/-!
# JointTrunkHead — одновременный certified шаг trunk+head

: закрыть брешь AlternatingJoint —
там чередование (extractor заморожен внутри фазы, движется только
на admission-границах), а ОДНОВРЕМЕННЫЙ шаг по (θ_trunk, θ_head)
оставался под пином `crmsm_joint_separation`. Здесь
одновременный шаг m → m' = ⟨bs', headProj, θ'⟩ (меняются блоки
ствола И параметры головы за ОДИН переход) сертифицируется
additive-damage мажорантой:

  CE(t, lm m') ≤ CE(t, lm m) − 2A²/R² + 2·HL·d,

где − 2A²/R² — certified head-спад на СТАРЫХ features
(`ceOneHot_safeStep_le_residual`), а 2·HL·d —
trunk-канал: CE-lip 2‖·‖sup (`ce_head_lipschitz_in_logits`,
) + логит-смещение от смены ствола, доминируемое
headLip-нормой НОВОЙ головы HL и MEASURED trunk-смещением d.

## Honest limits

- **Cross-член поглощается, не исчезает.** Взаимодействие
  head-шага со сменой ствола не зануляется: вся разность
  |CE(F',θ') − CE(F,θ')| доминируется 2·HL·d (неравенство
  треугольника через CE на старых features). Цена честности:
  2·HL·d оплачивается КАЖДЫЙ joint-шаг (у alternating —
  damage-форма того же порядка раз в K шагов, см.
  `joint_vs_alternating_cycle`).
- **Параметрическая липшиц-константа ствола выводима только для
  атомов .** Для RMSNorm-gain: √n·Σ|Δg| (насыщение
  |rmsN| ≤ √n); для MLP-весов: n·Z·(F₁·FΔ₂ + F₂'·FΔ₁).
  Для ПРОИЗВОЛЬНОГО trunk вывода нет и здесь он не вводится
  (новый класс посылок = YAGNI): d остаётся measured binder
  (прецедент честности — D-binder non-circular: смещение
  ствола не выводится из lip ОДНОГО экстрактора).
- **Пин остаётся.** Joint-гарантия — conditional на
  measured d; одновременный majorizer БЕЗ d-члена не заявляется.
- **Trade-off теорема — арифметика.** `joint_vs_alternating_cycle`
  сравнивает ДВЕ данные гарантии; содержимое — явное условие
  превосходства, не новая механика.
- **Мост к certify-then-commit.** `joint_step_commit_strict`
  даёт drop > 0 — критерий приёма шага в интерфейсе
  `commit_drop_checked`; сам не правится.
- Trunk-«параметры» в ProvenTrunk — данные уровня модуля (g, W₁,
  W₂); константы derivable-but-not-tight (наследие атомов).

Layer decision: Training — модуль расширяет семейство
AlternatingJoint и потребляет Theory + Model.
-/

set_option relaxedAutoImplicit false

open scoped BigOperators NNReal

open Hagi.Model.LMCompose Hagi.Theory.BlockLipschitz Hagi.Theory.ProvenTrunk
open Hagi.Training.AlternatingJoint

namespace Hagi.Training.JointTrunkHead

/-! ## Section A: параметрическая чувствительность атомов -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Насыщение RMSNorm-атома: нормированный выход не превосходит
√n по модулю в каждой координате (ε-floor семантика; причина
выводимости UNCONDITIONAL-констант — та же, что и там). -/
theorem rmsN_coord_le (ε : ℝ) (hε : 0 < ε) (z : V → ℝ) (v : V) :
    |rmsN ε z v| ≤ Real.sqrt (Fintype.card V) := by
  have hn : (0:ℝ) < Real.sqrt (Fintype.card V) := by positivity
  have hs : (0:ℝ) ≤ Real.sqrt (∑ w, z w ^ 2) := Real.sqrt_nonneg _
  have hd : (0:ℝ) < rmsDen ε z := by
    have h2 : (0:ℝ) ≤ Real.sqrt (∑ w, z w ^ 2)
        / Real.sqrt (Fintype.card V) :=
      div_nonneg hs hn.le
    unfold rmsDen; linarith
  have hkey : Real.sqrt (Fintype.card V) * rmsDen ε z
      = Real.sqrt (∑ w, z w ^ 2) + Real.sqrt (Fintype.card V) * ε := by
    unfold rmsDen
    field_simp [hn.ne']
  have hz : |z v| ≤ Real.sqrt (∑ w, z w ^ 2) := coord_abs_le_l2 z v
  unfold rmsN
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc |z v| ≤ Real.sqrt (∑ w, z w ^ 2) := hz
    _ ≤ Real.sqrt (∑ w, z w ^ 2) + Real.sqrt (Fintype.card V) * ε := by
        have h2 : (0:ℝ) ≤ Real.sqrt (Fintype.card V) * ε := by positivity
        linarith
    _ = Real.sqrt (Fintype.card V) * rmsDen ε z := hkey.symm

/-- Параметрический lip RMSNorm-атома по gain: при фиксированном
входе z выход гейна меняется на √n·‖Δg‖₁ — насыщение
`rmsN_coord_le` + модуль произведения. -/
theorem rms_gain_param_disp (ε : ℝ) (hε : 0 < ε)
    (g g' : V → ℝ) (z : V → ℝ) :
    (∑ v, |g v * rmsN ε z v - g' v * rmsN ε z v|)
      ≤ Real.sqrt (Fintype.card V) * (∑ v, |g v - g' v|) := by
  have hterm : ∀ v : V,
      |g v * rmsN ε z v - g' v * rmsN ε z v|
      ≤ Real.sqrt (Fintype.card V) * |g v - g' v| := by
    intro v
    have hsplit : g v * rmsN ε z v - g' v * rmsN ε z v
        = (g v - g' v) * rmsN ε z v := by ring
    rw [hsplit, abs_mul]
    calc |g v - g' v| * |rmsN ε z v|
        ≤ |g v - g' v| * Real.sqrt (Fintype.card V) :=
          mul_le_mul_of_nonneg_left (rmsN_coord_le ε hε z v)
            (abs_nonneg _)
      _ = Real.sqrt (Fintype.card V) * |g v - g' v| := mul_comm _ _
  calc (∑ v, |g v * rmsN ε z v - g' v * rmsN ε z v|)
      ≤ ∑ v, Real.sqrt (Fintype.card V) * |g v - g' v| :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = Real.sqrt (Fintype.card V) * (∑ v, |g v - g' v|) :=
        (Finset.mul_sum _ _ _).symm

/-- ℓ1 ≤ √n·ℓ2 (Cauchy–Schwarz с единичным вектором; мост из
BlockLipschitz `hleg1`-механики, в функциональной форме). -/
theorem l1_le_sqrt_card_l2 {ι : Type} [Fintype ι] (r : ι → ℝ) :
    (∑ v, |r v|) ≤ Real.sqrt (Fintype.card ι)
      * Real.sqrt (∑ v, r v ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι => (1:ℝ)) (fun v => |r v|)
  simp only [one_mul, one_pow] at hcs
  have hcardsum : (∑ v : ι, (1:ℝ)) = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hcardsum] at hcs
  have habs2 : ∑ v, |r v| ^ 2 = ∑ v, r v ^ 2 :=
    Finset.sum_congr rfl fun v _ => by rw [sq_abs]
  rw [habs2] at hcs
  have hcard : (0:ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hS : (0:ℝ) ≤ ∑ v, r v ^ 2 :=
    Finset.sum_nonneg fun v _ => sq_nonneg _
  have hkey : (∑ v, |r v|) ^ 2
      ≤ (Real.sqrt (Fintype.card ι) * Real.sqrt (∑ v, r v ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard, Real.sq_sqrt hS]
    exact hcs
  have hsq := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (Finset.sum_nonneg fun v _ => abs_nonneg _),
    Real.sqrt_sq (by positivity)] at hsq

omit [Nonempty V] in
/-- |Σ a·b| ≤ ‖a‖₂·‖b‖₂ (C-S в abs-форме). -/
theorem abs_sum_mul_le (a b : V → ℝ) :
    |∑ k, a k * b k|
      ≤ Real.sqrt (∑ k, a k ^ 2) * Real.sqrt (∑ k, b k ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hA : (0:ℝ) ≤ ∑ k, a k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hB : (0:ℝ) ≤ ∑ k, b k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnn : (0:ℝ) ≤ (∑ k, a k ^ 2) * ∑ k, b k ^ 2 := mul_nonneg hA hB
  have hle : |∑ k, a k * b k|
      ≤ Real.sqrt ((∑ k, a k ^ 2) * ∑ k, b k ^ 2) :=
    abs_le_of_sq_le_sq
      (by rw [Real.sq_sqrt hnn]; exact hcs) (Real.sqrt_nonneg _)
  rwa [Real.sqrt_mul hA] at hle

/-- |relu a| ≤ |a| (relu — сжатие). -/
theorem abs_relu_le_abs (a : ℝ) : |relu a| ≤ |a| := by
  unfold relu
  by_cases h : 0 ≤ a
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_nonneg _]

/-- Параметрический lip MLP-атома по весам (W₁, W₂) при
фиксированном входе z: двухногое разложение через
relu-разность; leg A (ΔW₂): |relu(W₁j·z)| ≤ F₁·Z; leg B (ΔW₁):
Cauchy–Schwarz по j с ℓ1-колонками W₂'. Асимметрия честна:
старое W₁ оценивает leg A, НОВОЕ W₂' — leg B. -/
theorem mlp_param_lip (W₁ W₂ W₁' W₂' : V → V → ℝ) (z : V → ℝ) :
    (∑ v, |mlpApply W₁ W₂ z v - mlpApply W₁' W₂' z v|)
      ≤ (Fintype.card V : ℝ) * Real.sqrt (∑ k, z k ^ 2)
        * (Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
            * Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
          + Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2)
            * Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2)) := by
  classical
  set Z : ℝ := Real.sqrt (∑ k, z k ^ 2) with hZ
  set F1 : ℝ := Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2) with hF1
  set F2 : ℝ := Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2) with hF2
  set G2 : ℝ := Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2) with hG2
  set G1 : ℝ := Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2) with hG1
  have hZn : 0 ≤ Z := Real.sqrt_nonneg _
  have hF1n : 0 ≤ F1 := Real.sqrt_nonneg _
  have hF2n : 0 ≤ F2 := Real.sqrt_nonneg _
  have hG2n : 0 ≤ G2 := Real.sqrt_nonneg _
  have hG1n : 0 ≤ G1 := Real.sqrt_nonneg _
  have hpre : ∀ j : V,
      (∑ k, W₁ j k * z k) - (∑ k, W₁' j k * z k)
      = ∑ k, (W₁ j k - W₁' j k) * z k := by
    intro j
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlegA : ∀ j : V,
      |relu (∑ k, W₁ j k * z k)| ≤ F1 * Z := by
    intro j
    refine le_trans (abs_relu_le_abs _) ?_
    refine le_trans (abs_sum_mul_le (fun k => W₁ j k) z) ?_
    gcongr
    have hrow : (∑ k, W₁ j k ^ 2) ≤ ∑ j', ∑ k, W₁ j' k ^ 2 :=
      Finset.single_le_sum (f := fun j' => ∑ k, W₁ j' k ^ 2)
        (fun j' _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
        (Finset.mem_univ j)
    exact Real.sqrt_le_sqrt hrow
  have hlegB : ∀ j : V,
      |relu (∑ k, W₁ j k * z k) - relu (∑ k, W₁' j k * z k)|
      ≤ G1 * Z := by
    intro j
    refine le_trans (relu_lip_abs _ _) ?_
    rw [hpre j]
    refine le_trans (abs_sum_mul_le (fun k => W₁ j k - W₁' j k) z) ?_
    gcongr
    have hrow : (∑ k, (W₁ j k - W₁' j k) ^ 2)
        ≤ ∑ j', ∑ k, (W₁ j' k - W₁' j' k) ^ 2 :=
      Finset.single_le_sum (f := fun j' => ∑ k, (W₁ j' k - W₁' j' k) ^ 2)
        (fun j' _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
        (Finset.mem_univ j)
    exact Real.sqrt_le_sqrt hrow
  -- per-v pointwise: two-leg split
  have hpt : ∀ v : V,
      |mlpApply W₁ W₂ z v - mlpApply W₁' W₂' z v|
      ≤ (∑ j, |W₂ v j - W₂' v j|) * F1 * Z
        + (∑ j, |W₂' v j|) * (G1 * Z) := by
    intro v
    have hdiff : mlpApply W₁ W₂ z v - mlpApply W₁' W₂' z v
        = ∑ j, ((W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)
          + W₂' v j * (relu (∑ k, W₁ j k * z k)
            - relu (∑ k, W₁' j k * z k))) := by
      unfold mlpApply
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs
      (fun j => (W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)
        + W₂' v j * (relu (∑ k, W₁ j k * z k)
          - relu (∑ k, W₁' j k * z k))) Finset.univ) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => abs_add_le _ _) ?_
    have hleg1 : (∑ j, |(W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)|)
        ≤ (∑ j, |W₂ v j - W₂' v j|) * F1 * Z := by
      have hterm : ∀ j : V, |(W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)|
          ≤ |W₂ v j - W₂' v j| * F1 * Z := by
        intro j
        calc |(W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)|
            = |W₂ v j - W₂' v j| * |relu (∑ k, W₁ j k * z k)| := abs_mul _ _
          _ ≤ |W₂ v j - W₂' v j| * (F1 * Z) :=
              mul_le_mul_of_nonneg_left (hlegA j) (abs_nonneg _)
          _ = |W₂ v j - W₂' v j| * F1 * Z := by ring
      calc (∑ j, |(W₂ v j - W₂' v j) * relu (∑ k, W₁ j k * z k)|)
          ≤ ∑ j, |W₂ v j - W₂' v j| * F1 * Z :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = (∑ j, |W₂ v j - W₂' v j|) * F1 * Z := by
            simp only [Finset.sum_mul]
    have hleg2 : (∑ j, |W₂' v j * (relu (∑ k, W₁ j k * z k)
          - relu (∑ k, W₁' j k * z k))|)
        ≤ (∑ j, |W₂' v j|) * (G1 * Z) := by
      have hterm : ∀ j : V, |W₂' v j * (relu (∑ k, W₁ j k * z k)
            - relu (∑ k, W₁' j k * z k))|
          ≤ |W₂' v j| * (G1 * Z) := by
        intro j
        calc |W₂' v j * (relu (∑ k, W₁ j k * z k)
              - relu (∑ k, W₁' j k * z k))|
            = |W₂' v j| * |relu (∑ k, W₁ j k * z k)
                - relu (∑ k, W₁' j k * z k)| := abs_mul _ _
          _ ≤ |W₂' v j| * (G1 * Z) :=
              mul_le_mul_of_nonneg_left (hlegB j) (abs_nonneg _)
      calc (∑ j, |W₂' v j * (relu (∑ k, W₁ j k * z k)
            - relu (∑ k, W₁' j k * z k))|)
          ≤ ∑ j, |W₂' v j| * (G1 * Z) :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = (∑ j, |W₂' v j|) * (G1 * Z) := by
            simp only [Finset.sum_mul]
    rw [Finset.sum_add_distrib]
    exact add_le_add hleg1 hleg2
  -- assemble over v: product-type l1 bridge (n^2 entries, l1 <= n * F)
  have hcardn : (0:ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  have hprodA : (∑ v, ∑ j, |W₂ v j - W₂' v j|)
      ≤ (Fintype.card V : ℝ) * F2 := by
    have hconv : (∑ v, ∑ j, |W₂ v j - W₂' v j|)
        = ∑ p : V × V, |W₂ p.1 p.2 - W₂' p.1 p.2| := by
      rw [Fintype.sum_prod_type]
    have hconv2 : (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
        = ∑ p : V × V, (W₂ p.1 p.2 - W₂' p.1 p.2) ^ 2 := by
      rw [Fintype.sum_prod_type]
    have h1 := l1_le_sqrt_card_l2
      (fun p : V × V => |W₂ p.1 p.2 - W₂' p.1 p.2|)
    simp only [abs_abs, sq_abs] at h1
    rw [hconv]
    refine le_trans h1 ?_
    have hcardprod : (Fintype.card (V × V) : ℝ)
        = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
      rw [Fintype.card_prod]
      push_cast
      ring
    have hn : (0:ℝ) ≤ (Fintype.card V : ℝ)
        * (Fintype.card V : ℝ) := by positivity
    rw [hcardprod, Real.sqrt_mul_self hcardn, hF2, ← hconv2]
  have hprodB : (∑ v, ∑ j, |W₂' v j|)
      ≤ (Fintype.card V : ℝ) * G2 := by
    have hconv : (∑ v, ∑ j, |W₂' v j|)
        = ∑ p : V × V, |W₂' p.1 p.2| := by
      rw [Fintype.sum_prod_type]
    have hconv2 : (∑ v, ∑ j, W₂' v j ^ 2)
        = ∑ p : V × V, W₂' p.1 p.2 ^ 2 := by
      rw [Fintype.sum_prod_type]
    have h1 := l1_le_sqrt_card_l2
      (fun p : V × V => |W₂' p.1 p.2|)
    simp only [abs_abs, sq_abs] at h1
    rw [hconv]
    refine le_trans h1 ?_
    have hcardprod : (Fintype.card (V × V) : ℝ)
        = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
      rw [Fintype.card_prod]
      push_cast
      ring
    have hn : (0:ℝ) ≤ (Fintype.card V : ℝ)
        * (Fintype.card V : ℝ) := by positivity
    rw [hcardprod, Real.sqrt_mul_self hcardn, hG2, ← hconv2]
  -- factor the two legs out of the v-sum
  have e1 : (∑ v, (∑ j, |W₂ v j - W₂' v j|) * F1 * Z)
      = ((∑ v, ∑ j, |W₂ v j - W₂' v j|) * F1 * Z) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have e2 : (∑ v, (∑ j, |W₂' v j|) * (G1 * Z))
      = ((∑ v, ∑ j, |W₂' v j|) * (G1 * Z)) := by
    rw [← Finset.sum_mul]
  calc (∑ v, |mlpApply W₁ W₂ z v - mlpApply W₁' W₂' z v|)
      ≤ ∑ v, ((∑ j, |W₂ v j - W₂' v j|) * F1 * Z
        + (∑ j, |W₂' v j|) * (G1 * Z)) :=
        Finset.sum_le_sum fun v _ => hpt v
    _ = ((∑ v, ∑ j, |W₂ v j - W₂' v j|) * F1 * Z
        + (∑ v, ∑ j, |W₂' v j|) * (G1 * Z)) := by
        rw [Finset.sum_add_distrib, e1, e2]
    _ ≤ ((Fintype.card V : ℝ) * F2) * F1 * Z
        + ((Fintype.card V : ℝ) * G2) * (G1 * Z) := by
        refine add_le_add ?_ ?_
        · gcongr
        · gcongr
    _ = (Fintype.card V : ℝ) * Z * (F1 * F2 + G2 * G1) := by ring


/-! ## Section B: одновременный certified шаг trunk+head -/

variable {K : Type} [Fintype K] [Nonempty K] {d : ℕ}

omit [Nonempty V] [Nonempty K] in
/-- Логит-смещение от смены ствола: при фиксированной голове
(p, θ) и координатном смещении ствола `|Δtrunk t v| ≤ dd`
каждый логит смещается не более чем на `headLip · dd`
(ℓ1-норма шаблона, взвешенная параметрами головы).
Mechanika: явные суммы `lmLogits_eq_sum` + abs-суммирование. -/
theorem trunk_disp_logit_le (m : LM V K d)
    (bs' : List (CertifiedBlock V)) (x : ℕ → V → ℝ) (t : ℕ)
    (a : K) (dd : ℝ)
    (hD : ∀ v : V, |lmTrunk bs' x t v - lmTrunk m.blocks x t v| ≤ dd) :
    |lmLogits { m with blocks := bs' } x t a - lmLogits m x t a|
      ≤ headLip m a * dd := by
  have h1 := lmLogits_eq_sum { m with blocks := bs' } x t a
  have h2 := lmLogits_eq_sum m x t a
  have hsumdiff : (∑ j, ∑ v, m.headProj a j v * lmTrunk bs' x t v
          * m.headTheta.ofLp j)
      - (∑ j, ∑ v, m.headProj a j v * lmTrunk m.blocks x t v
          * m.headTheta.ofLp j)
      = ∑ j, ∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j := by
    have hin : ∀ j : Fin d,
        (∑ v, m.headProj a j v * lmTrunk bs' x t v * m.headTheta.ofLp j)
          - (∑ v, m.headProj a j v * lmTrunk m.blocks x t v
            * m.headTheta.ofLp j)
        = ∑ v, m.headProj a j v
            * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j := by
      intro j
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hin j
  have hterm : ∀ j : Fin d, ∀ v : V,
      |m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|
      ≤ |m.headProj a j v * m.headTheta.ofLp j| * dd := by
    intro j v
    have h1 : |m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|
        = |m.headProj a j v * m.headTheta.ofLp j|
            * |lmTrunk bs' x t v - lmTrunk m.blocks x t v| := by
      rw [abs_mul, abs_mul, abs_mul]; ring
    rw [h1]
    gcongr
    exact hD v
  rw [h1, h2]
  simp only
  rw [hsumdiff]
  have habs1 : |∑ j, ∑ v, m.headProj a j v
        * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|
      ≤ ∑ j, |∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j| :=
    Finset.abs_sum_le_sum_abs
      (fun j : Fin d => ∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j)
      Finset.univ
  have habs2 : ∀ j : Fin d,
      |∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|
      ≤ ∑ v, |m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j| :=
    fun j => Finset.abs_sum_le_sum_abs
      (fun v : V => m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j)
      Finset.univ
  have hterm2 : ∀ j : Fin d,
      (∑ v, |m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|)
      ≤ (∑ v, |m.headProj a j v * m.headTheta.ofLp j|) * dd := by
    intro j
    calc (∑ v, |m.headProj a j v
            * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|)
        ≤ ∑ v, |m.headProj a j v * m.headTheta.ofLp j| * dd :=
          Finset.sum_le_sum fun v _ => hterm j v
      _ = (∑ v, |m.headProj a j v * m.headTheta.ofLp j|) * dd :=
          (Finset.sum_mul _ _ _).symm
  calc |∑ j, ∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j|
      ≤ ∑ j, |∑ v, m.headProj a j v
          * (lmTrunk bs' x t v - lmTrunk m.blocks x t v) * m.headTheta.ofLp j| :=
          habs1
    _ ≤ ∑ j, (∑ v, |m.headProj a j v * m.headTheta.ofLp j|) * dd :=
        Finset.sum_le_sum fun j _ => le_trans (habs2 j) (hterm2 j)
    _ = (∑ j, ∑ v, |m.headProj a j v * m.headTheta.ofLp j|) * dd :=
        (Finset.sum_mul _ _ _).symm
    _ = headLip m a * dd := rfl



/-- Одновременное обновление: новый ствол bs' + certified head-шаг
на СТАРЫХ features (направление и размер шага вычислены на m,
применены к новой голове в новом стволе). -/
noncomputable def jointUpdate (m : LM V K d)
    (bs' : List (CertifiedBlock V)) (x : ℕ → V → ℝ) (t : ℕ)
    (tgt : K) : LM V K d where
  blocks := bs'
  headProj := m.headProj
  headTheta := Hagi.Model.ceNextParameters (lmFeatures m x t)
    m.headTheta tgt (Hagi.Model.safeStepSize (lmFeatures m x t)
      m.headTheta tgt)

/-- Одновременный certified шаг trunk+head (ГЛАВНАЯ теорема):
за ОДИН переход m → m' = ⟨bs', headProj, θ'⟩ (меняются блоки ствола
И параметры головы; θ' = certified head-шаг CEDescent на СТАРЫХ
features) CE уменьшается на certified head-спад минус additive
trunk-канал 2·HL·dd:
- head-канал: `ceOneHot_safeStep_le_residual` на F = lmFeatures m
  x t даёт − 2A²/R² (R = ceStepRange > 0);
- trunk-канал: CE-lip 2‖·‖sup + `trunk_disp_logit_le` на НОВОЙ
  голове (θ'-взвешенная headLip-норма HL, measured смещение dd).
Cross-член ПОГЛОЩёН треугольником в 2·HL·dd (см. limits модуля). -/
theorem joint_head_trunk_step_le (m : LM V K d)
    (bs' : List (CertifiedBlock V)) (x : ℕ → V → ℝ) (t : ℕ)
    (tgt : K)
    (hr : 0 < Hagi.Model.ceStepRange (lmFeatures m x t) m.headTheta tgt)
    (HL dd : ℝ)
    (hHL : ∀ a : K, headLip (jointUpdate m bs' x t tgt) a ≤ HL)
    (hD : ∀ v : V,
      |lmTrunk bs' x t v - lmTrunk m.blocks x t v| ≤ dd) :
    Hagi.ceOneHot tgt (lmLogits (jointUpdate m bs' x t tgt) x t)
      ≤ Hagi.ceOneHot tgt (lmLogits m x t)
        - 2 * Hagi.Model.ceAlignment (lmFeatures m x t) m.headTheta tgt ^ 2
            / Hagi.Model.ceStepRange (lmFeatures m x t) m.headTheta tgt ^ 2
        + 2 * HL * dd := by
  -- новая голова θ' = certified head-шаг на старых features
  have hjoint : jointUpdate m bs' x t tgt
      = ⟨bs', m.headProj, Hagi.Model.ceNextParameters (lmFeatures m x t)
          m.headTheta tgt (Hagi.Model.safeStepSize (lmFeatures m x t)
            m.headTheta tgt)⟩ := rfl
  set m₁ : LM V K d :=
    ⟨m.blocks, m.headProj, Hagi.Model.ceNextParameters (lmFeatures m x t)
      m.headTheta tgt (Hagi.Model.safeStepSize (lmFeatures m x t)
        m.headTheta tgt)⟩ with hm₁
  -- head-канал: certified спад на СТАРЫХ features (механика lmHeadUpdate)
  have hhead : Hagi.ceOneHot tgt (lmLogits m₁ x t)
      ≤ Hagi.ceOneHot tgt (lmLogits m x t)
        - 2 * Hagi.Model.ceAlignment (lmFeatures m x t) m.headTheta tgt ^ 2
            / Hagi.Model.ceStepRange (lmFeatures m x t) m.headTheta tgt ^ 2 :=
    Hagi.Model.ceOneHot_safeStep_le_residual (lmFeatures m x t) m.headTheta tgt hr
  -- dd неотрицательно (насыщение от любого v)
  have hdd : 0 ≤ dd :=
    le_trans (abs_nonneg _)
      (hD (Classical.arbitrary V))
  -- trunk-канал по координатам
  have hzdiff : ∀ a : K,
      |lmLogits (jointUpdate m bs' x t tgt) x t a - lmLogits m₁ x t a|
      ≤ HL * dd := by
    intro a
    have hle := trunk_disp_logit_le m₁ bs' x t a dd hD
    rw [hjoint]
    have hHLm₁ : headLip m₁ a ≤ HL := by
      have : headLip m₁ a = headLip (jointUpdate m bs' x t tgt) a := rfl
      rw [this]; exact hHL a
    calc |lmLogits ⟨bs', m.headProj, Hagi.Model.ceNextParameters
            (lmFeatures m x t) m.headTheta tgt
            (Hagi.Model.safeStepSize (lmFeatures m x t) m.headTheta tgt)⟩ x t a
          - lmLogits m₁ x t a|
        ≤ headLip m₁ a * dd := hle
      _ ≤ HL * dd := by
          exact mul_le_mul_of_nonneg_right hHLm₁ hdd
  -- sup-норма разности логитов
  have hHLnn : 0 ≤ HL :=
    le_trans (show (0:ℝ) ≤ headLip (jointUpdate m bs' x t tgt)
        (Classical.arbitrary K) from by
          unfold headLip
          exact Finset.sum_nonneg fun j _ =>
            Finset.sum_nonneg fun v _ => abs_nonneg _) (hHL _)
  have hsup : ‖lmLogits (jointUpdate m bs' x t tgt) x t
      - lmLogits m₁ x t‖ ≤ HL * dd := by
    refine (pi_norm_le_iff_of_nonneg
      (mul_nonneg hHLnn hdd)).mpr ?_
    intro a
    simpa [Real.norm_eq_abs, Pi.sub_apply] using hzdiff a
  -- CE-lip соединяет каналы
  have hn : (2:ℝ) * ‖lmLogits (jointUpdate m bs' x t tgt) x t
      - lmLogits m₁ x t‖ ≤ 2 * HL * dd := by
    have h := hsup
    linarith
  have h2 : |Hagi.ceOneHot tgt (lmLogits (jointUpdate m bs' x t tgt) x t)
      - Hagi.ceOneHot tgt (lmLogits m₁ x t)| ≤ 2 * HL * dd :=
    (ce_head_lipschitz_in_logits tgt
      (lmLogits (jointUpdate m bs' x t tgt) x t)
      (lmLogits m₁ x t)).trans hn
  have hle : Hagi.ceOneHot tgt (lmLogits (jointUpdate m bs' x t tgt) x t)
      ≤ Hagi.ceOneHot tgt (lmLogits m₁ x t) + 2 * HL * dd := by
    have h3 := le_abs_self (Hagi.ceOneHot tgt
      (lmLogits (jointUpdate m bs' x t tgt) x t)
      - Hagi.ceOneHot tgt (lmLogits m₁ x t))
    linarith
  linarith


/-- Strict-вариант (мост к certify-then-commit): если certified
head-спад доминирует additive trunk-канал, одновременный шаг
СТРОГО уменьшает CE — критерий приёма шага в интерфейсе
`commit_drop_checked` (не правится; консумируется его
интерфейс drop > 0). -/
theorem joint_step_commit_strict (m : LM V K d)
    (bs' : List (CertifiedBlock V)) (x : ℕ → V → ℝ) (t : ℕ)
    (tgt : K)
    (hr : 0 < Hagi.Model.ceStepRange (lmFeatures m x t) m.headTheta tgt)
    (HL dd : ℝ)
    (hHL : ∀ a : K, headLip (jointUpdate m bs' x t tgt) a ≤ HL)
    (hD : ∀ v : V,
      |lmTrunk bs' x t v - lmTrunk m.blocks x t v| ≤ dd)
    (hstrict : 2 * HL * dd
      < 2 * Hagi.Model.ceAlignment (lmFeatures m x t) m.headTheta tgt ^ 2
          / Hagi.Model.ceStepRange (lmFeatures m x t) m.headTheta tgt ^ 2) :
    Hagi.ceOneHot tgt (lmLogits (jointUpdate m bs' x t tgt) x t)
      < Hagi.ceOneHot tgt (lmLogits m x t) := by
  have h := joint_head_trunk_step_le m bs' x t tgt hr HL dd hHL hD
  exact lt_of_le_of_lt h (by linarith)

/-! ## Section C: производные смещения ствола для атомов -/

omit [Nonempty V] in
/-- Смена ГОЛОВНОГО (первого) блока списка: смещение trunk-выхода
доминируется произведением lip-констант ХВОСТА и смещением выхода
изменённого блока (foldl-разворот + `trunk_lipschitz` хвоста). -/
theorem trunk_disp_head_change (b b' : CertifiedBlock V)
    (bs : List (CertifiedBlock V)) (x : ℕ → V → ℝ) (t : ℕ) :
    dPre (lmTrunk (b' :: bs) x) (lmTrunk (b :: bs) x) t
      ≤ (blocksLip bs : ℝ) * dPre (blockApply b'.toTransformerBlock x)
          (blockApply b.toTransformerBlock x) t := by
  simp only [lmTrunk, List.foldl_cons]
  exact trunk_lipschitz bs
    (blockApply b'.toTransformerBlock x)
    (blockApply b.toTransformerBlock x) t

/-- Параметрическое смещение MLP-блока (по весам, при общем входе):
per-position №1-смещение выхода блока = №1-смещению mlpApply
(residual общий) ≤ выведенной константе `mlp_param_lip`. -/
theorem certifiedMLP_param_dPre (W₁ W₂ W₁' W₂' : V → V → ℝ)
    (x : ℕ → V → ℝ) (t : ℕ) :
    dPre (blockApply (certifiedMLP W₁' W₂').toTransformerBlock x)
        (blockApply (certifiedMLP W₁ W₂).toTransformerBlock x) t
      ≤ ∑ i ∈ Finset.range (t + 1),
          (Fintype.card V : ℝ) * Real.sqrt (∑ k, x i k ^ 2)
            * (Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
                * Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
              + Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2)
                * Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2)) := by
  have hterm : ∀ i ∈ Finset.range (t + 1),
      (∑ v, |blockApply (certifiedMLP W₁' W₂').toTransformerBlock x i v
        - blockApply (certifiedMLP W₁ W₂).toTransformerBlock x i v|)
      ≤ (Fintype.card V : ℝ) * Real.sqrt (∑ k, x i k ^ 2)
            * (Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
                * Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
              + Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2)
                * Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2)) := by
    intro i _
    have hsplit : ∀ v : V,
        blockApply (certifiedMLP W₁' W₂').toTransformerBlock x i v
          - blockApply (certifiedMLP W₁ W₂).toTransformerBlock x i v
        = mlpApply W₁' W₂' (x i) v - mlpApply W₁ W₂ (x i) v := by
      intro v
      simp only [Hagi.Model.LMCompose.blockApply, certifiedMLP]
      ring
    calc (∑ v, |blockApply (certifiedMLP W₁' W₂').toTransformerBlock x i v
            - blockApply (certifiedMLP W₁ W₂).toTransformerBlock x i v|)
        = (∑ v, |mlpApply W₁' W₂' (x i) v - mlpApply W₁ W₂ (x i) v|) := by
          exact Finset.sum_congr rfl fun v _ => by rw [hsplit v]
      _ ≤ (Fintype.card V : ℝ) * Real.sqrt (∑ k, x i k ^ 2)
            * (Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
                * Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
              + Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2)
                * Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2)) :=
            (by simpa [abs_sub_comm] using mlp_param_lip W₁ W₂ W₁' W₂' (x i))
  show (∑ i ∈ Finset.range (t + 1),
      ∑ v, |blockApply (certifiedMLP W₁' W₂').toTransformerBlock x i v
        - blockApply (certifiedMLP W₁ W₂).toTransformerBlock x i v|)
    ≤ _
  exact Finset.sum_le_sum hterm


/-- ПОТРЕБЛЕНИЕ (RMSNorm-g): смещение trunk-выхода ProvenTrunk при
смене ТОЛЬКО gain g первого атома — выведенная формула: хвост
[MLP, ConvAtt] с произведением lip (1 + √n·F₂·F₁)·2
(`blocksLip_eq_trunkLip`-механика) доминирует √n·∑ℓ|g−g'|
смещение RMSNorm-атома (`rms_gain_param_disp`). -/
theorem provenTrunk_gain_param_disp (g g' : V → ℝ) (G : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ))
    (hg' : ∀ v, |g' v| ≤ (G : ℝ)) (W₁ W₂ : V → V → ℝ)
    (x : ℕ → V → ℝ) (t : ℕ) :
    dPre (lmTrunk (provenBlocks g' G ε hε hg' W₁ W₂) x)
        (lmTrunk (provenBlocks g G ε hε hg W₁ W₂) x) t
      ≤ ((1 + Real.sqrt (Fintype.card V)
            * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
            * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)) * 2)
        * (Real.sqrt (Fintype.card V)
            * ∑ _ ∈ Finset.range (t + 1), ∑ v, |g v - g' v|) := by
  -- разворачиваем списки атомов
  have hlists : [certifiedRMSNorm g' G ε hε hg',
      certifiedMLP W₁ W₂, certifiedConvAtt (V := V)]
      = [certifiedRMSNorm g' G ε hε hg', certifiedMLP W₁ W₂,
        certifiedConvAtt (V := V)] := rfl
  -- хвостовая константа
  have htail : (blocksLip [certifiedMLP W₁ W₂,
      certifiedConvAtt (V := V)] : ℝ)
      = (1 + Real.sqrt (Fintype.card V)
            * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
            * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)) * 2 := by
    simp only [blocksLip, List.map_cons, List.prod_cons, List.prod_nil,
      List.map_nil, NNReal.coe_mul, mul_one]
    rfl
  -- смещение RMSNorm-блока
  have hrms : ∀ i ∈ Finset.range (t + 1),
      (∑ v, |blockApply (certifiedRMSNorm g' G ε hε hg').toTransformerBlock
            x i v
        - blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock
            x i v|)
      ≤ Real.sqrt (Fintype.card V) * (∑ v, |g v - g' v|) := by
    intro i _
    have hterm : ∀ v : V,
        |blockApply (certifiedRMSNorm g' G ε hε hg').toTransformerBlock
            x i v
          - blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock
            x i v|
      ≤ Real.sqrt (Fintype.card V) * |g v - g' v| := by
      intro v
      have hsplit :
          blockApply (certifiedRMSNorm g' G ε hε hg').toTransformerBlock
            x i v
          - blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock
            x i v
        = g' v * rmsN ε (x i) v - g v * rmsN ε (x i) v := by
        simp only [Hagi.Model.LMCompose.blockApply, certifiedRMSNorm]
        ring
      have hmul : g' v * rmsN ε (x i) v - g v * rmsN ε (x i) v
          = (g' v - g v) * rmsN ε (x i) v := by ring
      rw [hsplit, hmul, abs_mul]
      calc |g' v - g v| * |rmsN ε (x i) v|
          ≤ |g' v - g v| * Real.sqrt (Fintype.card V) :=
            mul_le_mul_of_nonneg_left (rmsN_coord_le ε hε (x i) v)
              (abs_nonneg _)
        _ = Real.sqrt (Fintype.card V) * |g v - g' v| := by
            rw [abs_sub_comm]; ring
    calc (∑ v, |blockApply (certifiedRMSNorm g' G ε hε hg').toTransformerBlock
            x i v
          - blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock
            x i v|)
        ≤ ∑ v, Real.sqrt (Fintype.card V) * |g v - g' v| :=
          Finset.sum_le_sum fun v _ => hterm v
      _ = Real.sqrt (Fintype.card V) * (∑ v, |g v - g' v|) :=
          (Finset.mul_sum _ _ _).symm
  have hmain := trunk_disp_head_change
    (certifiedRMSNorm g G ε hε hg)
    (certifiedRMSNorm g' G ε hε hg')
    [certifiedMLP W₁ W₂, certifiedConvAtt (V := V)] x t
  refine le_trans hmain ?_
  rw [htail]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  show (∑ i ∈ Finset.range (t + 1),
      ∑ v, |blockApply (certifiedRMSNorm g' G ε hε hg').toTransformerBlock
        x i v
      - blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock
        x i v|)
    ≤ Real.sqrt (Fintype.card V)
      * ∑ i ∈ Finset.range (t + 1), ∑ v, |g v - g' v|
  refine le_trans (Finset.sum_le_sum hrms) ?_
  rw [← Finset.mul_sum]

/-- ПОТРЕБЛЕНИЕ (MLP-веса): смещение trunk-выхода ProvenTrunk при
смене ТОЛЬКО весов W₁/W₂ среднего атома — выведенная формула:
ConvAtt-хвост с lip = 2 доминирует параметрическое смещение MLP
(`certifiedMLP_param_dPre`), промежуточное состояние общее (первый
атом RMSNorm не менялся). -/
theorem provenTrunk_mlp_param_disp (g : V → ℝ) (G : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ))
    (W₁ W₂ W₁' W₂' : V → V → ℝ)
    (x : ℕ → V → ℝ) (t : ℕ) :
    dPre (lmTrunk (provenBlocks g G ε hε hg W₁' W₂') x)
        (lmTrunk (provenBlocks g G ε hε hg W₁ W₂) x) t
      ≤ 2 * (∑ i ∈ Finset.range (t + 1),
          (Fintype.card V : ℝ) * Real.sqrt (∑ k,
            blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock x i k ^ 2)
            * (Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
                * Real.sqrt (∑ v, ∑ j, (W₂ v j - W₂' v j) ^ 2)
              + Real.sqrt (∑ v, ∑ j, W₂' v j ^ 2)
                * Real.sqrt (∑ j, ∑ k, (W₁ j k - W₁' j k) ^ 2))) := by
  -- разворачиваем списки атомов
  have hsplit2 : provenBlocks g G ε hε hg W₁' W₂'
      = certifiedRMSNorm g G ε hε hg
        :: [certifiedMLP W₁' W₂', certifiedConvAtt (V := V)] := rfl
  have hsplit3 : provenBlocks g G ε hε hg W₁ W₂
      = certifiedRMSNorm g G ε hε hg
        :: [certifiedMLP W₁ W₂, certifiedConvAtt (V := V)] := rfl
  rw [hsplit2, hsplit3]
  -- lmTrunk [b, M', A] = lmTrunk (M' :: [A]) (blockApply b x): смена СРЕДНЕГО блока
  have heq : lmTrunk (certifiedRMSNorm g G ε hε hg
        :: [certifiedMLP W₁' W₂', certifiedConvAtt (V := V)]) x
      = lmTrunk (certifiedMLP W₁' W₂'
          :: [certifiedConvAtt (V := V)])
          (blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock x) := rfl
  have heq2 : lmTrunk (certifiedRMSNorm g G ε hε hg
        :: [certifiedMLP W₁ W₂, certifiedConvAtt (V := V)]) x
      = lmTrunk (certifiedMLP W₁ W₂
          :: [certifiedConvAtt (V := V)])
          (blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock x) := rfl
  rw [heq, heq2]
  have hmain := trunk_disp_head_change
    (certifiedMLP W₁ W₂) (certifiedMLP W₁' W₂')
    [certifiedConvAtt (V := V)]
    (blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock x) t
  refine le_trans hmain ?_
  have hlip : (blocksLip [certifiedConvAtt (V := V)] : ℝ) = 2 := by
    simp [blocksLip, certifiedConvAtt]
  rw [hlip]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact certifiedMLP_param_dPre W₁ W₂ W₁' W₂'
    (blockApply (certifiedRMSNorm g G ε hε hg).toTransformerBlock x) t

/-! ## Section D: trade-off vs alternating (арифметика гарантий) -/

/-- Сравнение ГАРАНТИЙ за один период k шагов
(арифметика, НЕ механика): joint-гарантия
«start − k·δh + k·damageJ» сильнее alternating-гарантии
«start − k·Δh + damageB» ровно при hcond. Обе величины —
ВЕРХНИЕ границы (среди joint: `joint_head_trunk_step_le`
с δh = 2A²/R², damageJ = 2·HL·dd; среди alternating:
`alternating_trajectory_bound_derived` c damageB = 2·headLip·D);
фактические значения могут лежать ниже любой из
них — теорема сравнивает гарантии, а не
траектории (честное ограничение). -/
theorem joint_bound_beats_alternating_bound
    (L0 δh Δh damageJ damageB k : ℝ)
    (hcond : k * (δh - damageJ) > k * Δh - damageB) :
    L0 - k * δh + k * damageJ < L0 - k * Δh + damageB := by
  linarith

end Hagi.Training.JointTrunkHead

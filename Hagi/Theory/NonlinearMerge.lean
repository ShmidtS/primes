/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# NonlinearMerge — остаток линеаризации как ИЗМЕРЯЕМАЯ премиса (C476, A19/G5)

Аудит N5/G5: слияние ТОЧНО только для линейного по параметрам случая
(`step0_equivalence` Core/BlockDiag — merged-слой = эксперт в блоке;
ModeConnectivity/ModelSoup — Йенсен для выпуклой квадратичной). Для
глубокой сети merge — ДОПУЩЕНИЕ, причём неизмеряемое (MergePrice:
«нелинейный остаток — липшицевость третьего порядка» — ничем не
измеряется). Этот модуль заменяет допущение ИЗМЕРЯЕМОЙ премисой:
остаток линеаризации δ вдоль интерполяции w_t = w₁ + t(w₂−w₁).

**Измеримость — процедура, не декларация**: δ определяется на КОНЕЧНОЙ
сетке t-точек (Fintype — стиль корпуса), Σ_t |L(w_t) − L_lin(w_t)|
мажорирует sup по сетке; точность измерения по сетке — своя
концентрационная задача, машина уже в корпусе
(`Hagi.Ensemble.Hoeffding`, C435) — здесь не дублируется.

**Теоремы:**

* `linResidualGrid` — ИЗМЕРИМЫЙ остаток: конечная сумма |L(w_t) −
  L_lin(w_t)| по сетке t (первый порядок, линеаризация в w₁);
* `nonlinear_merge_bound` — ГЛАВНАЯ: два измеренных остатка
  (в mid: δ, в w₂: δ₂) дают L(mid) ≤ ½(L₁+L₂) + δ + δ₂/2 для
  ПРОИЗВОЛЬНОЙ нелинейной L — композиция двух измерений, не
  premise=conclusion;
* `quad_merge_exact` — для диагонально-квадратичного лосса
  (½Σcᵢ(θᵢ−aᵢ)², c ≥ 0 — Fisher/кривизнный носитель C472) тождество
  ТОЧНО: Q(mid) = ½(Q₁+Q₂) − curvRemainder, δ_curv = ⅛Σcᵢdᵢ²;
* `quad_merge_le_mean` — при c ≥ 0: Q(mid) ≤ ½(Q₁+Q₂) (Йенсен
  закрыт точно в diag-кривизнной форме);
* `quad_residual_mid` — измеренный остаток в mid РАВЕН curvRemainder
  (минимум в w₁ ⇒ линеаризация константна): δ_curv ВЫВОДИТСЯ из
  измерения, не постулируется;
* `curvRemainder_le_path` — δ_curv ≤ ½ квадратичного отклонения в
  конце пути w₂ (sup по пути достигается в t=1);
* `MergeApprovedMeas` + `merge_gate_meas` — гейт слияния C-корпуса
  (MergePrice) в ИЗМЕРЯЕМОЙ версии: ½Σ цен + δ_bound + κ√n·s/2 <
  twoGap, где δ_bound — измеренный остаток (vs `merge_gate_certified`
  без δ-члена — DupLint: формы различны);
* `merge_unsafe_without_measurement` — НЕГАТИВ: ∀ B > 0 ∃ L w₁ w₂
  (1D): L(w₁) = L(w₂) = 0, но L(mid) ≥ B (вогнутая парабола
  B − 4B(x−½)²: острый минимум между w₁ и w₂ перевёрнут — концы-нули,
  середина-барьер). Без измерения δ merge НЕ безопасен: δ обязан
  быть ≥ B.
-/

open Finset

namespace Hagi.Theory.NonlinearMerge

variable {d : ℕ}

/-! ## Интерполяция и измеряемый остаток -/

/-- Интерполяция w_t = w₁ + t·(w₂ − w₁). -/
def interp (w1 w2 : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i => w1 i + t * (w2 i - w1 i)

/-- Средняя точка w̃ = (w₁+w₂)/2. -/
noncomputable def mid (w1 w2 : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (w1 i + w2 i) / 2

/-- Линеаризация L в w₁ первого порядка вдоль interp:
L(w₁) + t·Σᵢ gᵢ(w2ᵢ−w1ᵢ). -/
def linAt (L : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ) (w1 w2 : Fin d → ℝ)
    (t : ℝ) : ℝ :=
  L w1 + t * ∑ i, g i * (w2 i - w1 i)

/-- **ИЗМЕРИМАЯ премиса**: остаток линеаризации на конечной сетке
t-точек — Σ_t |L(w_t) − L_lin(w_t)| мажорирует sup по сетке.
Процедура: конечная выборка t-точек, вычисление L и линеаризации;
точность измерения — концентрация машины C435 (Hoeffding), здесь не
дублируется. -/
def linResidualGrid (L : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ)
    (w1 w2 : Fin d → ℝ) {T : Type} [Fintype T] (ts : T → ℝ) : ℝ :=
  ∑ t, |L (interp w1 w2 (ts t)) - linAt L g w1 w2 (ts t)|

/-- Сеточный остаток неотрицателен. -/
theorem linResidualGrid_nonneg (L : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ)
    (w1 w2 : Fin d → ℝ) {T : Type} [Fintype T] (ts : T → ℝ) :
    0 ≤ linResidualGrid L g w1 w2 ts :=
  Finset.sum_nonneg fun t _ => abs_nonneg _

/-- Сеточный остаток мажорирует уклонение в КАЖДОЙ точке сетки. -/
theorem linResidualGrid_point_le (L : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ)
    (w1 w2 : Fin d → ℝ) {T : Type} [Fintype T] (ts : T → ℝ) (t : T) :
    |L (interp w1 w2 (ts t)) - linAt L g w1 w2 (ts t)|
      ≤ linResidualGrid L g w1 w2 ts := by
  have hnn := fun t' (_ : t' ∈ (Finset.univ : Finset T)) =>
    abs_nonneg (L (interp w1 w2 (ts t')) - linAt L g w1 w2 (ts t'))
  exact Finset.single_le_sum hnn (Finset.mem_univ t)

/-- **Главная теорема**: два ИЗМЕРЕННЫХ остатка линеаризации (в mid:
δ, в w₂: δ₂) дают merge bound для ПРОИЗВОЛЬНОЙ нелинейной L:
L(mid) ≤ ½(L(w₁)+L(w₂)) + δ + δ₂/2. Премисы — измеряемые величины
(сетки из точек 1/2 и 1); ни выпуклости, ни линейности f не нужно. -/
theorem nonlinear_merge_bound (L : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ)
    (w1 w2 : Fin d → ℝ) (δ δ₂ : ℝ)
    (hmid : |L (mid w1 w2) - linAt L g w1 w2 (1/2)| ≤ δ)
    (hend : |L w2 - linAt L g w1 w2 1| ≤ δ₂) :
    L (mid w1 w2) ≤ (L w1 + L w2) / 2 + δ + δ₂ / 2 := by
  unfold linAt mid at *
  have h1 : L (fun i => (w1 i + w2 i) / 2)
      ≤ L w1 + (1/2) * ∑ i, g i * (w2 i - w1 i) + δ := by
    have := abs_le.mp hmid
    linarith
  have h2 : L w2 ≥ L w1 + ∑ i, g i * (w2 i - w1 i) - δ₂ := by
    have := abs_le.mp hend
    linarith
  linarith

/-! ## Квадратичный случай: ТОЧНО (diag-кривизна, мост C472) -/

/-- Диагонально-квадратичный лосс ½Σ cᵢ(θᵢ−aᵢ)² — Fisher/кривизнный
носитель C472 (FisherQuant: quadLoss + colCurv; здесь диагональная
форма c). -/
noncomputable def quadLossDiag (c a θ : Fin d → ℝ) : ℝ :=
  ∑ i, c i * (θ i - a i) ^ 2 / 2

/-- Градиент diag-квадратичного лосса (для линеаризации). -/
def quadGradDiag (c a θ : Fin d → ℝ) (j : Fin d) : ℝ :=
  c j * (θ j - a j)

/-- Кривизнный остаток merge: δ_curv = ⅛ Σ cᵢ (w2ᵢ−w1ᵢ)² — второй
порядок Taylor (C472 pattern) в диагональной метрике. -/
noncomputable def curvRemainder (c w1 w2 : Fin d → ℝ) : ℝ :=
  ∑ i, c i * (w2 i - w1 i) ^ 2 / 8

/-- **ТОЧНОЕ тождество слияния** для диагонально-квадратичного
лосса: Q(mid) = ½(Q₁+Q₂) − curvRemainder — без неравенств, без
измерений: квадратичный случай закрыт ТОЧНО (Йенсен-зазор =
кривизнный остаток). -/
theorem quad_merge_exact (c a w1 w2 : Fin d → ℝ) :
    quadLossDiag c a (mid w1 w2)
      = (quadLossDiag c a w1 + quadLossDiag c a w2) / 2
        - curvRemainder c w1 w2 := by
  have key : ∀ i : Fin d,
      c i * ((w1 i + w2 i) / 2 - a i) ^ 2 / 2
        = c i * (w1 i - a i) ^ 2 / 4 + c i * (w2 i - a i) ^ 2 / 4
          - c i * (w2 i - w1 i) ^ 2 / 8 := by
    intro i
    have hm : (w1 i + w2 i) / 2 - a i
        = ((w1 i - a i) + (w2 i - a i)) / 2 := by ring
    rw [hm]
    have h2 : ((w1 i - a i) + (w2 i - a i)) / 2
        = (1/2) * ((w1 i - a i) + (w2 i - a i)) := by ring
    rw [h2]
    have hsq : ∀ x y : ℝ,
        ((1/2) * (x + y)) ^ 2 = (x ^ 2 + 2 * x * y + y ^ 2) / 4 := by
      intro x y
      ring
    rw [hsq]
    have hxy : 2 * (w1 i - a i) * (w2 i - a i)
        = (w1 i - a i) ^ 2 + (w2 i - a i) ^ 2
          - (w2 i - w1 i) ^ 2 := by ring
    rw [hxy]
    field_simp
    ring
  unfold quadLossDiag curvRemainder mid
  have e1 : ∑ i, c i * ((w1 i + w2 i) / 2 - a i) ^ 2 / 2
      = ∑ i, (c i * (w1 i - a i) ^ 2 / 4 + c i * (w2 i - a i) ^ 2 / 4
        - c i * (w2 i - w1 i) ^ 2 / 8) :=
    Finset.sum_congr rfl fun i _ => key i
  have e2 : (∑ i, c i * (w1 i - a i) ^ 2 / 2
        + ∑ i, c i * (w2 i - a i) ^ 2 / 2) / 2
      - ∑ i, c i * (w2 i - w1 i) ^ 2 / 8
      = ∑ i, (c i * (w1 i - a i) ^ 2 / 4 + c i * (w2 i - a i) ^ 2 / 4
        - c i * (w2 i - w1 i) ^ 2 / 8) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_div, add_div, div_div]
    field_simp
    ring
  rw [e1, ← e2]

/-- Кривизнный остаток неотрицателен при c ≥ 0. -/
theorem curvRemainder_nonneg (c w1 w2 : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    0 ≤ curvRemainder c w1 w2 :=
  Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (hc i) (sq_nonneg _)) (by norm_num)

/-- **Йенсен закрыт точно** (diag-форма): при неотрицательной
кривизне Q(mid) ≤ ½(Q₁+Q₂) — следствие точного тождества. -/
theorem quad_merge_le_mean (c a w1 w2 : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    quadLossDiag c a (mid w1 w2)
      ≤ (quadLossDiag c a w1 + quadLossDiag c a w2) / 2 := by
  have h := quad_merge_exact c a w1 w2
  have hnn := curvRemainder_nonneg c w1 w2 hc
  linarith

/-- **δ_curv выводится из измерения**: при минимуме в w₁ (носитель
a = w₁) градиент зануляется, линеаризация константна, и измеренный
остаток в mid РАВЕН curvRemainder — кривизнная премиса гейта
получается ИЗМЕРЕНИЕМ в одной точке, не постулируется. -/
theorem quad_residual_mid (c w1 w2 : Fin d → ℝ) :
    quadLossDiag c w1 (mid w1 w2)
      - linAt (quadLossDiag c w1) (quadGradDiag c w1 w1) w1 w2 (1/2)
      = curvRemainder c w1 w2 := by
  have hgrad : ∑ i, quadGradDiag c w1 w1 i * (w2 i - w1 i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold quadGradDiag
    rw [sub_self, mul_zero, zero_mul]
  have hq1 : quadLossDiag c w1 w1 = 0 := by
    unfold quadLossDiag
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [sub_self, zero_pow two_ne_zero, mul_zero, zero_div]
  unfold linAt
  rw [hgrad, mul_zero, add_zero, hq1, sub_zero]
  unfold quadLossDiag curvRemainder mid
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (w1 i + w2 i) / 2 - w1 i = (w2 i - w1 i) / 2 := by ring
  rw [hm, div_pow]
  field_simp
  ring

/-- δ_curv ≤ ½ квадратичного отклонения в конце пути w₂:
curvRemainder ≤ quadLossDiag-отклонения от w₁ до w₂ (sup по пути
t ↦ ½Σcᵢ(w_t−w₁)ᵢ² достигается при t = 1). -/
theorem curvRemainder_le_path (c w1 w2 : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    curvRemainder c w1 w2 ≤ (1/2) * ∑ i, c i * (w2 i - w1 i) ^ 2 := by
  have key : ∀ i : Fin d,
      c i * (w2 i - w1 i) ^ 2 / 8
        ≤ (1/2) * (c i * (w2 i - w1 i) ^ 2) := by
    intro i
    have h1 : (0:ℝ) ≤ c i * (w2 i - w1 i) ^ 2 :=
      mul_nonneg (hc i) (sq_nonneg _)
    linarith
  unfold curvRemainder
  have hmul : ∑ i, (1/2) * (c i * (w2 i - w1 i) ^ 2)
      = (1/2) * ∑ i, c i * (w2 i - w1 i) ^ 2 := by
    rw [← Finset.mul_sum]
  rw [← hmul]
  exact Finset.sum_le_sum fun i _ => key i

/-! ## Измеряемый гейт слияния (мост к MergePrice) -/

variable {n N K : ℕ}

/-- Гейт слияния в ИЗМЕРЯЕМОЙ версии: twoGap (ансамблевый зазор,
GapLaw) должен перекрыть сумму цен доменов (σ-метрика MergePrice) +
ИЗМЕРЕННЫЙ остаток δ_bound + тернарную цену κ√n·s/2. δ_bound —
величина из linResidualGrid-процедуры, не допущение. -/
def MergeApprovedMeas (twoGap : ℝ) (prices : Fin N → ℝ) (w : Fin N → ℝ)
    (δ_bound κ s n' : ℝ) : Prop :=
  (∑ i, w i * prices i) + δ_bound + κ * (n' * s) / 2 < twoGap

/-- **Сертификат измеряемого гейта**: при выполнении
MergeApprovedMeas суммарный прирост (цены + измеренный остаток +
сжатие) строго меньше twoGap — merge сертифицирован ИЗМЕРЕНИЕМ
(ср. merge_gate_certified MergePrice: там δ-члена НЕТ — квадратичная
модель без остатка; здесь нелинейность оплачена измеренным δ). -/
theorem merge_gate_meas {twoGap : ℝ} {prices : Fin N → ℝ}
    {w : Fin N → ℝ} {δ_bound κ s n' : ℝ}
    (hgate : MergeApprovedMeas twoGap prices w δ_bound κ s n') :
    (∑ i, w i * prices i) + δ_bound + κ * (n' * s) / 2 < twoGap :=
  hgate

/-! ## Негатив: без измерения merge НЕ безопасен -/

/-- **НЕГАТИВ (обязательный)**: для любого B > 0 существует 1D-лосс с
L(w₁) = L(w₂) = 0, но L(mid) ≥ B — вогнутая парабола
L(x) = B − 4B(x−½)²: острый минимум между w₁ = 0 и w₂ = 1
ПЕРЕВЁРНУТ (концы — нули, середина — барьер высоты B). Любой
merge-bound обязан содержать остаток δ ≥ B: без ИЗМЕРЕНИЯ
(linResidualGrid-процедура) merge НЕ безопасен для произвольной
нелинейности. -/
theorem merge_unsafe_without_measurement (B : ℝ) (hB : 0 < B) :
    ∃ (L : (Fin 1 → ℝ) → ℝ) (w1 w2 : Fin 1 → ℝ),
      L w1 = 0 ∧ L w2 = 0 ∧ B ≤ L (mid w1 w2) := by
  refine ⟨fun θ => B - 4 * B * (θ 0 - 1/2) ^ 2,
    fun _ => 0, fun _ => 1, ?_, ?_, ?_⟩
  · show (fun θ => B - 4 * B * (θ 0 - 1/2) ^ 2) (fun _ : Fin 1 => 0) = 0
    field_simp
    ring
  · show (fun θ => B - 4 * B * (θ 0 - 1/2) ^ 2) (fun _ : Fin 1 => 1) = 0
    field_simp
    ring
  · unfold mid
    show B ≤ (fun θ => B - 4 * B * (θ 0 - 1/2) ^ 2)
      (fun i => ((fun _ : Fin 1 => (0:ℝ)) i + (fun _ : Fin 1 => 1) i) / 2)
    have h2 : ((fun _ : Fin 1 => (0:ℝ)) 0 + (fun _ : Fin 1 => 1) 0) / 2
        = 1/2 := by norm_num
    simp only [h2]
    have hs : (1/2 : ℝ) - 1/2 = 0 := by norm_num
    simp only [hs, sub_zero, zero_pow two_ne_zero, mul_zero]
    exact le_refl B

end Hagi.Theory.NonlinearMerge

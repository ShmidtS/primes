/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.BlockLipschitz

/-!
# ProvenTrunk — первый ПОЛНОСТЬЮ доказанный LM-ствол (C470)

Дорожная карта C469 топ-1: первая языковая модель в корпусе, где
НИ ОДНА lip/causal-посылка не является полем — всё выведено из
атомов. Склейка трёх результатов:

* C436 `Hagi.Model.LMCompose`: `trunk_lipschitz` (Π Lᵢ индукция),
  `lm_logit_lipschitz`, `lm_probs_prefix_determined`;
* C450/C465 `Hagi.Theory.BlockLipschitz`: атомы с ВЫВЕДЕННЫМИ
  константами — `certifiedRMSNorm` (lip = 1 + G·(n+1)/ε),
  `certifiedMLP` (lip = 1 + √n·‖W₂‖_F·‖W₁‖_F), `certifiedConvAtt`
  (lip = 2), все с выведенными `hLip`/`hCausal`.

Trunk = [RMSNorm, MLP, ConvAtt] на одном носителе `V` (без
коэрсингов/мостов — типы атомов совпадают). Единственная выведенная
константа ствола:

  `trunkLip = (1 + G·(n+1)/ε) · (1 + √n·‖W₂‖_F·‖W₁‖_F) · 2`,
  n = `Fintype.card V`

— получается ПРИМЕНЕНИЕМ `trunk_lipschitz` (никакой новой
индукции), полная lip LM — применением `lm_logit_lipschitz`:
`headLip · trunkLip`. Каузальность всей LM — применением
`lm_probs_prefix_determined` (бесплатно из выведенных `hCausal`).

## Карта «что осталось посылкой»

НИ ОДНА структурная lip/causal-посылка не осталась полем. Остались
только ДАННЫЕ (веса и их границы, все — параметры уровня модуля):

- `g` + `G` (gain и его граница) и `ε > 0` — данные RMSNorm-атома;
- `W₁`, `W₂` — данные MLP-атома (входят в константу через
  Frobenius-нормы ‖W₁‖_F, ‖W₂‖_F);
- `headProj`, `headTheta` — данные головы (входят через `headLip`,
  ℓ1-нормы произведений шаблонов на параметры).

Численный witness (V = Fin 4, g = 1, G = 1, ε = 1, W₁ = W₂ = 1/2):
Frobenius² = 4 → ‖W‖_F = 2, `trunkLip = 6 · 9 · 2 = 108`
(`witness_trunkLip`, `#eval`-зеркало на ℚ ниже).

## Honest pins

- Константы derivable-but-not-tight (наследие атомов: Frobenius
  вместо op-norm, ℓ2→ℓ1 √n-мосты, sup-norm-оценка внимания);
  цель этой склейки — выводимость, не оптимальность.
- Веса остаются произвольными данными: statement доказан для ВСЕХ
  g/W₁/W₂/голов, константа — функция от них.
- `#eval` вычисляет рациональное зеркало формулы (вещественный
  `trunkLip` noncomputable — наследие корпуса); равенство = 108
  доказано theorem'ом `witness_trunkLip`, не только вычислено.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.ProvenTrunk

open scoped BigOperators NNReal

open Hagi.Model.LMCompose Hagi.Theory.BlockLipschitz

/-! ## Ствол из трёх атомов -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Список сертифицированных блоков-атомов: RMSNorm → MLP →
каузальное внимание. Все `hLip`/`hCausal` ВЫВЕДЕНЫ в
`Hagi.Theory.BlockLipschitz` (никаких полей-посылок). -/
noncomputable def provenBlocks (g : V → ℝ) (G : ℝ≥0) (ε : ℝ)
    (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ))
    (W₁ W₂ : V → V → ℝ) : List (CertifiedBlock V) :=
  [certifiedRMSNorm g G ε hε hg, certifiedMLP W₁ W₂,
   certifiedConvAtt (V := V)]

/-- ЕДИНСТВЕННАЯ выведенная константа ствола: произведение трёх
выведенных атомарных констант. n = `Fintype.card V`. -/
noncomputable def trunkLip (g : V → ℝ) (G : ℝ≥0) (ε : ℝ)
    (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ))
    (W₁ W₂ : V → V → ℝ) : ℝ :=
  (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
    * (1 + Real.sqrt ((Fintype.card V : ℝ))
        * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
        * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
    * 2

/-- `blocksLip` ствола из трёх атомов в точности равен `trunkLip`:
произведение per-block констант разворачивается в замкнутую формулу
(rfl-равенства атомарных lip + List-механика, никакой индукции). -/
theorem blocksLip_eq_trunkLip (g : V → ℝ) (G : ℝ≥0) (ε : ℝ)
    (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ)) (W₁ W₂ : V → V → ℝ) :
    (blocksLip (provenBlocks g G ε hε hg W₁ W₂) : ℝ)
      = trunkLip g G ε hε hg W₁ W₂ := by
  have hmap : (provenBlocks g G ε hε hg W₁ W₂).map (fun b => b.lip)
      = [(certifiedRMSNorm g G ε hε hg).lip,
         (certifiedMLP W₁ W₂).lip,
         (certifiedConvAtt (V := V)).lip] := rfl
  have hprod : (blocksLip (provenBlocks g G ε hε hg W₁ W₂) : ℝ)
      = ((certifiedRMSNorm g G ε hε hg).lip : ℝ)
        * ((certifiedMLP W₁ W₂).lip : ℝ)
        * ((certifiedConvAtt (V := V)).lip : ℝ) := by
    simp only [blocksLip, hmap, List.prod_cons, List.prod_nil,
      NNReal.coe_mul, mul_one, mul_assoc]
  have e1 : ((certifiedRMSNorm g G ε hε hg).lip : ℝ)
      = 1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε) := rfl
  have e2 : ((certifiedMLP W₁ W₂).lip : ℝ)
      = 1 + Real.sqrt ((Fintype.card V : ℝ))
          * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
          * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2) := rfl
  have e3 : ((certifiedConvAtt (V := V)).lip : ℝ) = 2 := rfl
  rw [hprod, e1, e2, e3]
  rfl

/-- Липшиц-ствол: trunk из трёх атомов `trunkLip`-Липшиц в
prefix-метрике — ПРИМЕНЕНИЕ `trunk_lipschitz` C436 с выведенными
константами атомов (новой индукции нет). -/
theorem provenTrunk_lip (g : V → ℝ) (G : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ v, |g v| ≤ (G : ℝ)) (W₁ W₂ : V → V → ℝ)
    (x y : ℕ → V → ℝ) (t : ℕ) :
    dPre (lmTrunk (provenBlocks g G ε hε hg W₁ W₂) x)
        (lmTrunk (provenBlocks g G ε hε hg W₁ W₂) y) t
      ≤ trunkLip g G ε hε hg W₁ W₂ * dPre x y t := by
  rw [← blocksLip_eq_trunkLip g G ε hε hg W₁ W₂]
  exact trunk_lipschitz (provenBlocks g G ε hε hg W₁ W₂) x y t

/-! ## Полная LM с доказанным стволом -/

variable {K : Type} [Fintype K] [Nonempty K] {d : ℕ}

/-- Конкретная LM: trunk = три атома (все посылки выведены),
билинейная certified-голова CEDescent. headProj/headTheta —
данные (веса головы), не посылки. -/
noncomputable def concreteLM (g : V → ℝ) (G : ℝ≥0) (ε : ℝ)
    (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ)) (W₁ W₂ : V → V → ℝ)
    (proj : K → Fin d → V → ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    LM V K d where
  blocks := provenBlocks g G ε hε hg W₁ W₂
  headProj := proj
  headTheta := θ

/-- Полная lip LM: |logit a(x) − logit a(y)| ≤ `headLip · trunkLip ·
dPre x y` — применение `lm_logit_lipschitz` C436; НИ ОДНОЙ
структурной посылки: обе константы выведены (голова — ℓ1-норма
данных, ствол — формула из атомов). -/
theorem proven_lm_lip (g : V → ℝ) (G : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ v, |g v| ≤ (G : ℝ)) (W₁ W₂ : V → V → ℝ)
    (proj : K → Fin d → V → ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (x y : ℕ → V → ℝ) (t : ℕ) (a : K) :
    |lmLogits (concreteLM g G ε hε hg W₁ W₂ proj θ) x t a
        - lmLogits (concreteLM g G ε hε hg W₁ W₂ proj θ) y t a|
      ≤ headLip (concreteLM g G ε hε hg W₁ W₂ proj θ) a
          * trunkLip g G ε hε hg W₁ W₂ * dPre x y t := by
  have hkey : (blocksLip (concreteLM g G ε hε hg W₁ W₂ proj θ).blocks : ℝ)
      = trunkLip g G ε hε hg W₁ W₂ :=
    blocksLip_eq_trunkLip g G ε hε hg W₁ W₂
  calc |lmLogits (concreteLM g G ε hε hg W₁ W₂ proj θ) x t a
          - lmLogits (concreteLM g G ε hε hg W₁ W₂ proj θ) y t a|
      ≤ headLip (concreteLM g G ε hε hg W₁ W₂ proj θ) a
          * (blocksLip
              (concreteLM g G ε hε hg W₁ W₂ proj θ).blocks : ℝ)
            * dPre x y t :=
            lm_logit_lipschitz _ x y t a
    _ = headLip (concreteLM g G ε hε hg W₁ W₂ proj θ) a
          * trunkLip g G ε hε hg W₁ W₂ * dPre x y t := by
            rw [hkey]

/-- Каузальность всей LM (бесплатно): выходное распределение
prefix-determined — применение `lm_probs_prefix_determined` C436 к
выведенным `hCausal` атомов. Нулевая утечка из будущего. -/
theorem proven_lm_probs_prefix_determined (g : V → ℝ) (G : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ))
    (W₁ W₂ : V → V → ℝ) (proj : K → Fin d → V → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) (a : K) :
    lmProbs (concreteLM g G ε hε hg W₁ W₂ proj θ) x t a
      = lmProbs (concreteLM g G ε hε hg W₁ W₂ proj θ) y t a :=
  lm_probs_prefix_determined _ x y t hagree a

/-! ## Численный witness: n = 4, Π = 108 -/

/-- Witness-данные: носитель Fin 4, gain 1, ε = 1, матрицы 1/2
(Frobenius² = 16·(1/4) = 4, ‖W‖_F = 2). -/
noncomputable def witnessG : Fin 4 → ℝ := fun _ => 1

/-- Матрицы 1/2 witness-модели. -/
noncomputable def witnessW : Fin 4 → Fin 4 → ℝ := fun _ _ => (2 : ℝ)⁻¹

/-- Граница gain witness-модели: |1| ≤ 1. -/
theorem witness_hg : ∀ v, |witnessG v| ≤ ((1 : ℝ≥0) : ℝ) := by
  intro v; simp [witnessG]

/-- Witness-константа: при n = 4, G = 1, ε = 1, W₁ = W₂ = 1/2
массивах выведенная константа ствола РАВНА 108 = 6·9·2:
(1 + 1·5/1)·(1 + 2·2·2)·2. -/
theorem witness_trunkLip :
    trunkLip (V := Fin 4) witnessG 1 1 (by norm_num) witness_hg
        witnessW witnessW
      = 108 := by
  have hcard : ((Fintype.card (Fin 4) : ℝ)) = 4 := by norm_num
  have hfrob : ∑ v : Fin 4, ∑ j : Fin 4, witnessW v j ^ 2 = 4 := by
    simp only [witnessW]; norm_num
  show (1 + (1 : ℝ) * (((Fintype.card (Fin 4) : ℝ) + 1) / 1))
      * (1 + Real.sqrt ((Fintype.card (Fin 4) : ℝ))
        * Real.sqrt (∑ v : Fin 4, ∑ j : Fin 4, witnessW v j ^ 2)
        * Real.sqrt (∑ j : Fin 4, ∑ k : Fin 4, witnessW j k ^ 2))
      * 2 = 108
  rw [hcard, hfrob]
  norm_num

-- `#eval`-зеркало witness-вычисления на ℚ (вещественный `trunkLip`
-- noncomputable): Frobenius²-слагаемые witness-матриц.
#eval (∑ v : Fin 4, ∑ j : Fin 4, ((2 : ℚ)⁻¹) ^ 2 : ℚ)

-- Итоговое Π witness-модели на ℚ: 6·9·2.
#eval ((1 + (1 : ℚ) * 5 / 1) * (1 + 2 * 2 * 2) * 2 : ℚ)

end Hagi.Theory.ProvenTrunk

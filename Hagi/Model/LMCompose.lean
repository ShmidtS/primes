/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEDescent
import Hagi.Model.Attention

/-!
# LMCompose — языковая модель как ФУНКЦИЯ: композиция блоков

В корпусе есть кост-модели внимания (GQA/MLA/Flash/SWA, `Hagi.Model.Attention`), алгебра RoPE и
каузальной свёртки (`Hagi.Step.CausalFilter`), но самой языковой модели
как функции «вход → распределение» НЕТ — глубочайшая обучаемая модель
линейно-логитная (`Hagi.Model.CEDescent`) с фиксированными признаками.
Этот модуль — композиция: LM = список transformer-блоков
(записей с полями-функциями) + certified-голова, `lmProbs : Input → Probs`,
с четырьмя доказанными свойствами:

* (a) Липшиц-композиция: `trunk_lipschitz` — если каждый блок
  `Lᵢ`-Липшиц в prefix-метрике `dPre` (per-block посылка), то trunk
  `∏Lᵢ`-Липшиц; `lm_logit_lipschitz` — логиты LM Липшиц с константой
  `headLip · ∏Lᵢ` (chain-механика `BlockSmooth`, но на
  последовательностном носителе ℕ → V → ℝ);
* (b) cost-мост: `lm_kv_cache_lt` — KV-компонента стоимости eval
  (сумма `gqaKVCost` по блокам) строго меньше full-MHA суммы, мост
  через `Hagi.Model.GQA.gqa_kv_lt` поэлементно;
* (c) каузальность: `trunk_prefix_determined` /
  `lm_logit_prefix_determined` / `lm_probs_prefix_determined` — если
  каждый блок prefix-determined (per-block посылка), то вся LM
  prefix-determined (индукция по блокам; паттерн
  `Hagi.Step.causal_prefix_determined`, без импорта: носители разные);
* (d) certified-голова: `lm_head_safeStep_lt` — при ФИКСИРОВАННОМ
  trunk (вход x, позиция t) безопасный шаг `ceNextParameters` /
  `safeStepSize` строго уменьшает CE LM — буквально
  `Hagi.Model.ceOneHot_safeStep_lt` на feature-матрице
  `lmFeatures m x t` (arbitrary trunk + certified head).

## Honest pins (что эта композиция НЕ покрывает)

- Посылки `hLip` / `hCausal` — per-block binders (`CertifiedBlock`);
  разрядка для конкретных attention-атомов (softmax-внимание,
  RoPE-позиционирование) — будущее. Для линейного атома константа
  выводима по образцу `linear_lipschitz_frobenius` (BlockSmooth);
  перенос ℓ2 → prefix-ℓ1 здесь не делается (YAGNI).
- Поле `attn` — упрощённый агрегатор над префиксом БЕЗ softmax-нормализации
  внутри блока; канонический softmax живёт в голове
  (`Hagi.Prelude.softDef`). RoPE не вложен (`rope_normSq_preserved` —
  `Hagi.Model.Attention`).
- Голова билинейная (`headProj` × `headTheta`, low-rank) — форма, к
  которой certified-step CEDescent применим напрямую; произвольная
  Matrix-голова потребует отдельного моста.
- `lmProbs` noncomputable (вещественный корпус); стоимость формализована
  только через KV-счётчики (b), полная FLOP-модель не делается.
-/

set_option relaxedAutoImplicit false

open scoped BigOperators Matrix NNReal

namespace Hagi.Model.LMCompose

/-! ## Dist-агрегат -/

/-- Prefix-ℓ1 расстояние между последовательностями скрытых
состояний: сумма |x i v − y i v| по позициям i ≤ t и координатам v. -/
def dPre {V : Type} [Fintype V] (x y : ℕ → V → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v|

/-- Один координатный член входит в `dPre` (на позиции i = t). -/
theorem coord_abs_le_dPre {V : Type} [Fintype V]
    (x y : ℕ → V → ℝ) (t : ℕ) (v : V) :
    |x t v - y t v| ≤ dPre x y t := by
  have h1 : |x t v - y t v|
      ≤ ∑ w : V, |x t w - y t w| :=
    Finset.single_le_sum (f := fun w => |x t w - y t w|)
      (fun w _ => abs_nonneg _) (Finset.mem_univ v)
  have h2 : (∑ w : V, |x t w - y t w|)
      ≤ ∑ i ∈ Finset.range (t + 1), ∑ w : V, |x i w - y i w| :=
    Finset.single_le_sum (f := fun i => ∑ w : V, |x i w - y i w|)
      (fun i _ =>
        Finset.sum_nonneg (fun w _ => abs_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self t))
  exact le_trans h1 h2

/-! ## Блок -/

/-- Transformer-блок как ЗАПИСЬ с полями-функциями: агрегатор
внимания над префиксом (упрощённо — линейный скоринг, softmax в
голове), норм-слой как функция, геометрия голов (nH запросных,
nKv KV-голов GQA, d — размерность). Residual — структурный
(`blockApply`). -/
structure TransformerBlock (V : Type) [Fintype V] where
  /-- Агрегатор внимания: читает последовательность и позицию. -/
  attn : (ℕ → V → ℝ) → ℕ → V → ℝ
  /-- Норм-слой: преобразование вектора скрытого состояния. -/
  norm : (V → ℝ) → V → ℝ
  /-- Число запросных голов. -/
  nH : ℕ
  /-- Число KV-голов (GQA-геометрия). -/
  nKv : ℕ
  /-- Размерность головы. -/
  d : ℕ

/-- Применение блока с residual: `x t + norm (attn x t)`
(координатно; первый блок списка применяется первым, см. `lmTrunk`). -/
def blockApply {V : Type} [Fintype V]
    (b : TransformerBlock V) (x : ℕ → V → ℝ) : ℕ → V → ℝ :=
  fun t v => x t v + b.norm (b.attn x t) v

/-- Сертифицированный блок: блок + per-block посылки. `hLip` —
блок `lip`-Липшиц в prefix-метрике (для линейного атома константа
выводима, см. pins модуля); `hCausal` — блок prefix-determined
(нулевой обмен с будущим, паттерн `causal_prefix_determined`). -/
structure CertifiedBlock (V : Type) [Fintype V] extends TransformerBlock V where
  /-- Per-block константа Липшица. -/
  lip : ℝ≥0
  /-- Prefix-Липшиц посылка на уровне агрегата `dPre`. -/
  hLip : ∀ x y : ℕ → V → ℝ, ∀ t : ℕ,
    dPre (blockApply toTransformerBlock x) (blockApply toTransformerBlock y) t
      ≤ (lip : ℝ) * dPre x y t
  /-- Prefix-determinedness посылка (поэлементно). -/
  hCausal : ∀ x y : ℕ → V → ℝ, ∀ t : ℕ,
    (∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) →
      ∀ v : V, blockApply toTransformerBlock x t v
        = blockApply toTransformerBlock y t v

/-! ## Trunk: композиция блоков -/

/-- Константа Липшица списка блоков — произведение per-block
констант. -/
def blocksLip {V : Type} [Fintype V] (bs : List (CertifiedBlock V)) : ℝ≥0 :=
  (bs.map fun b => b.lip).prod

/-- Композиция блоков: foldl по списку (первый блок применяется
первым). Это trunk LM — «arbitrary trunk». -/
def lmTrunk {V : Type} [Fintype V] (bs : List (CertifiedBlock V))
    (x : ℕ → V → ℝ) : ℕ → V → ℝ :=
  bs.foldl (fun acc b => blockApply b.toTransformerBlock acc) x

/-- (a, часть 1) Композиция Липшиц: если каждый блок `Lᵢ`-Липшиц в
prefix-метрике (per-block посылки `CertifiedBlock.hLip`), то trunk
`∏Lᵢ`-Липшиц. Индукция по списку блоков; константы перемножаются
(chain-правило в константной форме). -/
theorem trunk_lipschitz {V : Type} [Fintype V]
    (bs : List (CertifiedBlock V)) (x y : ℕ → V → ℝ) (t : ℕ) :
    dPre (lmTrunk bs x) (lmTrunk bs y) t
      ≤ (blocksLip bs : ℝ) * dPre x y t := by
  induction bs generalizing x y with
  | nil => simp [lmTrunk, blocksLip, one_mul]
  | cons b bs ih =>
      have hb := b.hLip x y t
      have hih := ih (blockApply b.toTransformerBlock x)
                    (blockApply b.toTransformerBlock y)
      have key : dPre (lmTrunk (b :: bs) x) (lmTrunk (b :: bs) y) t
          ≤ (blocksLip bs : ℝ) * ((b.lip : ℝ) * dPre x y t) := by
        rw [lmTrunk, lmTrunk, List.foldl_cons, List.foldl_cons]
        exact le_trans hih
          (mul_le_mul_of_nonneg_left hb (NNReal.coe_nonneg _))
      have hcoe : (blocksLip (b :: bs) : ℝ)
          = (b.lip : ℝ) * (blocksLip bs : ℝ) := by
        simp [blocksLip, NNReal.coe_mul]
      rw [hcoe]
      exact key.trans (le_of_eq (by ring))

/-- (c, часть 1) Композиция каузальна: если каждый блок
prefix-determined (per-block посылки `CertifiedBlock.hCausal`), то
trunk prefix-determined. Индукция по списку блоков: совпадение
префиксов входов переносится через каждый блок. -/
theorem trunk_prefix_determined {V : Type} [Fintype V]
    (bs : List (CertifiedBlock V)) (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) :
    ∀ v : V, lmTrunk bs x t v = lmTrunk bs y t v := by
  induction bs generalizing x y with
  | nil => simpa [lmTrunk] using fun v => hagree t (Nat.le_refl t) v
  | cons b bs ih =>
      have hstep : ∀ i : ℕ, i ≤ t → ∀ v : V,
          blockApply b.toTransformerBlock x i v
            = blockApply b.toTransformerBlock y i v :=
        fun i hi v => b.hCausal x y i
          (fun j hj vj => hagree j (Nat.le_trans hj hi) vj) v
      have hbase := hstep t (Nat.le_refl t)
      have hrest := ih (blockApply b.toTransformerBlock x)
                    (blockApply b.toTransformerBlock y) hstep
      intro v
      simp only [lmTrunk, List.foldl_cons]
      exact hrest v

/-! ## LM: trunk + certified-голова -/

variable {V : Type} [Fintype V] {K : Type} [Fintype K] [Nonempty K]
  {d : ℕ}

/-- Языковая модель: список сертифицированных блоков + билинейная
голова (шаблоны классов `headProj` × обучаемые параметры
`headTheta`; low-rank форма, к которой certified-step CEDescent
применим напрямую). Вход — последовательность скрытых состояний,
выход — распределение на словаре K (`lmProbs`). -/
structure LM (V : Type) [Fintype V] (K : Type) [Fintype K] (d : ℕ) where
  /-- Список transformer-блоков (первый применяется первым). -/
  blocks : List (CertifiedBlock V)
  /-- Шаблоны классов: строки признаков для каждого токена словаря. -/
  headProj : K → Fin d → V → ℝ
  /-- Обучаемые параметры головы (shared по словарю). -/
  headTheta : EuclideanSpace ℝ (Fin d)

/-- Feature-матрица головы после trunk: строка класса a — проекция
скрытого состояния токена t на шаблон a. При фиксированном входе x и
позиции t это в точности «фиксированные признаки» модели CEDescent. -/
noncomputable def lmFeatures (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) :
    Matrix K (Fin d) ℝ :=
  Matrix.of fun a j => ∑ v, m.headProj a j v * lmTrunk m.blocks x t v

/-- Логиты LM: certified-линейная голова CEDescent на признаках
trunk (`ceLogits lmFeatures headTheta`). -/
noncomputable def lmLogits (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) :
    K → ℝ :=
  Hagi.Model.ceLogits (lmFeatures m x t) m.headTheta

/-- Выход LM: распределение на словаре — канонический softmax
`Hagi.Prelude.softDef` на логитах. Это eval : Input → Probs. -/
noncomputable def lmProbs (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) :
    K → ℝ :=
  Hagi.Prelude.softDef (lmLogits m x t)

omit [Nonempty K] in
/-- Раскрытие логита: строка feature-матрицы скалярно умножается на
параметры головы. -/
theorem lmLogits_eq_sum (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ) (a : K) :
    lmLogits m x t a
      = ∑ j, ∑ v, m.headProj a j v * lmTrunk m.blocks x t v
          * m.headTheta.ofLp j := by
  simp [lmLogits, lmFeatures, Hagi.Model.ceLogits, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Finset.sum_mul]

/-- Константа Липшица головы для класса a: ℓ1-норма произведения
шаблона на параметры. -/
noncomputable def headLip (m : LM V K d) (a : K) : ℝ :=
  ∑ j, ∑ v, |m.headProj a j v * m.headTheta.ofLp j|

omit [Nonempty K] in
/-- (a, часть 2) Логиты LM Липшиц: |logit a на x − logit a на y| ≤
`headLip · ∏Lᵢ · dPre x y` — голова ℓ1-Липшиц по скрытому состоянию
(`headLip`), trunk `∏Lᵢ`-Липшиц (`trunk_lipschitz`); итоговая
константа композиции есть произведение. -/
theorem lm_logit_lipschitz (m : LM V K d) (x y : ℕ → V → ℝ) (t : ℕ)
    (a : K) :
    |lmLogits m x t a - lmLogits m y t a|
      ≤ headLip m a * (blocksLip m.blocks : ℝ) * dPre x y t := by
  have hD : ∀ v : V,
      |lmTrunk m.blocks x t v - lmTrunk m.blocks y t v|
        ≤ dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t :=
    fun v => coord_abs_le_dPre _ _ _ v
  have htrunk := trunk_lipschitz m.blocks x y t
  have hS : (0:ℝ) ≤ ∑ j, ∑ v, |m.headProj a j v * m.headTheta.ofLp j| := by
    positivity
  have hpair : ∀ j : Fin d,
      (∑ v, m.headProj a j v * lmTrunk m.blocks x t v
          * m.headTheta.ofLp j)
        - (∑ v, m.headProj a j v * lmTrunk m.blocks y t v
          * m.headTheta.ofLp j)
      = ∑ v, m.headProj a j v
          * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
          * m.headTheta.ofLp j := by
    intro j
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hterm : ∀ j : Fin d, ∀ v : V,
      |m.headProj a j v
          * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
          * m.headTheta.ofLp j|
      ≤ |m.headProj a j v * m.headTheta.ofLp j|
          * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t := by
    intro j v
    have habs : |m.headProj a j v
          * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
          * m.headTheta.ofLp j|
        = |m.headProj a j v * m.headTheta.ofLp j|
          * |lmTrunk m.blocks x t v - lmTrunk m.blocks y t v| := by
      rw [abs_mul, abs_mul, abs_mul]
      ring
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hD v) (abs_nonneg _)
  have hrow : ∀ j : Fin d,
      |(∑ v, m.headProj a j v * lmTrunk m.blocks x t v
          * m.headTheta.ofLp j)
        - (∑ v, m.headProj a j v * lmTrunk m.blocks y t v
          * m.headTheta.ofLp j)|
      ≤ (∑ v, |m.headProj a j v * m.headTheta.ofLp j|)
          * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t := by
    intro j
    have hB := Finset.abs_sum_le_sum_abs
      (fun v : V => m.headProj a j v
        * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
        * m.headTheta.ofLp j) Finset.univ
    rw [hpair j]
    calc |∑ v, m.headProj a j v
            * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
            * m.headTheta.ofLp j|
        ≤ ∑ v, |m.headProj a j v
            * (lmTrunk m.blocks x t v - lmTrunk m.blocks y t v)
            * m.headTheta.ofLp j| := hB
      _ ≤ ∑ v, |m.headProj a j v * m.headTheta.ofLp j|
            * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t :=
          Finset.sum_le_sum (fun v _ => hterm j v)
      _ = (∑ v, |m.headProj a j v * m.headTheta.ofLp j|)
            * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t :=
          (Finset.sum_mul _ _ _).symm
  have hA := Finset.abs_sum_le_sum_abs
    (fun j : Fin d =>
      (∑ v, m.headProj a j v * lmTrunk m.blocks x t v
        * m.headTheta.ofLp j)
      - (∑ v, m.headProj a j v * lmTrunk m.blocks y t v
        * m.headTheta.ofLp j)) Finset.univ
  rw [lmLogits_eq_sum, lmLogits_eq_sum, ← Finset.sum_sub_distrib]
  calc |∑ j, ((∑ v, m.headProj a j v * lmTrunk m.blocks x t v
        * m.headTheta.ofLp j)
        - (∑ v, m.headProj a j v * lmTrunk m.blocks y t v
          * m.headTheta.ofLp j))|
      ≤ ∑ j, |((∑ v, m.headProj a j v * lmTrunk m.blocks x t v
          * m.headTheta.ofLp j)
        - (∑ v, m.headProj a j v * lmTrunk m.blocks y t v
          * m.headTheta.ofLp j))| := hA
    _ ≤ ∑ j, (∑ v, |m.headProj a j v * m.headTheta.ofLp j|)
          * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t :=
          Finset.sum_le_sum (fun j _ => hrow j)
    _ = (∑ j, ∑ v, |m.headProj a j v * m.headTheta.ofLp j|)
          * dPre (lmTrunk m.blocks x) (lmTrunk m.blocks y) t :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, ∑ v, |m.headProj a j v * m.headTheta.ofLp j|)
          * ((blocksLip m.blocks : ℝ) * dPre x y t) :=
          mul_le_mul_of_nonneg_left htrunk hS
    _ = headLip m a * (blocksLip m.blocks : ℝ) * dPre x y t := by
          unfold headLip
          ring

/-! ## (b) Cost-мост: KV-кэш -/

/-- KV-компонента стоимости eval LM: сумма GQA KV-стоимостей
блоков (`gqaKVCost` на per-block геометрии nKv, d). -/
def lmKVCost (m : LM V K d) (T : ℕ) : ℕ :=
  (m.blocks.map fun b =>
    Hagi.Model.GQA.gqaKVCost T b.toTransformerBlock.nKv
      b.toTransformerBlock.d).sum

/-- Full-MHA baseline той же стоимости: сумма `mhaKVCost`. -/
def lmKVCostFull (m : LM V K d) (T : ℕ) : ℕ :=
  (m.blocks.map fun b =>
    Hagi.Model.GQA.mhaKVCost T b.toTransformerBlock.nH
      b.toTransformerBlock.d).sum

omit [Nonempty K] in
/-- (b) Cost-мост: если LM непуста и каждый блок имеет GQA-геометрию
nKv < nH, то KV-компонента стоимости eval LM строго меньше
full-MHA baseline — `gqa_kv_lt` поэлементно (`List.sum_le_sum` +
один строгий член непустого списка). -/
theorem lm_kv_cache_lt (m : LM V K d) (T : ℕ)
    (hT : 1 ≤ T) (hne : m.blocks ≠ [])
    (hlt : ∀ b ∈ m.blocks,
      b.toTransformerBlock.nKv < b.toTransformerBlock.nH)
    (hd : ∀ b ∈ m.blocks,
      1 ≤ b.toTransformerBlock.d) :
    lmKVCost m T < lmKVCostFull m T := by
  have hlt' : ∀ b ∈ m.blocks,
      Hagi.Model.GQA.gqaKVCost T b.toTransformerBlock.nKv
        b.toTransformerBlock.d
        < Hagi.Model.GQA.mhaKVCost T b.toTransformerBlock.nH
          b.toTransformerBlock.d := fun b hb =>
    Hagi.Model.GQA.gqa_kv_lt T b.toTransformerBlock.nH
      b.toTransformerBlock.nKv b.toTransformerBlock.d
      (hlt b hb) hT (hd b hb)
  obtain ⟨b, bs, hbl⟩ := List.exists_cons_of_ne_nil hne
  have hbmem : b ∈ m.blocks := hbl ▸ List.mem_cons_self ..
  have := List.sum_lt_sum (l := m.blocks)
    (f := fun b => Hagi.Model.GQA.gqaKVCost T
      b.toTransformerBlock.nKv b.toTransformerBlock.d)
    (g := fun b => Hagi.Model.GQA.mhaKVCost T
      b.toTransformerBlock.nH b.toTransformerBlock.d)
    (fun b' hb' => (hlt' b' hb').le)
    ⟨b, hbmem, hlt' b hbmem⟩
  simpa [lmKVCost, lmKVCostFull] using this

/-! ## (c) Каузальность LM -/

omit [Nonempty K] in
/-- (c, часть 2) Логиты LM prefix-determined: если входы совпадают
на префиксе 0..t и каждый блок prefix-determined, то логиты на
позиции t совпадают (trunk-равенство + детерминизм головы). -/
theorem lm_logit_prefix_determined (m : LM V K d)
    (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) (a : K) :
    lmLogits m x t a = lmLogits m y t a := by
  have ht : lmTrunk m.blocks x t = lmTrunk m.blocks y t :=
    funext (trunk_prefix_determined m.blocks x y t hagree)
  simp [lmLogits, lmFeatures, ht]

omit [Nonempty K] in
/-- (c, часть 3) Выход LM prefix-determined: распределения на
позиции t совпадают — нулевая утечка из будущего для всей
композиции (softmax детерминирован). -/
theorem lm_probs_prefix_determined (m : LM V K d)
    (x y : ℕ → V → ℝ) (t : ℕ)
    (hagree : ∀ i : ℕ, i ≤ t → ∀ v : V, x i v = y i v) (a : K) :
    lmProbs m x t a = lmProbs m y t a := by
  unfold lmProbs
  congr 1
  exact funext fun a => lm_logit_prefix_determined m x y t hagree a

/-! ## (d) Certified-голова при фиксированном trunk -/

/-- Обновление параметров головы certified safe-step'ом CEDescent
при фиксированном trunk (вход x, позиция t, цель tgt): признаки
`lmFeatures m x t` не меняются, обновляются только `headTheta`. -/
noncomputable def lmHeadUpdate (m : LM V K d) (x : ℕ → V → ℝ)
    (t : ℕ) (tgt : K) : LM V K d where
  blocks := m.blocks
  headProj := m.headProj
  headTheta := Hagi.Model.ceNextParameters (lmFeatures m x t)
    m.headTheta tgt
    (Hagi.Model.safeStepSize (lmFeatures m x t) m.headTheta tgt)

/-- (d) Certified-голова: при ФИКСИРОВАННОМ trunk (вход x, позиция
t) безопасный шаг `ceNextParameters` / `safeStepSize` строго
уменьшает one-hot CE LM — буквально `ceOneHot_safeStep_lt` на
признаках trunk. Trunk произволен (arbitrary trunk + certified
head): его влияние входит только через фиксированную
feature-матрицу. -/
theorem lm_head_safeStep_lt (m : LM V K d) (x : ℕ → V → ℝ) (t : ℕ)
    (tgt : K)
    (hr : 0 < Hagi.Model.ceStepRange (lmFeatures m x t)
      m.headTheta tgt) :
    Hagi.ceOneHot tgt
        (lmLogits (lmHeadUpdate m x t tgt) x t)
      < Hagi.ceOneHot tgt (lmLogits m x t) := by
  have hf : lmFeatures (lmHeadUpdate m x t tgt) x t
      = lmFeatures m x t := by
    simp [lmFeatures, lmHeadUpdate]
  show Hagi.ceOneHot tgt
      (Hagi.Model.ceLogits (lmFeatures (lmHeadUpdate m x t tgt) x t)
        (lmHeadUpdate m x t tgt).headTheta)
    < Hagi.ceOneHot tgt
      (Hagi.Model.ceLogits (lmFeatures m x t) m.headTheta)
  rw [hf]
  exact Hagi.Model.ceOneHot_safeStep_lt (lmFeatures m x t)
    m.headTheta tgt hr

end Hagi.Model.LMCompose

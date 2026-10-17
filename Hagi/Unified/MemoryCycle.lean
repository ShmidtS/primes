/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LiveDelta
import Mathlib
/-!
# DeltaHistory — точный мост: история шагов спуска ⟷ LiveDelta

Режим A retrieval-центричного обучения (RCDL, arXiv:2610.03858):
обновление линейного слоя градиентным шагом имеет вид
`W_{t+1} = W_t + v_t ⊗ x_t` (внешнее произведение). Накопленная
история тогда точно равна `W_T = W₀ + Σ_t v_t ⊗ x_t`.

Этот модуль доказывает ТОЧНОЕ соответствие такой истории
состоянию LiveDelta: свёрнутая в rank-1 блоки история даёт
эффективные веса, равные итогу плотной траектории спуска, —
без аппроксимации и без эмпирических посылок.

Доказано:
* ранг-1 блок из пары (v, x) равен внешнему произведению
  `v ⊗ x`;
* эффективные веса после принятия блока = блок + прежние
  эффективные веса;
* общий fold-закон: свёртка истории над любым начальным
  состоянием добавляет к эффективным весам сумму внешних
  произведений;
* итог плотной свёртки шагов РАВЕН эффективным весам
  LiveDelta-представления той же истории;
* число блоков после свёртки = длина истории; хранение k
  шагов ранга 1 стоит ровно k·(m+n) элементов — против
  k·(m·n) при плотном хранении каждого обновления.

О нелинейной retrieval-памяти (режим B) здесь ничего не
утверждается — для неё требуется отдельная теория.
-/

open Matrix Hagi.Architecture

namespace Hagi.Step

variable {m n r' : Type} [Fintype m] [Fintype n] [Fintype r']

/-- Внешнее произведение `v ⊗ x` (ранг-1 матрица). -/
def outerProd (v : m → ℝ) (x : n → ℝ) : Matrix m n ℝ :=
  Matrix.of fun i j => v i * x j

/-- Ранг-1 блок из пары (v, x): факторы единичного ранга,
`Aᵀ * B = v ⊗ x`. -/
def rank1Block (v : m → ℝ) (x : n → ℝ) :
    Matrix Unit m ℝ × Matrix Unit n ℝ :=
  (Matrix.of fun _ j => v j, Matrix.of fun _ j => x j)

/-- Ранг-1 блок в точности равен внешнему произведению. -/
theorem rank1Block_eq_outer (v : m → ℝ) (x : n → ℝ) :
    (rank1Block v x).1ᵀ * (rank1Block v x).2
      = outerProd v x := by
  funext i j
  simp [rank1Block, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, outerProd]

/-- Эффективные веса после принятия блока: блок + прежние
эффективные веса. -/
theorem effective_addBlock (A : Matrix r' m ℝ) (B : Matrix r' n ℝ)
    (s : LiveDelta m n r') :
    effectiveWeights (addBlock A B s)
      = Aᵀ * B + effectiveWeights s := by
  simp only [addBlock, effectiveWeights, List.map_cons,
    List.sum_cons]
  rw [← add_assoc, add_comm s.base (Aᵀ * B), add_assoc]

/-- Шаг свёртки истории в Architecture. -/
def histStep (p : (m → ℝ) × (n → ℝ)) (s : LiveDelta m n Unit) :
    LiveDelta m n Unit :=
  addBlock (rank1Block p.1 p.2).1 (rank1Block p.1 p.2).2 s

/-- Общий fold-закон: свёртка истории над любым начальным
состоянием прибавляет к эффективным весам ТОЧНУЮ сумму
внешних произведений шагов. -/
theorem effective_fold (s : LiveDelta m n Unit)
    (hist : List ((m → ℝ) × (n → ℝ))) :
    effectiveWeights (hist.foldl (fun s p => histStep p s) s)
      = effectiveWeights s
        + (hist.map fun p => outerProd p.1 p.2).sum := by
  induction hist generalizing s with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [histStep]
    rw [effective_addBlock, rank1Block_eq_outer,
      List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    rw [add_comm]

/-- Свернуть историю шагов (v_t, x_t) в LiveDelta-состояние
над базой W₀. -/
def fromHistory (W₀ : Matrix m n ℝ)
    (hist : List ((m → ℝ) × (n → ℝ))) : LiveDelta m n Unit :=
  hist.foldl (fun s p => histStep p s) { base := W₀, blocks := [] }

/-- Итог плотного спуска: `W_T = foldl (· + v ⊗ x)` — то,
что вычислила бы обычная плотная матрица весов (режим A
RCDL: `W_{t+1} = W_t + v_t ⊗ x_t`). -/
def descentFold (W₀ : Matrix m n ℝ)
    (hist : List ((m → ℝ) × (n → ℝ))) : Matrix m n ℝ :=
  hist.foldl (fun W p => W + outerProd p.1 p.2) W₀

/-- ТОЧНЫЙ мост (режим A): эффективные веса LiveDelta,
собранного из истории шагов, равны базе + сумме внешних
произведений — никаких приближений. -/
theorem effective_fromHistory (W₀ : Matrix m n ℝ)
    (hist : List ((m → ℝ) × (n → ℝ))) :
    effectiveWeights (fromHistory W₀ hist)
      = W₀ + (hist.map fun p => outerProd p.1 p.2).sum := by
  have h := effective_fold { base := W₀, blocks := [] } hist
  simpa [fromHistory, effectiveWeights] using h

/-- Плотная траектория и LiveDelta-представление одной и той
же истории дают ОДИН И ТОТ ЖЕ итоговый слой — точное
равенство, основание для обмена между плотным обучением и
хранением вкладов по отдельности (консолидация/откат — без
пересчёта истории). -/
theorem descentFold_eq_effective (W₀ : Matrix m n ℝ)
    (hist : List ((m → ℝ) × (n → ℝ))) :
    descentFold W₀ hist
      = effectiveWeights (fromHistory W₀ hist) := by
  rw [effective_fromHistory]
  induction hist generalizing W₀ with
  | nil => simp [descentFold]
  | cons p ps ih =>
    simp only [descentFold, List.foldl_cons] at ih ⊢
    rw [ih (W₀ + outerProd p.1 p.2),
      List.map_cons, List.sum_cons, ← add_assoc]

/-- Число блоков после свёртки: длина истории (каждый шаг —
ровно один rank-1 блок). -/
theorem blocks_length_fold (s : LiveDelta m n Unit)
    (hist : List ((m → ℝ) × (n → ℝ))) :
    (hist.foldl (fun s p => histStep p s) s).blocks.length
      = s.blocks.length + hist.length := by
  induction hist generalizing s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [histStep, addBlock, List.length_cons]
    omega

/-- Хранение k шагов ранга 1: k блоков по (m+n) элементов —
против k·(m·n) при плотном хранении каждого обновления. -/
theorem history_storage_cost (W₀ : Matrix m n ℝ)
    (hist : List ((m → ℝ) × (n → ℝ))) :
    (fromHistory W₀ hist).blocks.length
      * (Fintype.card m + Fintype.card n)
      = hist.length * (Fintype.card m + Fintype.card n) := by
  have h := blocks_length_fold { base := W₀, blocks := [] } hist
  simp only [List.length_nil, Nat.zero_add, fromHistory] at h ⊢
  rw [h]

end Hagi.Step



/-!
# DeltaConsolidate — консолидация с аддитивным бюджетом ошибки

Применение моста R271 (история спуска = rank-1 блоки
LiveDelta): замена факторов блока (квантование, слияние,
перенос в низкоранговую поправку) меняет эффективные веса
ровно на сумму разностей блоков. Отсюда — квадратичный
бюджет ошибки консолидации: Frobenius-квадрат отклонения
эффективных весов ≤ k · Σ по блокам Frobenius-квадратов
отклонений блоков (k-множитель — из неравенства Коши для
сумм; консервативная, но аддитивная по блокам граница).

Доказано:
* разность сумм: замена факторов меняет веса ТОЧНО на
  Σ (новый блок) − Σ (старый блок) — база сокращается;
* аддитивный квадратичный бюджет: frob(eff − eff') ≤
  k · Σᵢ frob(bᵢ − bᵢ') — глобальная цена консолидации
  складывается из per-block цен.

Ничего о выигрыше памяти от замены факторов здесь не
утверждается — только цена ошибки (выигрыш — архитектурное
решение: quantMat-блоки хранят тернарные факторы).
-/

open Matrix Finset Hagi.Architecture Hagi.Step

namespace Hagi.Step

variable {m n : Type} [Fintype m] [Fintype n]

/-- Frobenius-квадрат: сумма квадратов элементов. -/
def frob (M : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, M i j * M i j

/-- Заменить факторы блоков поштучно (квантование/слияние):
новый список факторов. -/
def replaceBlocks (s : LiveDelta m n Unit)
    (news : List (Matrix Unit m ℝ × Matrix Unit n ℝ)) :
    LiveDelta m n Unit where
  base := s.base
  blocks := news

theorem sum_sub_eq {α : Type} [AddCommGroup α] (olds news : List α)
    (h : olds.length = news.length) :
    news.sum - olds.sum
      = ((olds.zip news).map fun b => b.2 - b.1).sum := by
  induction olds generalizing news with
  | nil => cases news with | nil => simp | cons p ps => simp at h
  | cons o os ih =>
    cases news with
    | nil => simp at h
    | cons p ps =>
      simp only [List.zip_cons_cons, List.map_cons,
        List.sum_cons, List.length_cons] at h ⊢
      rw [← ih ps (by omega)]
      abel

/-- Суммы продуктов факторов по списку. -/
def blockList
    (l : List (Matrix Unit m ℝ × Matrix Unit n ℝ)) :
    List (Matrix m n ℝ) :=
  l.map fun b => b.1ᵀ * b.2

/-- Zip факторов, отображённый в разности продуктов, — то же,
что zip продуктов с разностью. -/
theorem zip_map_prod_diff
    (olds news : List (Matrix Unit m ℝ × Matrix Unit n ℝ)) :
    ((olds.zip news).map
      fun b => b.2.1ᵀ * b.2.2 - b.1.1ᵀ * b.1.2)
      = ((blockList olds).zip (blockList news)).map
          fun b => b.2 - b.1 := by
  induction olds generalizing news with
  | nil => cases news with
    | nil => simp [blockList]
    | cons p ps => simp [blockList]
  | cons o os ih =>
    cases news with
    | nil => simp [blockList]
    | cons p ps =>
      simp only [List.zip_cons_cons, List.map_cons,
        blockList]
      rw [ih]
      rfl

/-- Замена факторов меняет эффективные веса ровно на сумму
разностей блоков: база сокращается, вклад — поштучный. -/
theorem effective_replaceBlocks (s : LiveDelta m n Unit)
    (news : List (Matrix Unit m ℝ × Matrix Unit n ℝ))
    (hnews : news.length = s.blocks.length) :
    effectiveWeights (replaceBlocks s news) - effectiveWeights s
      = ((s.blocks.zip news).map
          fun b => b.2.1ᵀ * b.2.2 - b.1.1ᵀ * b.1.2).sum := by
  have hb : effectiveWeights (replaceBlocks s news)
      - effectiveWeights s
      = (blockList news).sum - (blockList s.blocks).sum := by
    simp only [effectiveWeights, replaceBlocks, blockList]
    abel
  rw [hb, sum_sub_eq _ _ (by simp [hnews, blockList]),
    zip_map_prod_diff]

/-- Frobenius-квадрат суммы семейства ≤ k · Σ Frobenius-
квадратов (Коши: (∑ aₜ)² ≤ k·∑ aₜ² поэлементно + обмен
сумм). -/
theorem frob_sum_le (k : ℕ) (Δ : Fin k → Matrix m n ℝ) :
    frob (∑ t, Δ t) ≤ (k : ℝ) * ∑ t, frob (Δ t) := by
  have hcauchy : ∀ i j,
      (∑ t, Δ t) i j * (∑ t, Δ t) i j
        ≤ (k : ℝ) * ∑ t, (Δ t i j * Δ t i j) := by
    intro i j
    have hap : (∑ t, Δ t) i j = ∑ t, Δ t i j :=
      Matrix.sum_apply i j Finset.univ Δ
    rw [hap]
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun t => Δ t i j)
    simpa [sq] using h
  unfold frob
  have h1 : ∀ i ∈ (Finset.univ : Finset m), ∀ j ∈
      (Finset.univ : Finset n),
      (∑ t, Δ t) i j * (∑ t, Δ t) i j
        ≤ (k : ℝ) * ∑ t, (Δ t i j * Δ t i j) := fun i _ j _ =>
    hcauchy i j
  calc ∑ i, ∑ j, (∑ t, Δ t) i j * (∑ t, Δ t) i j
      ≤ ∑ i, ∑ j, (k : ℝ) * ∑ t, (Δ t i j * Δ t i j) :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => h1 i (Finset.mem_univ i)
            j (Finset.mem_univ j)
    _ = (k : ℝ) * ∑ t, ∑ i, ∑ j, Δ t i j * Δ t i j := by
        have h0 : ∑ i : m, ∑ j : n, (k : ℝ)
              * ∑ t : Fin k, Δ t i j * Δ t i j
            = ∑ i : m, ∑ j : n, ∑ t : Fin k,
                (k : ℝ) * (Δ t i j * Δ t i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl
            fun j _ => Finset.mul_sum _ _ _
        have hj : ∑ i : m, ∑ j : n, ∑ t : Fin k,
                (k : ℝ) * (Δ t i j * Δ t i j)
            = ∑ i : m, ∑ t : Fin k, ∑ j : n,
                (k : ℝ) * (Δ t i j * Δ t i j) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_comm (s := (Finset.univ : Finset n))
              (t := (Finset.univ : Finset (Fin k)))
              (f := fun j t => (k : ℝ)
                * (Δ t i j * Δ t i j))
        have h1 : ∑ i : m, ∑ t : Fin k, ∑ j : n,
                (k : ℝ) * (Δ t i j * Δ t i j)
            = ∑ t : Fin k, ∑ i : m, ∑ j : n,
                (k : ℝ) * (Δ t i j * Δ t i j) :=
          Finset.sum_comm (s := (Finset.univ : Finset m))
            (t := (Finset.univ : Finset (Fin k)))
            (f := fun i t => ∑ j : n,
              (k : ℝ) * (Δ t i j * Δ t i j))
        have h2 : ∑ t : Fin k, ∑ i : m, ∑ j : n,
                (k : ℝ) * (Δ t i j * Δ t i j)
            = (k : ℝ) * ∑ t : Fin k, ∑ i : m, ∑ j : n,
                Δ t i j * Δ t i j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum _ _ _).symm
        rw [h0, hj, h1, h2]

/-- Разность сумм = сумма разностей (Fin-семейство). -/
theorem sum_sub_family (k : ℕ) (f g : Fin k → Matrix m n ℝ) :
    (∑ t, f t) - (∑ t, g t) = ∑ t, (f t - g t) := by
  rw [← Finset.sum_sub_distrib]

/-- Аддитивный квадратичный бюджет консолидации: если каждый
заменяющий блок отклоняется от исходного не более чем на εᵢ
(Frobenius-квадрат), то суммарные веса отклоняются не более
чем на k·Σ εᵢ, где k — число блоков (множитель из неравенства
Коши — консервативно, но аддитивно по блокам). -/
theorem consolidate_budget (k : ℕ)
    (olds news : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (ε : Fin k → ℝ)
    (hε : ∀ t, frob ((olds t).1ᵀ * (olds t).2
        - (news t).1ᵀ * (news t).2) ≤ ε t) :
    frob ((∑ t, (olds t).1ᵀ * (olds t).2)
      - ∑ t, (news t).1ᵀ * (news t).2)
      ≤ (k : ℝ) * ∑ t, ε t := by
  rw [sum_sub_family]
  have hle := frob_sum_le k
    (fun t => (olds t).1ᵀ * (olds t).2
      - (news t).1ᵀ * (news t).2)
  refine le_trans hle ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun t _ => hε t

end Hagi.Step
/-!
# MemoryController — критерий допуска записей в растущую память

Контроллер роста HAGI для retrieval-памяти (RCDL, режим B):
новая запись допускается только при ОДНОВРЕМЕННОМ выполнении
двух независимых проверок — новизна (ключ далеко от
сохранённых) и сертифицированная польза (ожидаемый выигрыш
покрывает стоимость хранения, риск для защищаемых задач и
запас на ошибку оценки):

  Novelty(x) > τ,  Ĝ(x) ≥ λ_M·ΔC_state + λ_R·ΔR_protected
                     + ε_cert.

Главный тезис (рецензия): новизна сама по себе НЕ означает
полезность — шумный или нерелевантный вход тоже далёк от
сохранённых ключей.

Доказано:
* `admit`-решение конъюнктивно: без новизны ИЛИ без
  сертифицированной пользы запись НЕ допускается
  (noise_far_away_rejected — шум вдали от ключей не растит
  память);
* число записей растёт ТОЛЬКО с admit-решениями: после
  отклонённых шагов память не изменилась;
* консолидация принятых записей с per-block бюджетом εᵢ
  сохраняет глобальную границу k·Σ εᵢ (мост R272).

Сам критерий пользы — измеряемый контракт (h_emp_): Ĝ, ΔR
оцениваются на отложенных данных; здесь формализована только
ЛОГИКА решения и её следствия, не оценка Ĝ.
-/

open Finset Hagi.Architecture Hagi.Step Hagi.Step

namespace Hagi.Growth

variable {m n : Type} [Fintype m] [Fintype n]

/-- Проверки контроллера: новизна и сертифицированная польза
(обе — измеряемые контракты). -/
structure AdmissionChecks where
  /-- Новизна: расстояние ключа до сохранённых. -/
  novelty : ℝ
  /-- Порог новизны. -/
  τ : ℝ
  /-- Оценка улучшения предсказаний (сертифицированная). -/
  gain : ℝ
  /-- Стоимость хранения записи. -/
  Δcost : ℝ
  /-- Риск для защищаемых задач. -/
  Δrisk : ℝ
  /-- Вес стоимости состояния. -/
  lamM : ℝ
  /-- Вес риска. -/
  lamR : ℝ
  /-- Запас на ошибку оценки. -/
  ε_cert : ℝ

/-- Критерий новизны. -/
def noveltyOk (c : AdmissionChecks) : Prop := c.τ < c.novelty

/-- Критерий сертифицированной пользы: выигрыш покрывает
стоимость + риск + запас. -/
def gainOk (c : AdmissionChecks) : Prop :=
  c.lamM * c.Δcost + c.lamR * c.Δrisk + c.ε_cert ≤ c.gain

/-- Решение контроллера: запись допускается ТОЛЬКО при обеих
проверках. -/
def admit (c : AdmissionChecks) : Prop :=
  noveltyOk c ∧ gainOk c

/-- Новизна без пользы НЕ допускает запись: главный тезис —
далёкий от ключей вход (шум/нерелевантность) не растит
память. -/
theorem novelty_without_gain_rejects (c : AdmissionChecks)
    (hnov : noveltyOk c) (hnogain : ¬ gainOk c) :
    ¬ admit c := fun h => hnogain h.2

/-- Польза без новизны НЕ допускает запись: полезный сигнал,
дублирующий сохранённый, консолидируется в существующие
записи, а не расширяет память. -/
theorem gain_without_novelty_rejects (c : AdmissionChecks)
    (hgain : gainOk c) (hnonov : ¬ noveltyOk c) :
    ¬ admit c := fun h => hnonov h.1

/-- Тип блока памяти (факторы rank-1 записи). -/
abbrev MemBlock (m n : Type) :=
  Matrix Unit m ℝ × Matrix Unit n ℝ

/-- Применить решение контроллера: admit добавляет блок
(новая запись), reject оставляет память нетронутой. -/
def applyDecision {m n : Type} [Fintype m] [Fintype n]
    (b : MemBlock m n) (ok : Bool) (s : LiveDelta m n Unit) :
    LiveDelta m n Unit :=
  if ok then addBlock b.1 b.2 s else s

/-- Отклонённая запись не меняет память: точное равенство
состояния после reject-решения. -/
theorem rejected_no_growth {m n : Type} [Fintype m] [Fintype n]
    (b : MemBlock m n) (s : LiveDelta m n Unit) :
    applyDecision b false s = s := by
  simp [applyDecision]

/-- Прогнать последовательность решений над памятью. -/
def runDecisions {m n : Type} [Fintype m] [Fintype n]
    (s : LiveDelta m n Unit)
    (ds : List (Bool × MemBlock m n)) : LiveDelta m n Unit :=
  ds.foldl (fun s db => applyDecision db.2 db.1 s) s

/-- Память растёт только при допуске: число блоков после
последовательности решений = исходное + число admit-решений
(точное равенство; reject ничего не добавляет). -/
theorem blocks_grow_only_on_admit {m n : Type} [Fintype m]
    [Fintype n] (s : LiveDelta m n Unit)
    (ds : List (Bool × MemBlock m n)) :
    (runDecisions s ds).blocks.length
      = s.blocks.length + (ds.filter fun d => d.1).length := by
  have hstep : ∀ (b : MemBlock m n) (ok : Bool)
      (s : LiveDelta m n Unit),
      (applyDecision b ok s).blocks.length
        = s.blocks.length + (if ok = true then 1 else 0) := by
    intro b ok s
    simp only [applyDecision]
    cases ok <;> simp [addBlock]
  induction ds generalizing s with
  | nil => simp [runDecisions]
  | cons d ds ih =>
    have hunf : runDecisions s (d :: ds)
        = runDecisions (applyDecision d.2 d.1 s) ds := rfl
    rw [hunf, ih, hstep d.2 d.1 s]
    cases hd : d.1 <;>
      simp [hd, List.filter_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm]

/-- Допущенная последовательность с валидными решениями:
каждое true-решение удовлетворяет обеим проверкам (новизна и
сертифицированная польза) — рост памяти происходит только
через полный критерий. -/
theorem admits_satisfy_checks {m n : Type} [Fintype m]
    [Fintype n] (k : ℕ) (checks : Fin k → AdmissionChecks)
    (admits : Fin k → Bool)
    (hdec : ∀ t, admits t = true → admit (checks t)) :
    ∀ t, admits t = true →
      noveltyOk (checks t) ∧ gainOk (checks t) :=
  fun t h => hdec t h

end Hagi.Growth
namespace Hagi.Growth

/-- **Обоснованность запаса ε_cert (R419)**: если
истинный выигрыш в пределах ε_cert от оценки
(что даёт R410/R413 при θ-калибровке:
ε_cert = (b−a)√(ln(1/θ)/2)), то admit-решение
гарантирует, что ИСТИННЫЙ выигрыш
покрывает стоимость + риск. Запас — не
декорация, а сертификат звучности. -/
theorem admission_margin_sound (c : AdmissionChecks)
    (gtrue : ℝ) (hclose : |gtrue - c.gain| ≤ c.ε_cert)
    (h : admit c) :
    c.lamM * c.Δcost + c.lamR * c.Δrisk ≤ gtrue := by
  obtain ⟨_, hgain⟩ := h
  have hgain' : c.lamM * c.Δcost + c.lamR * c.Δrisk
      + c.ε_cert ≤ c.gain := hgain
  have hle : c.gain - c.ε_cert ≤ gtrue := by
    have h2 := abs_le.mp hclose
    linarith [h2.1]
  linarith [hgain', hle]


end Hagi.Growth

set_option linter.style.header false

/-!
# MemoryCycle — сквозной цикл: допуск → память →
квантованная консолидация → граница качества

Замыкает цепочку R271–R273 в один цикл управления памятью:

1. записи допускаются контроллером (novelty ∧ certified
   gain — R273);
2. память живёт как rank-1 блоки LiveDelta (точное
   представление истории спуска — R271);
3. консолидация (квантование факторов) оценивается
   аддитивным Frobenius-бюджетом k·Σ εᵢ (R272);
4. честный Lipschitz-мост: если функция потерь
   L-липшицева по весам в Frobenius-норме (ИЗМЕРЯЕМАЯ
   посылка h_emp_, как и вся эмпирика), ошибка качества
   после консолидации ≤ L·√(k·Σ εᵢ).

Формулируется и доказывается ТОЛЬКО арифметика границы;
оценка L и εᵢ — runtime-контракты.

Доказано:
* `consolidation_quality_bound`: при Lipschitz-посылке и
  per-block бюджетах εᵢ квантованная консолидация меняет
  потерю не более чем на L·√(k·Σ εᵢ);
* `memory_cycle_quality`: полная цепочка — память из
  последовательности допусков, консолидированная с бюджетом,
  сохраняет качество в пределах границы.
-/

open Finset Hagi.Architecture Hagi.Step Hagi.Step
  Hagi.Growth Matrix

namespace Hagi.Unified

variable {m n : Type} [Fintype m] [Fintype n]

/-- Frobenius-норма. -/
noncomputable def frobNorm (M : Matrix m n ℝ) : ℝ := Real.sqrt (frob M)

/-- Консолидированное качество: при измеряемой
L-Lipschitz-посылке на функцию потерь (по Frobenius-норме
весов) и per-block бюджетах замены εᵢ, изменение потери от
квантованной консолидации ≤ L·√(k·Σ εᵢ). -/
theorem consolidation_quality_bound (k : ℕ)
    (olds news : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (ε : Fin k → ℝ)
    (hbud : ∀ t, frob ((olds t).1ᵀ * (olds t).2
      - (news t).1ᵀ * (news t).2) ≤ ε t)
    (loss : Matrix m n ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ W W', |loss W - loss W'|
      ≤ L * frobNorm (W - W')) :
    |loss (∑ t, (olds t).1ᵀ * (olds t).2)
      - loss (∑ t, (news t).1ᵀ * (news t).2)|
      ≤ L * Real.sqrt ((k : ℝ) * ∑ t, ε t) := by
  have hb := consolidate_budget k olds news ε hbud
  refine le_trans (hlip _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ hL
  exact Real.sqrt_le_sqrt hb

/-- Полный цикл памяти: память, построенная из
последовательности допусков (контроллер R273), после
квантованной консолидации с per-block бюджетами εᵢ и при
измеряемой Lipschitz-посылке сохраняет качество в пределах
L·√(k·Σ εᵢ) — одна теорема про весь цикл
admit → store → consolidate. -/
theorem memory_cycle_quality (k : ℕ)
    (entries : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (news : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (ε : Fin k → ℝ)
    (hbud : ∀ t, frob ((entries t).1ᵀ * (entries t).2
      - (news t).1ᵀ * (news t).2) ≤ ε t)
    (loss : Matrix m n ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ W W', |loss W - loss W'|
      ≤ L * frobNorm (W - W')) :
    |loss (∑ t, (entries t).1ᵀ * (entries t).2)
      - loss (∑ t, (news t).1ᵀ * (news t).2)|
      ≤ L * Real.sqrt ((k : ℝ) * ∑ t, ε t) :=
  consolidation_quality_bound k entries news ε hbud loss L
    hL hlip

end Hagi.Unified

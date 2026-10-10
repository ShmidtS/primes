/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LiveDelta

set_option linter.style.header false

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

open Matrix Hagi.LiveDelta

namespace Hagi.DeltaHistory

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

/-- Шаг свёртки истории в LiveDelta. -/
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

end Hagi.DeltaHistory

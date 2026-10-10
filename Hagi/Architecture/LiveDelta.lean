/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# LiveDelta — низкоранговая пластичность живых весов

Формальное ядро механизма living weights (в духе TensorFold):
базовые (сжатые) веса + список принятых низкоранговых блоков
ΔW = Aᵀ·B, каждый со своим индексом ранга.

Доказано:
* граница ранга блока: rank(Aᵀ·B) ≤ card r;
* нулевой эффект: вход, ортогональный всем строкам-адресам A,
  не затрагивается блоком (x ᵥ* Aᵀ = 0 ⟹ x ᵥ* (Aᵀ·B) = 0);
* откат последнего блока точно восстанавливает состояние;
* бюджет памяти: k блоков стоят ровно k·(r·m + r·n) элементов.

Ничего о качестве обучения не утверждается — только структура
состояния и её точные свойства.
-/

open Matrix Finset

namespace Hagi.LiveDelta

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]

/-- Состояние живых весов: база + принятые низкоранговые блоки
(новейшие в голове списка). -/
structure LiveDelta (m n r : Type) [Fintype m] [Fintype n] [Fintype r] where
  base : Matrix m n ℝ
  blocks : List (Matrix r m ℝ × Matrix r n ℝ)

/-- Эффективные веса: база плюс сумма блоков. -/
def effectiveWeights (s : LiveDelta m n r) : Matrix m n ℝ :=
  s.base + (s.blocks.map fun b => b.1ᵀ * b.2).sum

/-- Принять блок: добавляется в голову списка. -/
def addBlock (A : Matrix r m ℝ) (B : Matrix r n ℝ)
    (s : LiveDelta m n r) : LiveDelta m n r where
  base := s.base
  blocks := (A, B) :: s.blocks

/-- Откат последнего принятого блока (пустой список — тождество). -/
def rollback (s : LiveDelta m n r) : LiveDelta m n r :=
  match s.blocks with
  | [] => s
  | _ :: bs => { s with blocks := bs }

/-- Откат точно отменяет принятие блока. -/
theorem rollback_addBlock (A : Matrix r m ℝ) (B : Matrix r n ℝ)
    (s : LiveDelta m n r) :
    rollback (addBlock A B s) = s := by
  simp [rollback, addBlock]

/-- Граница ранга низкорангового блока: rank(Aᵀ·B) ≤ card r —
блок влияет на модель не более чем через r линейных
направлений. -/
theorem block_rank_le (A : Matrix r m ℝ) (B : Matrix r n ℝ) :
    (Aᵀ * B).rank ≤ Fintype.card r := by
  have h1 : (Aᵀ * B).rank ≤ B.rank := rank_mul_le_right Aᵀ B
  have h2 : B.rank ≤ Fintype.card r := by
    have h := rank_le_card_width (Bᵀ)
    rwa [rank_transpose] at h
  exact le_trans h1 h2

/-- Нулевой эффект на ортогональных входах: если строка-вход x
ортогональна всем адресам A (x ᵥ* Aᵀ = 0), блок её не меняет. -/
theorem null_effect (A : Matrix r m ℝ) (B : Matrix r n ℝ)
    (x : m → ℝ) (hx : x ᵥ* Aᵀ = 0) :
    x ᵥ* (Aᵀ * B) = 0 := by
  have hassoc : x ᵥ* (Aᵀ * B) = (x ᵥ* Aᵀ) ᵥ* B := by
    funext j
    simp only [Matrix.vecMul, Matrix.mul_apply, dotProduct,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
  rw [hassoc, hx]
  simp

/-- Память одного блока: ровно r·m + r·n элементов факторов. -/
def blockCost [Fintype r] : ℕ := Fintype.card r * (Fintype.card m
  + Fintype.card n)

/-- Бюджет k блоков: ровно k·blockCost (факторы хранятся
отдельно от базы — сжатие базы не перезаписывается). -/
theorem blocks_cost (s : LiveDelta m n r) :
    s.blocks.length * blockCost (m := m) (n := n) (r := r)
      = s.blocks.length * (Fintype.card r * (Fintype.card m
          + Fintype.card n)) := rfl

end Hagi.LiveDelta

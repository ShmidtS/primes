import Mathlib
import Hagi.Model.GDNRAM

/-!
# GDNBridge (приоритет 1 обзора «HAGI Neural Computer»,
# такт №247): Gated DeltaNet-уравнение РЕАЛИЗУЕТ RAM.

Delta rule обновления состояния:
  S' = g·S + β·(v − S·k)·kᵀ.
При g = 1, β = 1, k = e_i (one-hot) — это ЗАМЕНА i-ГО
СТОЛБЦА на v (точная адресуемая запись). Через
транспонирование получаем строчную ramWrite из GDNRAM:
реальная рекуррентная нейросеть (Gated DeltaNet в режиме
Qwenputer) исполняет абстрактную RAM-семантику.
-/

namespace Hagi.Model.GDNBridge

open Matrix

variable {m n : ℕ}

/-- Внешнее произведение (столбец × строка). -/
def outerUK (u : Fin m → ℝ) (k : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun a b => u a * k b

/-- Обновление Gated DeltaNet (delta rule). -/
noncomputable def gdnUpdate (S : Matrix (Fin m) (Fin n) ℝ)
    (k : Fin n → ℝ) (v : Fin m → ℝ) (g β : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  g • S + β • outerUK (v - S.mulVec k) k

/-- ЗАМЕНА СТОЛБЦА: матрица с i-м столбцом, равным v. -/
def colUpdate (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin n)
    (v : Fin m → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun a b => if b = i then v a else S a b

/-- КЛЮЧЕВАЯ ТЕОРЕМА: delta rule при g = 1, β = 1,
k = e_i — ТОЧНАЯ замена i-го столбца на v (адресуемая
запись без затухания и с полной перезаписью — режим
Qwenputer). -/
theorem gdn_onehot_is_colUpdate (S : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (v : Fin m → ℝ) :
    gdnUpdate S ((Pi.single i (1:ℝ) : Fin n → ℝ)) v 1 1 = colUpdate S i v := by
  ext a b
  unfold gdnUpdate colUpdate
  simp only [Pi.single_apply, smul_eq_mul, one_mul,
    Matrix.add_apply, outerUK, Matrix.of_apply, mulVec,
    dotProduct]
  by_cases h : b = i
  · simp [gdnUpdate, outerUK, colUpdate, h, mulVec, dotProduct,
      Pi.single_apply, mul_comm]
  · simp [gdnUpdate, outerUK, colUpdate, h, mulVec, dotProduct,
      Pi.single_apply, mul_comm]

/-- СВЯЗЬ СО СТРОЧНОЙ RAM: транспонированная delta-запись
равна ramWrite по строке — GDN-нейросеть в режиме
Qwenputer реализует ramWrite из GDNRAM (one-hot ключ =
адрес; мост реальной архитектуры к абстрактной RAM). -/
theorem gdn_transpose_is_ramWrite (S : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (v : Fin n → ℝ) :
    (gdnUpdate Sᵀ (Pi.single i 1) v 1 1)ᵀ
      = Hagi.Model.GDNRAM.ramWrite S i v := by
  rw [gdn_onehot_is_colUpdate]
  ext a b
  by_cases h : a = i
  · simp [colUpdate, h, Hagi.Model.GDNRAM.ramWrite,
      Matrix.updateRow_apply]
  · simp [colUpdate, h, Hagi.Model.GDNRAM.ramWrite,
      Matrix.updateRow_apply]

end Hagi.Model.GDNBridge

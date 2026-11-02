import Mathlib
import Hagi.Model.Memory

/-!
# GDNBridge (приоритет 1 обзора «HAGI Neural Computer»,
# ): Gated DeltaNet-уравнение РЕАЛИЗУЕТ RAM.

Delta rule обновления состояния (КАНОНИЧЕСКАЯ gated-форма,
исправлено по аудиту №262: остаток берётся по ЗАТУХШЕМУ
состоянию gS, как в оригинальной статье Gated DeltaNet):
  S' = g·S + β·(v − g·S·k)·kᵀ.
При g = 1, β = 1, k = e_i (one-hot) — это ЗАМЕНА i-ГО
СТОЛБЦА на v (точная адресуемая запись; при g = 1 формы
совпадают, старые теоремы сохраняются). Через
транспонирование — строчная ramWrite из GDNRAM:
реальная рекуррентная нейросеть (Gated DeltaNet в режиме
Qwenputer) исполняет абстрактную RAM-семантику.
Общая лемма gdn_onehot_interp: при произвольных g, β —
интерполяция столбца: (1−β)·g·S + β·v (мера перезаписи β).
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
  g • S + β • outerUK (v - g • S.mulVec k) k

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


/-- КОЛОНОЧНАЯ ИНТЕРПОЛЯЦИЯ: i-й столбец = (1−β)·g·S + β·v,
остальные затухают в g раз. -/
def colInterp (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin n)
    (v : Fin m → ℝ) (g β : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun a b =>
    if b = i then (1-β)*g*S a b + β*v a else g*S a b

/-- ОБЩАЯ ЛЕММА gated-записи: при one-hot ключе и
произвольных g, β обновление S' = gS + β(v − gSk)e_iᵀ —
ТОЧНО колоночная интерполяция: i-й столбец =
(1−β)·g·S + β·v (β — мера перезаписи; β=1 — полная
замена, β=0 — чистое затухание g). Частный случай
g = β = 1 даёт gdn_onehot_is_colUpdate. -/
theorem gdn_onehot_interp (S : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (v : Fin m → ℝ) (g β : ℝ) :
    gdnUpdate S ((Pi.single i (1:ℝ) : Fin n → ℝ)) v g β
      = colInterp S i v g β := by
  ext a b
  unfold gdnUpdate colInterp outerUK
  simp only [Pi.single_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.of_apply, Matrix.smul_apply, mulVec, dotProduct,
    Pi.single_apply, mul_comm, mul_sub, sub_mul]
  by_cases h : b = i
  · simp [h, mul_comm]
    ring
  · simp [h, mul_comm]

/-! ### СИНТЕЗ-АРХИТЕКТУРА: полный RAM-контракт GDN

Аудит-синтез (гибридный поток + GDN-RAM):
для детерминированного подпространства
рамка требует полного контракта
памяти: чтение без модификации,
инертность остальных адресов,
write-after-write. Здесь эти инварианты
закрыты для режима
α=1, β=1, one-hot. -/

/-- ЧТЕНИЕ = ВЫБОРКА СТРОКИ: умножение
one-hot слева (vecMul) возвращает i-ю
строку — чистое чтение
(матрица не меняется). -/
theorem gdn_onehot_read {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ* S = S i := by
  ext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- ИНЕРТНОСТЬ ДРУГИХ АДРЕСОВ: запись
в адрес i не трогает другие
адреса. -/
theorem colUpdate_inert {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin n)
    (v : Fin m → ℝ) (b : Fin n) (hb : b ≠ i)
    (a : Fin m) :
    colUpdate S i v a b = S a b := by
  simp [colUpdate, hb]

/-- WRITE-AFTER-WRITE: последовательные
записи в один адрес —
последнее значение
побеждает (память не
накопляет мусор). -/
theorem colUpdate_waw {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin n)
    (v w : Fin m → ℝ) :
    colUpdate (colUpdate S i v) i w = colUpdate S i w := by
  ext a b
  simp only [colUpdate]
  by_cases h : b = i
  · simp [h]
  · simp [h]

/-- ПОЛНЫЙ ЦИКЛ RAM: записали v в
адрес i через GDN → читаем
i-ю строку через mulVec →
получили ТОЧНО v (детерминированное
подпространство воспроизводит
записанное без единой
ошибки). -/
theorem gdn_ram_roundtrip {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) :
    (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ*
      Hagi.Model.GDNRAM.ramWrite S i v = v := by
  change (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ*
    (Matrix.updateRow S i v) = v
  rw [gdn_onehot_read]
  exact Matrix.updateRow_self

end Hagi.Model.GDNBridge

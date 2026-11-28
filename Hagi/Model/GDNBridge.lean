import Mathlib.Tactic
import Hagi.Model.Memory

/-!
# GDNBridge: Gated DeltaNet-уравнение РЕАЛИЗУЕТ RAM.

Delta rule обновления состояния (каноническая gated-форма:
остаток берётся по затухшему состоянию gS, как в оригинальной
статье Gated DeltaNet):
  S' = g·S + β·(v − g·S·k)·kᵀ.
При g = 1, β = 1, k = e_i (one-hot) — это ЗАМЕНА i-ГО
СТОЛБЦА на v (точная адресуемая запись; при g = 1 формы
совпадают). Через
транспонирование — строчная ramWrite из GDNRAM:
реальная рекуррентная нейросеть (Gated DeltaNet в режиме
Qwenputer) исполняет абстрактную RAM-семантику.
Общая лемма gdn_onehot_interp: при произвольных g, β —
интерполяция столбца: (1−β)·g·S + β·v (мера перезаписи β).

State-carry BPTT (`optimal_lm.py`, `state_carry = True`): `GdnStep`, `gdnScan`
(fold of `gdnUpdate` over a chunk); `gdnScan_append` — scanning `l₁ ++ l₂` with
the state carried across the chunk boundary equals the one-pass scan, so
chunking changes nothing; `carry_without_wrap_leaks` — a step with `g = 1`,
`β = 0` passes the state through untouched, hence a stream boundary MUST reset
the state (`wrap`), otherwise the next stream reads the previous one.
Honest boundary: the carried state is `detach()`ed, so the forward pass is
exact across chunks while the backward pass is truncated (TBPTT): no gradient
flows from chunk 2 into the parameters of chunk 1 through `S`.
`carry_influence_decays`: after `T` decay-only steps the carried state is
`g^T • S₀`; `carry_influence_abs_le`: `|g| ≤ γ ⇒ |g^T| ≤ γ^T` — the truncated
part is exponentially small for `γ < 1`.
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

/-! ### Полный RAM-контракт GDN

Для детерминированного подпространства требуется полный контракт
памяти: чтение без модификации, инертность остальных адресов,
write-after-write. Инварианты закрыты для режима α=1, β=1, one-hot. -/

/-- ЧТЕНИЕ = ВЫБОРКА СТРОКИ: умножение one-hot слева (vecMul)
возвращает i-ю строку — чистое чтение (матрица не меняется). -/
theorem gdn_onehot_read {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ* S = S i := by
  ext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- ИНЕРТНОСТЬ ДРУГИХ АДРЕСОВ: запись в адрес i не трогает другие адреса. -/
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

/-- ПОЛНЫЙ ЦИКЛ RAM: записали v в адрес i через GDN → читаем i-ю строку
через mulVec → получили ТОЧНО v. -/
theorem gdn_ram_roundtrip {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) :
    (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ*
      Hagi.Model.GDNRAM.ramWrite S i v = v := by
  change (Pi.single i (1:ℝ) : Fin m → ℝ) ᵥ*
    (Matrix.updateRow S i v) = v
  rw [gdn_onehot_read]
  exact Matrix.updateRow_self

/-- LAG-1 ALIGNMENT (misaligned read): запись в адрес
i в момент t−1 (ключ k_{t−1} = e_i); чтение в момент t
по ДРУГОМУ адресу j ≠ i возвращает старую строку
S j — незатронутые адреса не изменились.

Эмпирическая мотивация (не посылка): в синтез-архитектуре Arch3
(mHC + Lag-1 GDN + RoPE) рассинхронный доступ к адресу даёт
эмпирический потолок ~50% против ~99.6% при выровненном lag-1. -/
theorem gdn_lag1_read_miss {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m)
    (v : Fin n → ℝ) (hj : j ≠ i) :
    (Pi.single j (1:ℝ) : Fin m → ℝ) ᵥ*
      Hagi.Model.GDNRAM.ramWrite S i v = S j := by
  change (Pi.single j (1:ℝ) : Fin m → ℝ) ᵥ*
    (Matrix.updateRow S i v) = S j
  rw [gdn_onehot_read]
  exact Matrix.updateRow_ne hj

/-- LAG-1 ALIGNMENT (полный контракт, premise-form):
чтение в момент t по адресу j после записи в адрес i
в момент t−1 (k_{t−1} = e_i, значение v_t = v) возвращает
v при j = i (совпавший адрес — см. также
`gdn_ram_roundtrip`) и старую строку S j при j ≠ i
(рассинхрон — `gdn_lag1_read_miss`). -/
theorem gdn_lag1_alignment {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m)
    (v : Fin n → ℝ) :
    (Pi.single j (1:ℝ) : Fin m → ℝ) ᵥ*
      Hagi.Model.GDNRAM.ramWrite S i v =
        if j = i then v else S j := by
  by_cases h : j = i
  · rw [h, if_pos rfl]
    exact gdn_ram_roundtrip S i v
  · rw [if_neg h]
    exact gdn_lag1_read_miss S i j v h

/-- Шаг GDN с параметрами, упакованными в запись. -/
structure GdnStep (m n : ℕ) where
  k : Fin n → ℝ
  v : Fin m → ℝ
  g : ℝ
  β : ℝ
/-- Скан GDN по списку шагов: `S_T = foldl gdnUpdate`. -/
noncomputable def gdnScan (S : Matrix (Fin m) (Fin n) ℝ) :
    List (GdnStep m n) → Matrix (Fin m) (Fin n) ℝ
  | [] => S
  | st :: l => gdnScan (gdnUpdate S st.k st.v st.g st.β) l
/-- State-carry BPTT: скан по `l₁ ++ l₂` с переносом состояния между чанками
равен скану по конкатенации — разбиение на чанки ничего не меняет. -/
theorem gdnScan_append (S : Matrix (Fin m) (Fin n) ℝ) (l₁ l₂ : List (GdnStep m n)) :
    gdnScan S (l₁ ++ l₂) = gdnScan (gdnScan S l₁) l₂ := by
  induction l₁ generalizing S with
  | nil => rfl
  | cons st l ih => rw [List.cons_append, gdnScan, gdnScan, ih]
/-- Перенос без обнуления на границе потоков — утечка: шаг с `g = 1`,
`β = 0` пропускает состояние насквозь, и чтение `y = S·k` второго потока
зависит от предыстории первого. Поэтому `wrap` обязан обнулять `S`. -/
theorem carry_without_wrap_leaks (S : Matrix (Fin m) (Fin n) ℝ) (k : Fin n → ℝ)
    (v : Fin m → ℝ) :
    gdnScan S [{ k, v, g := 1, β := 0 }] = S := by
  unfold gdnScan gdnUpdate
  simp [gdnScan]

/-- Вклад перенесённого состояния затухает: `T` шагов с затуханием `g` и
`β = 0` дают `g^T • S₀` — усечённый градиент по первому чанку теряет
множитель `g^T` (цена TBPTT экспоненциально мала при `g < 1`). -/
theorem carry_influence_decays (S : Matrix (Fin m) (Fin n) ℝ) (k : Fin n → ℝ)
    (v : Fin m → ℝ) (g : ℝ) (T : ℕ) :
    gdnScan S (List.replicate T { k, v, g, β := 0 } : List (GdnStep m n))
      = (g ^ T) • S := by
  induction T generalizing S with
  | zero => simp [gdnScan]
  | succ T ih =>
    rw [List.replicate_succ, gdnScan, gdnUpdate, ih]
    simp only [zero_smul, add_zero, smul_smul, pow_succ']
    rw [mul_comm]
/-- Цена TBPTT (скалярная форма): доля влияния `S₀` после `T` шагов равна
`g^T`; при `|g| ≤ γ < 1` — `|g^T| ≤ γ^T → 0`: усечённый градиент теряет
экспоненциально малую часть. -/
theorem carry_influence_abs_le (g γ : ℝ) (T : ℕ) (hg : |g| ≤ γ) :
    |g ^ T| ≤ γ ^ T := by
  rw [abs_pow g T]
  exact pow_le_pow_left₀ (abs_nonneg g) hg T

theorem gdn_beta_readout {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (k : Fin n → ℝ) (v : Fin m → ℝ) (g β : ℝ)
    (hk : ∑ j, k j * k j = 1) :
    (gdnUpdate S k v g β).mulVec k = β • v + (1 - β) • g • (S.mulVec k) := by
  ext a
  have hSk : (S.mulVec k) a = ∑ j, S a j * k j := rfl
  show (∑ j, (g • S + β • outerUK (v - g • S.mulVec k) k) a j * k j) = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, outerUK, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hSk]
  have e1 : ∀ j, (g * S a j + β * ((v a - g * (∑ j', S a j' * k j')) * k j)) * k j
      = g * (S a j * k j) + (β * (v a - g * (∑ j', S a j' * k j'))) * (k j * k j) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hk]
  simp only [smul_eq_mul, mul_one, Pi.add_apply, Pi.smul_apply, hSk]; ring
/-- Итерированная запись по одному ключу при `g = 1`: отклонение прочитанного
значения от `v` умножается на `(1 − β)` за шаг. `β = 1` — за один шаг; `|1 − β| < 1` —
геометрическая сходимость; `β ∈ (1, 2)` — осциллирующая (со сменой знака) сходимость:
старая ассоциация инвертируется, что при `β ≤ 1` невозможно. -/
theorem gdn_beta_iter (S : Matrix (Fin m) (Fin n) ℝ) (k : Fin n → ℝ) (v : Fin m → ℝ) (β : ℝ)
    (hk : ∑ j, k j * k j = 1) (t : ℕ) :
    ((fun S => gdnUpdate S k v 1 β)^[t] S).mulVec k - v = (1 - β) ^ t • ((S.mulVec k) - v) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    rw [gdn_beta_readout _ k v 1 β hk]
    have h2 : ((fun S => gdnUpdate S k v 1 β)^[t] S).mulVec k = (1 - β) ^ t • (S.mulVec k - v) + v := sub_eq_iff_eq_add.mp ih
    rw [h2]
    simp only [smul_eq_mul, smul_add, smul_sub, pow_succ]
    module

end Hagi.Model.GDNBridge

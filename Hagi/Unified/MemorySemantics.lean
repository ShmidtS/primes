/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.GDNBridge
import Hagi.Unified.MemoryCycle

open Matrix

set_option linter.style.header false

/-!
# MemorySemantics — единая сертифицированная запись в память
(аудит v18 P1: MemoryReadWriteCorrectness + CertifiedMemoryAdmission)

Аудит: «запись и чтение действительно соответствуют адресуемой
памяти» + «допущенная запись имеет необходимый запас полезности».
Обе половины соединены в ОДИН сертификат записи:

* `RamWriteCert`: адресуемая запись с точной RAM-семантикой
  (чтение по ключу возвращает значение, чужие адреса не тронуты);
* `CertifiedMemoryWrite`: RAM-сертификат + допуск контроллера
  (novelty ∧ gain) — «не каждое новое знание автоматически
  становится постоянной частью системы».

Носители нетронуты: GDN-семантика — Model.GDNBridge
(gdn_transpose_is_ramWrite: нейро-дельта == Matrix.updateRow),
Admission-контроллер — Unified.MemoryCycle.
-/

namespace Hagi.Unified.MemorySemantics

/-! ### Сертификат адресуемой записи -/

/-- СЕРТИФИКАТ ЗАПИСИ: адрес `i`, значение `v`, состояние до.
Три обязательных свойства точной RAM-семантики (носитель —
строчная запись Matrix.updateRow, к которой GDN-дельта
сводится по gdn_transpose_is_ramWrite). -/
structure RamWriteCert {m n : ℕ} (pre : Matrix (Fin m) (Fin n) ℝ)
    (address : Fin m) (value : Fin n → ℝ) where
  /-- Фактическое пост-состояние (явное, не выводимое). -/
  post : Matrix (Fin m) (Fin n) ℝ
  /-- ГЛАВНОЕ СВОЙСТВО: пост-состояние — точная запись
  updateRow (никакой тавтологии: пост — независимое поле,
  равенство — доказываемое поле сертификата). -/
  post_eq : post = Matrix.updateRow pre address value
  /-- Чтение по записанному адресу возвращает значение. -/
  read_back : (Pi.single address (1:ℝ) : Fin m → ℝ) ᵥ* post = value
  /-- Чужой адрес j ≠ address не изменён. -/
  others_untouched : ∀ j : Fin m, j ≠ address →
    post j = pre j
  /-- Идемпотентность записи: повторная запись того же
  значения по тому же адресу не меняет состояние. -/
  rewrite_idem : Matrix.updateRow post address value = post

/-- Канонический конструктор: все четыре свойства GDN-записи
(gdn_ram_roundtrip, updateRow-семантика). -/
noncomputable def ramWriteCert_of_updateRow {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (v : Fin n → ℝ) :
    RamWriteCert S i v where
  post := Matrix.updateRow S i v
  post_eq := rfl
  read_back := Hagi.Model.GDNBridge.gdn_ram_roundtrip S i v
  others_untouched := by
    intro j hj
    simp [Matrix.updateRow_apply, hj]
  rewrite_idem := by
    ext a b
    simp only [Matrix.updateRow_apply]
    by_cases h : a = i
    · simp [h]
    · simp [h]

/-! ### Допуск: RAM-сертификат + Admission = сертифицированная запись -/

/-- СЕРТИФИЦИРОВАННАЯ ЗАПИСЬ В ПАМЯТЬ. -/
structure CertifiedMemoryWrite {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (v : Fin n → ℝ)
    (c : Hagi.Growth.AdmissionChecks) where
  /-- RAM-корректность записи. -/
  ram : RamWriteCert S i v
  /-- Допуск контроллера (novelty ∧ gain). -/
  admitted : Hagi.Growth.admit c

/-- Звучность допуска: из сертификата следует строгий запас
полезности (gain покрывает стоимость+риск+запас) —
«необходимый запас полезности» из аудита. -/
theorem certified_gain_margin {m n : ℕ}
    {S : Matrix (Fin m) (Fin n) ℝ} {i : Fin m} {v : Fin n → ℝ}
    {c : Hagi.Growth.AdmissionChecks}
    (w : CertifiedMemoryWrite S i v c) :
    c.lamM * c.Δcost + c.lamR * c.Δrisk + c.ε_cert ≤ c.gain :=
  w.admitted.2

end Hagi.Unified.MemorySemantics

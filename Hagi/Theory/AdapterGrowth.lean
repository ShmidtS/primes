/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

/-!
# AdapterGrowth — certified low-rank адаптер роста (C532)

Существующие механизмы роста добавляют объём ЦЕЛИКОМ: fiber-width
C494 (`mkOrthoFiberBlock` — widening признаков) и depth-block
C504/C506/C521 (`benchResidualBlock γ h` — ЦЕЛЫЙ блок,
~d·d параметров при скрытой ширине ~d). C532 добавляет
МИНИМАЛЬНЫЙ носитель роста: low-rank side-branch адаптер
(LoRA-форма, Hu et al. 2021, arXiv:2106.09685)

  `adapterVec A B x = x + B *ᵥ (A *ᵥ x)`,

где `A : r×d`, `B : d×r` — добавляется `2·r·d` параметров
вместо `d·d` полного блока (`r ≪ d`).

Ближайший сосед — `Hagi.Core.Element.residualLeaf E₀ + A * B`
(consolidation листьев): его `residualLeaf_zero` требует ОБА
множителя нулевыми; здесь нейтральность сертифицирована при
ОДНОМ нулевом множителе (ядро LoRA-инициализации: в произведении
`B * A` достаточно обнулить один сомножитель), плюс obj-инвариант
для ЛЮБОГО функционала при admission (grow-мост, паттерн
`grow_block_obj_invariant` C504), ЯВНЫЙ счёт параметров с
неравенством против полного блока и certified-шаг обучения
адаптера (measured drop > 0 / HOLD — паттерн C506/C521).

Cycle-соответствие: `scripts/bench_bridge.py --mode adapter-grow`
исполняет ровно эту схему на живом корпусе unified_ledger:
trunk+head certified fd-шаги (C521 phase A), freeze trunk,
адаптер на голове `pred = w·(f + B·(A·f))` растёт при B = 0
(assert: obj-инвариант ТОЧНО), certified fd-шаги ТОЛЬКО по 2·r·d
параметрам адаптера (r = 1 → 8, r = 2 → 16 против 21 параметра
целого mh5-блока), head-to-head прогресс на равном числе шагов.

## Honest pins (что этот мост НЕ покрывает)

- **Certified-шаги после admission** — measured (drop > 0 в
  трейсе), не доказательная нижняя граница выигрыша; на шаге 0
  вклад адаптера = 0 по построению (B = 0).
- **Экономия 2·r·d < d·d** — свойство СЧЁТА параметров при
  2·r ≤ d (честное условие, не замаскировано; ранг-семантика —
  Mathlib `Matrix.rank_mul_le`, available-not-needed здесь).
- **Адаптер остаётся low-rank** после certified-обучения —
  не утверждается (шаги двигают значения A/B, факторизация
  r фиксирована по построению носителя, ранг ≤ r —
  `Hagi.Core.delta_rank_le`).
- **Lipschitz обученного адаптера** — не утверждается (per-block
  premise — контракт C436); на шаге 0 добавка 0.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.AdapterGrowth

open scoped Matrix

section Adapter

variable {d r : Type*} [Fintype d] [Fintype r]
  [DecidableEq d] [DecidableEq r]

/-- LoRA-адаптер слоя: side-branch `x + B *ᵥ (A *ᵥ x)` с факторами
`A : r × d` (down) и `B : d × r` (up). Носитель `d → ℝ` НЕ
расширяется (в отличие от fiber-grow C494) и НЕ добавляется целый
блок (C504): рост живёт в существующем пространстве. -/
def adapterVec (A : Matrix r d ℝ) (B : Matrix d r ℝ)
    (x : d → ℝ) : d → ℝ := x + B *ᵥ (A *ᵥ x)

omit [DecidableEq d] [DecidableEq r] in
/-- Ядро LoRA-инициализации, up-фактор: `B = 0` ⇒ адаптер
ТОЖДЕСТВЕНЕН при ПРОИЗВОЛЬНОЙ `A` (0 *ᵥ a = 0, a + 0 = a).
Сильнее `Hagi.Core.residualLeaf_zero`: один нулевой множитель
в произведении `B *ᵥ (A *ᵥ x)` обнуляет всю ветку. -/
@[simp]
theorem adapter_neutral_B (A : Matrix r d ℝ) :
    adapterVec A 0 = id := by
  funext x
  simp [adapterVec, Matrix.zero_mulVec]

omit [DecidableEq d] [DecidableEq r] in
/-- Ядро LoRA-инициализации, down-фактор: `A = 0` ⇒ адаптер
ТОЖДЕСТВЕНЕН при ПРОИЗВОЛЬНОЙ `B` (b *ᵥ 0 = 0, a + 0 = a):
нейтральной инициализации достаточно одного сомножителя. -/
@[simp]
theorem adapter_neutral_A (B : Matrix d r ℝ) :
    adapterVec 0 B = id := by
  funext x
  simp [adapterVec, Matrix.zero_mulVec]

omit [DecidableEq d] [DecidableEq r] in
/-- Admission-инвариант: при нейтральной инициализации (любой
один нулевой фактор) ЛЮБОЙ функционал obj от выхода слоя сохраняет
значение ТОЧНО — certified-нейтральность добавления адаптера
(congrArg-мост, паттерн `grow_block_obj_invariant` C504). -/
theorem adapter_obj_invariant {A : Matrix r d ℝ}
    {B : Matrix d r ℝ} (hB : B = 0) (obj : (d → ℝ) → ℝ)
    (x : d → ℝ) : obj (adapterVec A B x) = obj x := by
  rw [hB, adapter_neutral_B]
  rfl

end Adapter

/-! ## Счёт параметров: 2·r·d против d·d полного блока -/

section ParamCount

variable (r d : Type*) [Fintype r] [Fintype d]

/-- Явный счёт параметров адаптера: позиции двух факторов —
down `A : r × d` и up `B : d × r`, каждая позиция — одна
вещественная ячейка. -/
theorem adapter_param_count :
    (Finset.univ : Finset (r × d)).card +
      (Finset.univ : Finset (d × r)).card =
    2 * Fintype.card r * Fintype.card d := by
  simp [Fintype.card_prod]
  ring

variable {r d}

/-- Полный d×d-блок того же слоя несёт `card d * card d`
параметров — база сравнения объёма (identity-блок C504 при
скрытой ширине ~d). -/
theorem block_param_count : (Fintype.card d * Fintype.card d :
    ℕ) = (Finset.univ : Finset (d × d)).card := by
  simp [Fintype.card_prod]

/-- Экономия объёма: при `2 * card r ≤ card d` адаптер ранга `r`
строго меньше полного блока по числу параметров
(`2·r·d ≤ d·d`, равенство только при `2r = d`). Bench-инстанс
C532: r=1, d=4 → 8 ≤ 16. -/
theorem adapter_param_count_le_block
    (h : 2 * Fintype.card r ≤ Fintype.card d) :
    2 * Fintype.card r * Fintype.card d ≤
      Fintype.card d * Fintype.card d :=
  Nat.mul_le_mul_right _ h

/-- Строгая экономия при `2 * card r < card d`. -/
theorem adapter_param_count_lt_block
    (h : 2 * Fintype.card r < Fintype.card d) :
    2 * Fintype.card r * Fintype.card d <
      Fintype.card d * Fintype.card d := by
    have hd : 0 < Fintype.card d :=
      lt_of_le_of_lt (Nat.zero_le _) h
    exact Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl _) hd

end ParamCount

/-! ## Certified-шаг обучения адаптера -/

section CertifiedStep

variable {S : Type*} (obj : S → ℝ) (s s' : S)

/-- Certified-шаг обучения адаптера: COMMIT только по measured
строгому drop (obj s' < obj s), иначе HOLD (состояние не меняется)
— bench-семантика grow-цикла C506/C521 (admission drop > 0,
rollback при не-спуске). -/
noncomputable def adapterStep : S :=
  if obj s' < obj s then s' else s

/-- COMMIT-ветка certified: measured drop > 0 ⇒ состояние
обновляется и obj строго убывает. -/
theorem adapter_step_certified (h : obj s' < obj s) :
    adapterStep obj s s' = s' ∧
      obj (adapterStep obj s s') < obj s := by
  unfold adapterStep
  split
  · rename_i h'; exact ⟨rfl, h'⟩
  · rename_i h'; exact absurd h h'

/-- Негатив (noBlockAdmissionWithoutMargin-паттерн C444):
отсутствие строгого drop ⇒ HOLD, состояние ТОЧНО не меняется —
нулевой/отрицательный кандидат не допускается. -/
theorem adapter_step_hold (h : ¬ obj s' < obj s) :
    adapterStep obj s s' = s := by
  unfold adapterStep
  split
  · rename_i h'; exact absurd h' h
  · rfl

end CertifiedStep

end Hagi.Theory.AdapterGrowth

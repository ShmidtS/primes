/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.LMCompose
import Hagi.Theory.FunctionPreservingGrowth

/-!
# GrowTrunkBlock — рост trunk'а ЦЕЛЫМ БЛОКОМ (bench-мост C504)

C504 расширяет мини-HAGI: рост = добавление ЦЕЛОГО блока в trunk
(глубина +1), а не только fiber-признака. Теоретическая основа —
C450 `FunctionPreservingGrowth` (`trunk_function_preserving`,
`function_preserving_admissible`); этот модуль — перенос той же
идеи на bench-носитель:

* `benchResidualBlock γ h` — residual-gated блок bench-формы
  `y = x + γ·h x` (L1-rms + MLP атомы bench_bridge живут внутри
  `h`; важно: rms-подобная норма НЕ даёт identity даже при
  масштабе 1 — 1/(1+1/1000) = 1000/1001 ≠ 1 — поэтому identity
  достигается только residual-zero гейтом γ = 0).
* `benchResidual_zero` — при γ = 0 блок ТОЖДЕСТВЕНЕН (точное
  равенство функций; Fraction-экзактность: `0·a = 0`, `a+0 = a`).
* `benchTrunk` / `benchTrunk_append` — последовательная композиция
  блоков (foldl-форма, mirrors `lmTrunk`).
* `grow_block_bench_sound` — добавление residual-zero блока
  сохраняет trunk-функцию ТОЧНО — bench-инстанс C450
  `trunk_function_preserving`.
* `grow_block_obj_invariant` — ЛЮБОЙ функционал obj от trunk-
  выхода (канонический MSE-объектив bench) инвариантен при grow
  (congrArg-следствие) — bench-мост к obj-непрерывности цепи.
* `bench_bridge_to_C450` — residual-zero блок и C450 `identityBlock`
  вычисляют ОДНУ И ТУ ЖЕ функцию (оба = id): bench-форма и
  контракт-форма `CertifiedBlock` — один и тот же step-0 инстанс.

Cycle-соответствие: `scripts/bench_bridge.py --mode mini-hagi4`
исполняет ровно эту схему: GROW-BLOCK (γ=0, нейтральная адмиссия
C450 `function_preserving_admissible`: 0 ≤ 0; NOT a CertStepData
step — как w||[0] fiber-grow в C494), затем certified fd-шаги
блока (snap 1/10000, admission ТОЛЬКО по measured canonical
drop > 0 — вклад блока появляется тут), затем GPM continual +
Ville stop на ОДНОЙ канонической CertStepData цепи; obj до/после
grow равен ТОЧНО (exact Fraction assert).

C506 (`--mode mini-hagi5`): ПОВТОРЯЕМЫЙ grow-цикл — несколько
identity-grow событий в одном прогоне (глубина 2 → 5, каждое —
`grow_blocks_repeat_sound` шаг за шагом), между событиями —
certified-обучение ТОЛЬКО нового блока (старые frozen); весь цикл
под явным вычислительным бюджетом (cap знаменателей, cap шагов,
Ville-стоп) — bench-измерение, не теорема.

## Honest pins (что этот мост НЕ покрывает)

- **Certified-шаги после grow** — measured (drop > 0 в трейсе,
  `Hagi.Runtime.CertChecker`), не доказательная нижняя граница
  выигрыша; на шаге 0 вклад блока = 0 по построению (γ = 0).
- **Lipschitz после обучения блока** — не утверждается здесь
  (после γ ≠ 0 блок ненулевой; per-block premise — контракт C436);
  на шаге 0 lip-добавка 0 — C450 `blocksLip_grow_identity`.
- **Носители**: bench-блоки — произвольные функции-стрелки на
  `ℕ → V → ℝ`, `CertifiedBlock` — запись с attn/norm-полями;
  унификация носителей — вне этого бита (KISS; совпадение ФУНКЦИЙ
  фиксирует `bench_bridge_to_C450`).
- Отсутствие полезности нейтрального блока на шаге 0 — по
  построению; польза — из последующего certified-обучения (тот же
  pin, что у C450/C444).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.GrowTrunkBlock

open Hagi.Model.LMCompose Hagi.Theory.FunctionPreservingGrowth

section Residual

variable {V : Type}

/-- Bench-блок роста: residual-gate форма `y = x + γ·h x`, где `h` —
произвольная внутренняя функция блока (bench_bridge: L1-rms-surrogate
норма → W₁ → ReLU → W₂). При `γ = 0` блок — ТОЧНАЯ identity (см.
`benchResidual_zero`): внутренности полностью замаскированы нулём.
Инициализация внутренностей «identity-like» НЕ работает: rms-норма
не идентична даже при единичном масштабе (1/(1+ε) ≠ 1). -/
def benchResidualBlock (γ : ℝ)
    (h : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    ℕ → V → ℝ :=
  fun t v => x t v + γ * h x t v

/-- Шаг 0: γ = 0 ⇒ блок тождественен — ТОЧНОЕ равенство функций
(`0·a = 0`, `a + 0 = a`), независимо от внутренностей `h`.
Bench-инстанс паттерна `zero_init_identity` /
`blockApply_identityBlock` (C450). -/
theorem benchResidual_zero (h : (ℕ → V → ℝ) → ℕ → V → ℝ)
    (x : ℕ → V → ℝ) : benchResidualBlock 0 h x = x := by
  funext t v
  simp [benchResidualBlock]

end Residual

section Trunk

variable {V : Type}

/-- Композиция bench-блоков: первый блок применяется первым
(foldl-форма, mirrors `lmTrunk` C444/LMCompose). -/
def benchTrunk : List ((ℕ → V → ℝ) → ℕ → V → ℝ) →
    (ℕ → V → ℝ) → ℕ → V → ℝ :=
  List.foldl (fun b f => f ∘ b) id

/-- Добавление блока в КОНЕЦ trunk'а применяет его к выходу
старого trunk'а (append-лемма, mirrors `lmTrunk_append_single`). -/
theorem benchTrunk_append (bs : List ((ℕ → V → ℝ) → ℕ → V → ℝ))
    (f : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    benchTrunk (bs ++ [f]) x = f (benchTrunk bs x) := by
  simp [benchTrunk]

/-- **Bench-мост (C504)**: добавление ЦЕЛОГО residual-zero блока в
trunk сохраняет функцию ТОЧНО — `benchTrunk (bs ++ [γ=0-блок]) x =
benchTrunk bs x`. Это bench-инстанс C450 `trunk_function_preserving`
(`lmTrunk (bs ++ [identityBlock]) x = lmTrunk bs x`): рост глубины
2 → 3 не меняет вычисляемую функцию на шаге 0. -/
theorem grow_block_bench_sound
    (bs : List ((ℕ → V → ℝ) → ℕ → V → ℝ))
    (h : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    benchTrunk (bs ++ [benchResidualBlock 0 h]) x = benchTrunk bs x := by
  rw [benchTrunk_append, benchResidual_zero]

/-- **Obj-инвариант**: ЛЮБОЙ функционал от trunk-выхода — в
частности канонический objective bench (MSE головы над
признаками trunk) — РАВЕН до и после grow. Это congrArg-следствие
`grow_block_bench_sound`: bench-форма obj-непрерывности цепи при
блоковом росте (exact Fraction assert в mini-hagi4). -/
theorem grow_block_obj_invariant {α : Type}
    (f : (ℕ → V → ℝ) → α)
    (bs : List ((ℕ → V → ℝ) → ℕ → V → ℝ))
    (h : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    f (benchTrunk (bs ++ [benchResidualBlock 0 h]) x)
      = f (benchTrunk bs x) :=
  congrArg f (grow_block_bench_sound bs h x)

/-- **Повторяемый grow (C506)**: ДВА identity-добавления подряд
(глубина +2) сохраняют trunk-функцию ТОЧНО — двойное применение
`grow_block_bench_sound`. Это теоретическое ядро повторяемого
grow-цикла mini-hagi5 (несколько grow-событий в одном прогоне).
Вычислительный бюджет цикла (рост знаменателей ~3.2x на grow —
bench-измерение) — свойство носителя, не теорема. -/
theorem grow_blocks_repeat_sound
    (bs : List ((ℕ → V → ℝ) → ℕ → V → ℝ))
    (h1 h2 : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    benchTrunk (bs ++ [benchResidualBlock 0 h1,
                      benchResidualBlock 0 h2]) x = benchTrunk bs x := by
  have h : bs ++ [benchResidualBlock 0 h1,
      benchResidualBlock 0 h2]
      = (bs ++ [benchResidualBlock 0 h1])
        ++ [benchResidualBlock 0 h2] := by simp
  rw [h, grow_block_bench_sound, grow_block_bench_sound]

/-- **Obj-инвариант повторяемого цикла**: любой функционал от
trunk-выхода равен до и после ДВУХ identity-grow подряд (congrArg-
следствие `grow_blocks_repeat_sound`); мини-hagi5 ассертит это
ТОЧНО на каждом событии. -/
theorem grow_blocks_obj_invariant_repeat {α : Type}
    (f : (ℕ → V → ℝ) → α)
    (bs : List ((ℕ → V → ℝ) → ℕ → V → ℝ))
    (h1 h2 : (ℕ → V → ℝ) → ℕ → V → ℝ) (x : ℕ → V → ℝ) :
    f (benchTrunk (bs ++ [benchResidualBlock 0 h1,
                          benchResidualBlock 0 h2]) x)
      = f (benchTrunk bs x) :=
  congrArg f (grow_blocks_repeat_sound bs h1 h2 x)

end Trunk

section Bridge

variable {V : Type} [Fintype V]

/-- Bench-форма и контракт-форма совпадают как ФУНКЦИИ: residual-zero
блок (γ = 0) и `identityBlock` C450 вычисляют один и тот же
результат — тождественное преобразование. Рост bench-trunk'а
residual-zero блоком — это рост `identityBlock`-ом в смысле C450
(`trunk_function_preserving`), в исполнении bench-носителя. -/
theorem bench_bridge_to_C450 (h : (ℕ → V → ℝ) → ℕ → V → ℝ)
    (x : ℕ → V → ℝ) :
    benchResidualBlock 0 h x
      = blockApply identityBlock.toTransformerBlock x := by
  rw [benchResidual_zero, blockApply_identityBlock]

end Bridge

end Hagi.Theory.GrowTrunkBlock

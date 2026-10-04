/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.MergePrice
set_option linter.style.header false

/-!
# R133: T1 NonlinearStep0 — нелинейная step-0 эквивалентность

FORMALIZATION_PLAN §7.1 T1 (P0, закрывает P0-6): R129-алгебра
и существующий `step0_equivalence` (Core) доказаны для
ЛИНЕЙНОГО слоя и голов; реальный merge-блок содержит
per-block RMSNorm, per-head attention, SwiGLU, residual +
BranchScale, zero-init Q-Former — НЕЛИНЕЙНЫЕ модули.

**Ядро T1** (источник 2606.31963: Th.2.1 — максимальная
нативная калибровочная группа RMSNorm = B_d, знаковые
перестановки; Lemma B.2/B.3 — правила трансформации модулей):
класс БЛОКОВО-ЭКВИВАРИАНТНЫХ слоёв замкнут относительно
композиции ⟹ merged(concat) = ансамбль ПО ИНДУКЦИИ ПО
ГЛУБИНЕ.

**Модель:** широкая сеть на блочном пространстве
`Fin N → V`; гейдж-преобразование g — семейство биекций
блоков `Fin N → (V → V)`; слой L гейдж-эквивариантен, если
L ∘ (g-действие) = (g-действие) ∘ L.

**Теоремы:**

* `gauge_equiv_comp` — замыкание класса по композиции
  (индукция по глубине — механизм T1).
* `perBlock_gauge_equiv` — поблочный слой (per-block RMSNorm,
  SwiGLU, per-head структура) эквивариантен, если каждый
  блочный модуль коммутирует со своим гейджем.
* `perBlock_net_blockwise` — сеть из поблочных слоёв действует
  ПОБЛОЧНО: DeepNet(x)_i = DeepExpert_i(x_i) — индукция по
  глубине (нелинейный step-0: merged(concat) = ансамбль).
* `zero_init_identity` — zero-init up-проекция: слой
  x ↦ x + 0 • f(x) — ТОЖДЕСТВО (function-preserving,
  2607.16888/2609.34972).

**Честные границы:** гейдж-коммутация отдельных модулей
(RMSNorm с знаковой группой B_d и т.д.) — measured premises
(правила B.2/B.3 источника); per-head attention как
блочная структура (головы = блоки) — та же схема;
контрпример Prop M.1 (перестановки БЕЗ знаков ухудшают
midpoint-лосс) и более узкая группа LayerNorm (±P) —
в докстринге: знаковая свобода обязательна.
-/

namespace Hagi

variable {N : ℕ} {V : Type*}

/-- Гейдж-действие на блочном пространстве: g-семейство
отображений, действующих поблочно. -/
def blockMap (g : Fin N → (V → V)) (x : Fin N → V) : Fin N → V :=
  fun i => g i (x i)

/-- Гейдж-эквивариантность слоя (коммутация с g-действием). -/
def GaugeEquiv (L : (Fin N → V) → (Fin N → V))
    (g : Fin N → (V → V)) : Prop :=
  ∀ x, L (blockMap g x) = blockMap g (L x)

/-- **Замыкание по композиции**: композиция гейдж-эквивариантных
слоёв гейдж-эквивариантна — индукция по глубине сети
сохраняет эквивариантность (механизм T1). -/
theorem gauge_equiv_comp
    (L1 L2 : (Fin N → V) → (Fin N → V))
    (g : Fin N → (V → V))
    (h1 : GaugeEquiv L1 g) (h2 : GaugeEquiv L2 g) :
    GaugeEquiv (fun x => L1 (L2 x)) g := by
  intro x
  unfold GaugeEquiv at h1 h2
  show L1 (L2 (blockMap g x)) = blockMap g (L1 (L2 x))
  rw [h2 x, h1 (L2 x)]

/-- Поблочный слой: блок i трансформируется модулем ℓ_i
(per-block RMSNorm, SwiGLU, per-head attention-структура). -/
def PerBlockLayer (ℓ : Fin N → (V → V)) :
    (Fin N → V) → (Fin N → V) :=
  fun x i => ℓ i (x i)

/-- **Поблочный слой эквивариантен**, если каждый блочный
модуль коммутирует со своим гейджем (правила B.2/B.3
источника для конкретных модулей — measured premises). -/
theorem perBlock_gauge_equiv (ℓ : Fin N → (V → V))
    (g : Fin N → (V → V))
    (hcomm : ∀ i x, ℓ i (g i x) = g i (ℓ i x)) :
    GaugeEquiv (PerBlockLayer ℓ) g := by
  intro x
  funext i
  simp only [PerBlockLayer, blockMap]
  exact hcomm i (x i)

/-- Сеть: композиция списка слоёв (глубина = длина списка). -/
def DeepNet (layers : List ((Fin N → V) → (Fin N → V))) :
    (Fin N → V) → (Fin N → V) :=
  fun x => layers.foldr (fun L acc => L acc) x

/-- Экспертная подсеть блока: композиция блочных модулей. -/
def DeepNetV (layers : List (V → V)) : V → V :=
  fun x => layers.foldr (fun L acc => L acc) x

/-- **Нелинейный step-0 (T1, ядро)**: сеть из ПОБЛОЧНЫХ слоёв
действует поблочно: выход блока i сети = выходу экспертной
подсети (композиции модулей блока i) на входе блока i —
merged(concat) = ансамбль, ИНДУКЦИЯ ПО ГЛУБИНЕ. Каждый
нелинейный модуль (per-block RMSNorm, SwiGLU, per-head
attention-структура) входит как блочный ℓ_i; эквивариантность
композиции — `gauge_equiv_comp`. -/
theorem perBlock_net_blockwise
    (ℓs : List (Fin N → (V → V))) (x : Fin N → V) (i : Fin N) :
    DeepNet (ℓs.map PerBlockLayer) x i
      = DeepNetV (ℓs.map fun ℓ => ℓ i) (x i) := by
  induction ℓs generalizing x with
  | nil => rfl
  | cons ℓ rest ih =>
      show PerBlockLayer ℓ
        (DeepNet (rest.map PerBlockLayer) x) i
        = ℓ i (DeepNetV (rest.map fun ℓ' => ℓ' i) (x i))
      rw [PerBlockLayer, ih x]

/-- **Zero-init up-проекция — тождество**: слой
x ↦ x + P(0 • f(x)) точно сохраняет функцию
(function-preserving; 2607.16888 / 2609.34972: zero-init
output-проекции включают модуль без изменения поведения —
условие включения Q-Former/новых ветвей на шаге 0). -/
theorem zero_init_identity [AddCommGroup V] [Module ℝ V]
    (f : (Fin N → V) → (Fin N → V))
    (P : ((Fin N → V) →ₗ[ℝ] (Fin N → V))) (x : Fin N → V) :
    (fun y => y + P ((0 : ℝ) • f y)) x = x := by
  simp [zero_smul, map_zero, add_zero]

end Hagi

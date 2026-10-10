/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# NonlinearStep0: нелинейная step-0 эквивалентность

Модель: широкая сеть на блочном пространстве `Fin N → V`;
гейдж-семейство `g : Fin N → (V → V)` действует поблочно
(`blockMap`); слой гейдж-эквивариантен (`GaugeEquiv`), если
коммутирует с этим действием.

* `gauge_equiv_comp` — гейдж-эквивариантные слои замкнуты
  относительно композиции.
* `perBlock_gauge_equiv` — поблочный слой (`PerBlockLayer`)
  эквивариантен, если каждый блочный модуль коммутирует со
  своим гейджем.
* `perBlock_net_blockwise` — сеть из поблочных слоёв действует
  поблочно: `DeepNet (ℓs.map PerBlockLayer) x i =
  DeepNetV (ℓs.map fun ℓ => ℓ i) (x i)`.
* `zero_init_identity` — zero-init up-проекция
  `x ↦ x + P (0 • f x)` — тождество.

Гейдж-коммутация конкретных модулей (RMSNorm и т.п.) —
гипотезы, здесь не доказываются.
-/

namespace Hagi.Core

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

/-- Поблочный слой эквивариантен, если каждый блочный модуль
коммутирует со своим гейджем (`hcomm`). -/
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

/-- Сеть из поблочных слоёв действует поблочно: выход сети в
блоке `i` равен выходу экспертной подсети (композиции модулей
блока `i`) на входе блока `i`. Индукция по глубине. -/
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

/-- Zero-init up-проекция — тождество: слой
`x ↦ x + P (0 • f x)` точно сохраняет вход. -/
theorem zero_init_identity [AddCommGroup V] [Module ℝ V]
    (f : (Fin N → V) → (Fin N → V))
    (P : ((Fin N → V) →ₗ[ℝ] (Fin N → V))) (x : Fin N → V) :
    (fun y => y + P ((0 : ℝ) • f y)) x = x := by
  simp [zero_smul, map_zero, add_zero]

end Hagi.Core

namespace Hagi
export Hagi.Core (blockMap GaugeEquiv gauge_equiv_comp PerBlockLayer perBlock_gauge_equiv DeepNet DeepNetV perBlock_net_blockwise zero_init_identity)
end Hagi

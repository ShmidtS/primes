/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R156: TakeoffElasticity — произведение эластичностей петли

Порт 2609.15802 (Cunningham), абстрактная форма; связка с
ignition-гейтом R124/R138 (Cunningham-форма в GainOperator:
eps_T * eps_gamma >= порога).

Контракт: петля HAGI — цепочка зависимостей (disagreement ->
frontier -> capability -> disagreement). Каждое звено i
имеет эластичность e_i: прирост выхода >= (1 + e_i) *
прирост входа. Тогда произведение эластичностей петли
управляет ростом: prod (1 + e_i) > 1 - самоподдержка
(ускорение), < 1 - затухание.

**Теоремы:**

* `elasticity_chain` — цепочка: x_{t+1} >= (1 + e_t) * x_t
  на горизонте T и все 1 + e_t > 0 ⟹ x_T >= x_0 *
  prod_{t<T} (1 + e_t) (индукция, telescoping);
* `takeoff_elasticity` — САМОПОДДЕРЖКА: произведение
  эластичностей > 1 и x_0 > 0 ⟹ x_T > x_0 (строгий рост по
  всей петле: зажигание Cunningham как пороговая форма);
* `decay_elasticity` — затухание: произведение < 1 и
  монотонная цепочка ⟹ сжатие.

**Честные границы**: эластичности e_t — измеряемые
(h_emp_-слой); теорема НЕ решает, когда произведение > 1 —
это рантайм-измерение (gamma-дефицит ~9x, README).
-/

open Finset Real

namespace Hagi

/-- **Цепочка эластичностей**: пошаговый прирост не меньше
(1 + e_t)-кратного (все множители положительны) ⟹
кумулятивный рост управляется произведением множителей
(telescoping по горизонту). -/
theorem elasticity_chain (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, (1 + e t) * x t ≤ x (t + 1))
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t) :
    x 0 * ∏ t ∈ Finset.range T, (1 + e t) ≤ x T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hmem : ∀ t ∈ Finset.range T, 0 < 1 + e t :=
        fun t ht => hpos t
          (Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (Finset.mem_range.mp ht)))
      have hprod : (0:ℝ)
          < ∏ t ∈ Finset.range T, (1 + e t) :=
        Finset.prod_pos fun t ht => hmem t ht
      have hih := ih hmem
      have hs := hstep T
      rw [Finset.prod_range_succ]
      calc x 0 * ((∏ t ∈ Finset.range T, (1 + e t)) * (1 + e T))
          = (x 0 * ∏ t ∈ Finset.range T, (1 + e t)) * (1 + e T) := by
              ring
        _ ≤ x T * (1 + e T) := mul_le_mul_of_nonneg_right hih
              (le_of_lt (hpos T (Finset.mem_range.mpr (by omega))))
        _ = (1 + e T) * x T := mul_comm _ _
        _ ≤ x (T + 1) := hs

/-- **Самоподдержка (Cunningham-зажигание)**: произведение
эластичностей петли > 1 и положительный старт ⟹ строгий
рост на любом горизонте T >= 1: петля ускоряет сама себя. -/
theorem takeoff_elasticity (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, (1 + e t) * x t ≤ x (t + 1))
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t)
    (hprod : 1 < ∏ t ∈ Finset.range T, (1 + e t))
    (hx0 : 0 < x 0) :
    x 0 < x T := by
  have hchain := elasticity_chain x e T hstep hpos
  have hstrict : x 0 < x 0 * ∏ t ∈ Finset.range T, (1 + e t) := by
    nlinarith [hx0, hprod]
  linarith

/-- **Затухание**: верхняя цепочка x_{t+1} <= (1 + e_t) x_t
с положительными множителями и произведением < 1 при
x_0 > 0 ⟹ строгий спад x_T < x_0 (петля гасит себя —
«нет зажигания», R124-порог не пройден). -/
theorem decay_elasticity (x : ℕ → ℝ) (e : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t, x (t + 1) ≤ (1 + e t) * x t)
    (hpos : ∀ t ∈ Finset.range T, 0 < 1 + e t)
    (hx0 : 0 < x 0)
    (hprod : ∏ t ∈ Finset.range T, (1 + e t) < 1) :
    x T < x 0 := by
  have hmain : ∀ K : ℕ, K ≤ T →
      x K ≤ x 0 * ∏ t ∈ Finset.range K, (1 + e t) := by
    intro K
    induction K with
    | zero => intro _; simp
    | succ K ih =>
        intro hle
        have hs := hstep K
        have hpK : (0:ℝ) ≤ 1 + e K :=
          le_of_lt (hpos K (Finset.mem_range.mpr (by omega)))
        have hmul : (1 + e K) * x K
            ≤ (1 + e K) * (x 0 * ∏ t ∈ Finset.range K, (1 + e t)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hpK
        rw [Finset.prod_range_succ]
        linarith [hs, hmul]
  have hbound := hmain T (le_refl T)
  nlinarith

end Hagi

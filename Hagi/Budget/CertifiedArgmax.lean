/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# (§AW): CertifiedArgmax — легитимность argmax на
# Γ-оценках ComputeBudget

Рабочий список 2026-10-04, §5.2: выбор argmax Γ_i/K_i в
бюджетном распределении ЛЕГИТИМЕН только когда сертифицирован
зазор Γ̂_i − Γ̂_j > 2ε_Γ (split-half брекет ε_Γ); при зазоре
внутри 2ε_Γ — случайный выбор (никакой вывод о истинном
argmax невозможен: обе конфигурации измерения согласованы с
данными).

**Теоремы:**

* `argmax_pair_certified` — попарная форма: при
  |Γ̂ k − Γ k| ≤ ε_Γ для всех k и зазоре Γ̂ i − Γ̂ j > 2ε_Γ
  следует Γ i > Γ j (истинное упорядочение);
* `argmax_select_certified` — селекция: если sel максимизирует
  Γ̂ И отделён от каждого конкурента более чем на 2ε_Γ, то
  sel максимизирует истинное Γ;
* argmax_tie_random — ПОЛИТИКА (def, не теорема):
  `RequiresRandomSplit` — зазор ≤ 2ε_Γ ⟹ выбор случайный
  (обоснование: две конфигурации Γ, Γ' обе согласованы с
  измерением Γ̂ в пределах ε_Γ, но меняют argmax —
  контрпример-конструкция `tie_ambiguity`).

ε_Γ — измеряемая посылка (split-half / h_emp_-слой).
-/

open Finset

namespace Hagi.Budget

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Попарная сертификация: зазор > 2ε_Γ при точности ε_Γ
восстанавливает истинное упорядочение Γ. -/
theorem argmax_pair_certified (Gamma GammaHat : I → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hacc : ∀ k, |GammaHat k - Gamma k| ≤ eps)
    (i j : I) (hgap : 2 * eps < GammaHat i - GammaHat j) :
    Gamma j < Gamma i := by
  have h1 := hacc i
  have h2 := hacc j
  have h3 : GammaHat i - eps ≤ Gamma i := by
    rw [abs_sub_comm] at h1
    rw [abs_le] at h1
    linarith
  have h4 : Gamma j ≤ GammaHat j + eps := by
    rw [abs_le] at h2
    linarith
  linarith

/-- Селекционная сертификация: максимайзер измерения с
зазором > 2ε_Γ от каждого конкурента — истинный максимайзер. -/
theorem argmax_select_certified (Gamma GammaHat : I → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hacc : ∀ k, |GammaHat k - Gamma k| ≤ eps)
    (sel : I)
    (hsel : ∀ k, GammaHat k ≤ GammaHat sel)
    (hsep : ∀ k, sel ≠ k → 2 * eps < GammaHat sel - GammaHat k) :
    ∀ k, Gamma k ≤ Gamma sel := by
  intro k
  by_cases hk : k = sel
  · rw [hk]
  · have hgt := argmax_pair_certified Gamma GammaHat eps heps hacc sel k
      (hsep k (fun h => hk h.symm))
    exact le_of_lt hgt

/-- Политика случайного выбора при несертифицированном зазоре
(2ε_Γ-брекет не выполнен): argmax НЕ легитимен. -/
def RequiresRandomSplit (GammaHat : I → ℝ) (eps : ℝ) (i j : I) : Prop :=
  GammaHat i - GammaHat j ≤ 2 * eps

/-- **Неоднозначность при несертифицированном зазоре**
(контрпример-конструкция): зазор Γ̂ i − Γ̂ j = 2ε − δ ≤ 2ε
допускает ДВЕ конфигурации истинных Γ, обе согласованные с
измерением в пределах ε, но с ПРОТИВОПОЛОЖНЫМ argmax
(Γᴬ: argmax = true; Γᴮ: argmax = false) — argmax по Γ̂ не
несёт информации об истинном argmax. Политика
`RequiresRandomSplit` обоснована. -/
theorem tie_ambiguity (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta) (hdelta2 : delta < 2 * eps) :
    ∃ GammaA GammaB GammaHat : Bool → ℝ,
      (∀ k, |GammaHat k - GammaA k| ≤ eps)
        ∧ (∀ k, |GammaHat k - GammaB k| ≤ eps)
        ∧ RequiresRandomSplit GammaHat eps true false
        ∧ GammaB true < GammaB false
        ∧ GammaA false < GammaA true := by
  refine ⟨(fun b => if b then eps else delta - eps),
    (fun b => if b then -eps else delta - eps),
    (fun b => if b then 0 else -(2 * eps - delta)), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  · intro k
    cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  · unfold RequiresRandomSplit
    simp
    linarith
  · simp
    linarith
  · simp
    linarith

end Hagi.Budget

namespace Hagi
export Hagi.Budget (argmax_pair_certified argmax_select_certified RequiresRandomSplit tie_ambiguity)
end Hagi

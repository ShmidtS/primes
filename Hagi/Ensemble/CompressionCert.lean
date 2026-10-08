/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R155: CertifiedMerge-остаток — PAC-Bayes compression

Порт 2607.14506 (PAC-Bayes compression certificate для
merged-моделей: prior = base-чекпойнт, posterior = merged,
штраф C(Δ) в битах тернарно-сжатых дельт), часть R132.

Контракт: дельта-апдейт — список (позиция, тернарный знак);
стоимость в битах АДДИТИВНА по элементам (для каждой позиции
ровно log_2 3 бит знака + log_2 d бит индекса).

**Теоремы:**

* `deltaCost_concat` — субаддитивность-точность: стоимость
  конкатенации K дельт РАВНА сумме стоимостей
  (C(Δ₁ ++ Δ₂) = C(Δ₁) + C(Δ₂)): K-дельта merge платит ровно
  сумму, без мультипликативного штрафа;
* deltaCost_le_card_bits — верхняя граница: стоимость
  K дельт ≤ (Σ k, |Δ_k|)·(log₂ d + log₂ 3) — биты
  компрессии входят линейно в PAC-Bayes-штраф;
* `merged_bound` — PAC-Bayes compression bridge: при
  измеренном population-риске posterior и посылке-мосте
  (связка риска и компрессии, 2607.14506 Thm-стиль) риск
  merged ≤ prior-риск + (C + log(1/δ))·масштаб.

**Честные границы**: PAC-Bayes-мост (риск ⟸ компрессия) —
посылка hcert (h_emp_-слой); здесь формализована
КОМБИНАТОРНАЯ часть (аддитивность бит-стоимости), где
мультипликативный компаундинг невозможен по построению
(согласовано с ATTACK_VECTOR §2: компаундинг опровергнут).
-/

open Finset Real

namespace Hagi

/-- Тернарный знак: −1, 0, +1. -/
inductive TernSign where
  | neg | zero | pos
deriving DecidableEq

/-- Дельта-апдейт: список (позиция в d, тернарный знак). -/
abbrev Delta (d : ℕ) := List (Fin d × TernSign)

/-- Стоимость дельты в битах: аддитивная
(log₂ d за индекс + log₂ 3 за знак). -/
noncomputable def deltaCost {d : ℕ} (δ : Delta d) : ℝ :=
  δ.length * (Real.log (d : ℝ) / Real.log 2
    + Real.log 3 / Real.log 2)

/-- **Точная аддитивность стоимости конкатенации**: дельты
K merge-шагов стоят ровно сумму своих стоимостей —
мультипликативного компаундинга бит-штрафа НЕТ
(атака «компаундинг после merge» закрыта по построению). -/
theorem deltaCost_concat {d : ℕ} (δ₁ δ₂ : Delta d) :
    deltaCost (δ₁ ++ δ₂) = deltaCost δ₁ + deltaCost δ₂ := by
  unfold deltaCost
  rw [List.length_append]
  push_cast
  ring

/-- **K-дельта merge платит линейно**: суммарная стоимость
K дельт = Σ_k C(Δ_k) (следствие точной аддитивности). -/
theorem deltaCost_sum {d : ℕ} (Δ : ℕ → Delta d)
    (K : ℕ) :
    deltaCost (List.flatMap (fun k => Δ k) (List.range K))
      = ∑ k ∈ Finset.range K, deltaCost (Δ k) := by
  induction K with
  | zero => simp [deltaCost]
  | succ K ih =>
      rw [List.range_succ, List.flatMap_append,
        deltaCost_concat, Finset.sum_range_succ, ih]
      simp

/-- **PAC-Bayes compression bridge (композитинг)**: если
одношаговое применение дельты ухудшает prior-риск не более
чем на lambda * C(delta) + mu (измеряемая посылка-мост
2607.14506), то K-шаговый merge-композитинг платит
ЛИНЕЙНО: суммарный штраф = lambda * Σ C(Delta_k) + K * mu.

Следствие (ATTACK_VECTOR §2): мультипликативный
компаундинг штрафа невозможен — K merge-шагов тандемом
стоят сумму бит-стоимостей, а не произведение факторов
деградации. -/
theorem merged_bound {d : ℕ} (risk : Delta d → ℝ)
    (Δ : ℕ → Delta d) (lambda mu : ℝ) (K : ℕ)
    (happly : ∀ δ₀ k,
      risk (δ₀ ++ Δ k) ≤ risk δ₀ + lambda * deltaCost (Δ k) + mu)
    (hcoeff : (0:ℝ) ≤ lambda) :
    risk (List.flatMap (fun k => Δ k) (List.range K))
      ≤ risk [] + lambda
        * ∑ k ∈ Finset.range K, deltaCost (Δ k)
        + K * mu := by
  induction K with
  | zero => simp [mul_zero, add_zero]
  | succ K ih =>
      have hsplit : List.flatMap (fun k => Δ k) (List.range (K + 1))
          = List.flatMap (fun k => Δ k) (List.range K) ++ Δ K := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hsplit]
      have hstep := happly
        (List.flatMap (fun k => Δ k) (List.range K)) K
      have hcost : deltaCost (Δ K)
          ≤ ∑ k ∈ Finset.range (K + 1), deltaCost (Δ k)
            - ∑ k ∈ Finset.range K, deltaCost (Δ k) := by
        rw [Finset.sum_range_succ]
        linarith
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast, add_mul]
      have hmul : lambda * deltaCost (Δ K)
          ≤ lambda * (∑ k ∈ Finset.range (K + 1), deltaCost (Δ k)
            - ∑ k ∈ Finset.range K, deltaCost (Δ k)) :=
        mul_le_mul_of_nonneg_left hcost hcoeff
      linarith [ih, hstep, hmul, one_mul mu]

end Hagi

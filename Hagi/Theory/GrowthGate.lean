/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 authors
-/

import Hagi.Theory.NegativeTransfer

/-!
# GrowthGate — certified-гейт ёмкости: когда рост оправдан (C632)

Новая эра (roadmap C631 top-1): rank/adapter-ёмкость. Аналогия
transfer-гейта (C601 bench / C577 `autoGate`): рост ёмкости
(rank+1 / adapter-add) допустим ⟺ certified-выигрыш покрывает
стоимость. Модель: текущая модель M_r (rank r) дообучается
градиентно на residual; при L-smooth и градиентной G-границе
guaranteed per-step drop равен `G²/(2L)` при оптимальном шаге
γ* = 1/L (C606 `nl_drop_optimal`) ⇒ за n шагов возможное
убывание objective ≤ `n·G²/(2L)` (`nl_drop_total`). Стоимость
добавления ёмкости — scalar `c_add` (параметры/вычисления).

- `growthGate (potentialBound cAdd : ℚ) : Bool` — grow ⟺
  potentialBound > c_add (равенство → stay: budget-приоритет
  меньшей ёмкости, паттерн C535 `rankSelect`);
- `growth_gate_stay_char` — гейт совпадает с порогом
  (детерминизм тотального порядка ℚ);
- `growth_gate_sound` (MAIN) — CERTIFIED-STAY: если
  `n·G²/(2L) ≤ c_add`, то ЛЮБОЕ n-шаговое дообучение (в т.ч. с
  добавленной ёмкостью: её выигрыш ≤ выигрышу дообучения того же
  budget-класса границ G, L) уменьшает objective не более чем на
  `c_add` — рост НЕ может окупиться за n шагов.

Отличия от прецедентов: C535 — селектор ранга 1 vs 2 по измеренным
probe-score (выбор режима); здесь — решение «расти/нет» по
ФОРМУЛЬНОЙ границе теории против cost-модели, до всякого probe.
C601/C577 — сравнение двух измеренных probe-прогонов; здесь —
ноль измерений: чистая theory-граница (C606) + scalar cost.

## Honest pins (что этот модуль НЕ покрывает)

- **Потенциал-модель — квадратичный класс** (`hmodel`):
  равенство в descent-лемме (прецедент C572: точная теория — в
  квадратичном мире). Для ОБЩЕГО L-smooth non-quadratic objective
  certified-потолок per-step drop шире — форма `nlBudget` C592
  `γG² + Lγ²G²/2` (= 3G²/(2L) при γ = 1/L); там гейт нужно
  пересчитывать с этой более широкой границей.
- **Grow-ветка = разрешение, НЕ обещание**:
  `growthGate = true` разрешает рост, но НЕ обещает выигрыша:
  `n·G²/(2L)` — ВЕРХНЯЯ граница возможного drop, не факт;
  реальный выигрыш может быть нулевым
  (напр. grad = 0 вдоль всей траектории). Sound-гарантия есть
  ТОЛЬКО у stay-ветки — асимметрия честна и отражена в форме
  теорем. Граница G — градиентная граница ТЕКУЩЕЙ модели на
  residual: если модель роста имеет больший G, bound пересчитывается
  и гейт честно решает заново (гейт — функция констант, паттерн
  детерминизма C535).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.GrowthGate

open scoped InnerProductSpace
open Hagi.Theory.NegativeTransfer

/-! ## Детерминированный ℚ-гейт ёмкости -/

/-- **growthGate (C632, def)**: решение grow/stay по формульной
границе — рост оправдан ⟺ potential-bound (n·G²/(2L), C606)
СТРОГО больше стоимости c_add. Равенство → stay (budget-приоритет
меньшей ёмкости, паттерн C535 `rankSelect`; тотальный порядок ℚ
делает сравнение детерминированным — повторный вызов на тех же
константах даёт тот же ответ). -/
def growthGate (potentialBound cAdd : ℚ) : Bool :=
  decide (cAdd < potentialBound)

/-- **growth_gate_stay_char (C632)**: stay-ветка гейта — в точности
порог «bound ≤ cost»: гейт не добавляет и не теряет информации
относительно сравнения чисел (детерминизм, no hidden state). -/
theorem growth_gate_stay_char (pb c : ℚ) :
    growthGate pb c = false ↔ pb ≤ c := by
  unfold growthGate
  by_cases h : c < pb
  · rw [decide_eq_true h]
    simpa using h
  · push Not at h
    have hd : (decide (c < pb) : Bool) = false := by
      have hn : ¬ (c < pb) := by push Not; linarith
      simp [hn]
    simp [hd, h]

/-! ## n-шаговая certified-граница возможного выигрыша

Модель потенциала: КВАДРАТИЧНЫЙ класс (прецедент C572: там
точная iff-теория живёт в квадратичном мире; честный pin ниже).
hmodel — точная форма потенциала на оптимальном шаге: drop за
один γ*=1/L-шаг РАВЕН `‖grad x‖²/(2L)` (для f = (L/2)·quadObj —
равенство в descent-лемме; guaranteed-drop C606 `G²/(2L)` —
значение этой же формы на границе G). -/

section TotalDrop

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **nl_drop_step_eq (C632, a)**: per-step guaranteed drop при
оптимальном шаге γ* = 1/L для ЛЮБОГО значения градиента x —
поточечная форма `nl_drop_optimal` (C606: x = G). -/
theorem nl_drop_step_eq {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    nlDrop (1 / L) L x = x ^ 2 / (2 * L) := by
  unfold nlDrop
  field_simp
  ring

/-- **nl_drop_total (C632, b)**: телескоп-индукция — в квадратичной
потенциальной модели (hmodel: drop одного γ*=1/L-шага ТОЧНО равен
`‖grad‖²/(2L)`, descent-лемма без зазора) n шагов уменьшают
objective ровно на `Σ‖grad_k‖²/(2L)` и потому НЕ БОЛЕЕ чем на
`n·G²/(2L)` — certified-потолок возможного выигрыша n-шагового
дообучения (per-step drop ≤ потолка C606 `nl_drop_optimal`). -/
theorem nl_drop_total (f : E → ℝ) (grad : E → E) (L G : ℝ)
    (hL : 0 < L) (n : ℕ) (z : E)
    (hmodel : ∀ x : E, f (nlStep (1 / L) grad x)
      = f x - ‖grad x‖ ^ 2 / (2 * L))
    (hG : ∀ k, k ≤ n → ‖grad (nlRun k (1 / L) grad z)‖ ≤ G) :
    f z - f (nlRun n (1 / L) grad z) ≤ n * (G ^ 2 / (2 * L)) := by
  revert hG
  induction n generalizing z with
  | zero => intro _; simp [nlRun]
  | succ n ih =>
      intro hG
      have hstep := hmodel z
      have hgz : ‖grad z‖ ≤ G := by
        have h0 : nlRun 0 (1 / L) grad z = z := by simp [nlRun]
        rw [← h0]
        exact hG 0 (by omega)
      have hsq : ‖grad z‖ ^ 2 ≤ G ^ 2 := by
        have h6 := mul_self_le_mul_self (norm_nonneg _) hgz
        nlinarith [h6]
      have hdrop : f z - f (nlStep (1 / L) grad z)
          ≤ G ^ 2 / (2 * L) := by
        rw [hstep]
        have hpos : (2 * L : ℝ) > 0 := by positivity
        have hdiv : ‖grad z‖ ^ 2 / (2 * L) ≤ G ^ 2 / (2 * L) := by
          gcongr
        linarith
      have hG' : ∀ k, k ≤ n →
          ‖grad (nlRun k (1 / L) grad (nlStep (1 / L) grad z))‖ ≤ G := by
        intro k hk
        have h3 : nlRun k (1 / L) grad (nlStep (1 / L) grad z)
            = nlRun (k + 1) (1 / L) grad z := by
          unfold nlRun
          rw [Function.iterate_succ]
          rfl
        rw [h3]
        exact hG (k + 1) (by omega)
      have hih := @ih (nlStep (1 / L) grad z) hG'
      have heq : nlRun (n + 1) (1 / L) grad z
          = nlRun n (1 / L) grad (nlStep (1 / L) grad z) := by
        unfold nlRun
        exact Function.iterate_succ_apply _ _ _
      rw [heq]
      push_cast
      nlinarith [hdrop, hih]

end TotalDrop

/-! ## Certified-stay (sound-ветка гейта) -/

/-- **growth_gate_sound (C632, MAIN — certified stay)**: если
потолок возможного выигрыша n-шагового дообучения `n·G²/(2L)`
НЕ превышает стоимость добавления ёмкости `c_add`, то ЛЮБОЕ
такое дообучение уменьшает objective не более чем на `c_add` —
рост ёмкости НЕ может окупиться за n шагов: stay-решение гейта
certified (композиция `nl_drop_total` с cost-порогом). Grow-ветка
честно НЕ гарантирует ничего: bound — верхняя граница возможного,
не факт (см. honest pins модуля). -/
theorem growth_gate_sound {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L G : ℝ)
    (hL : 0 < L) (n : ℕ) (z : E) (cAdd : ℝ)
    (hmodel : ∀ x : E, f (nlStep (1 / L) grad x)
      = f x - ‖grad x‖ ^ 2 / (2 * L))
    (hG : ∀ k, k ≤ n → ‖grad (nlRun k (1 / L) grad z)‖ ≤ G)
    (hc : n * (G ^ 2 / (2 * L)) ≤ cAdd) :
    f z - f (nlRun n (1 / L) grad z) ≤ cAdd :=
  le_trans (nl_drop_total f grad L G hL n z hmodel hG) hc

end Hagi.Theory.GrowthGate

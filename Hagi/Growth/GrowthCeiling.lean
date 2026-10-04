/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.Saturation
set_option linter.style.header false

/-!
# R151: GrowthCeiling — дихотомия стационарности для F3-петли

Порт 2609.34924 ("Audit the Scaffold, Not the Checkpoint: A
Stationarity Dichotomy for Recursive Self-Improvement"),
в абстрактной потенциальной форме (honest-граница: измеряемая
стационарность V и бюджет расширения b — посылки, см.
докстринги ниже).

Контракт: пошаговый potential-сертификат

  V(t+1) <= V(t) - eps_t + b_t,

где eps_t >= 0 — edge шага (прирост над лучшим фиксированным
конкурентом ЗАМОРОЖЕННОГО класса гипотез), V_t >= 0 —
measurement-budget/variation potential (аналог Ville/Hedge:
конечная стационарность scaffold-аудита), b_t >= 0 — бюджет
СОБЫТИЯ РАСШИРЕНИЯ класса (новая ширина/биты/домен: добавление
листа, домена, разрядности).

**Теоремы:**

* `potential_telescope` — V(T) <= V(0) - Σε + Σb и
  `edge_total_bound`: Σ_{t<T} ε_t <= V(0) + Σ_{t<T} b_t.
* `frozen_saturation` — замороженный класс (b = 0):
  суммарный edge любого ОКНА длины k ограничен V(0)
  (сатурация: устойчивый поток η_t → 0 в агрегате);
* `expansion_required` — устойчивый edge (кумулятивно ≥ G на
  всех горизонтах) ТРЕБУЕТ событий расширения:
  Σ_{t<T} b_t >= G - V(0);
* `growth_dichotomy` — либо бюджет расширения неограничен,
  либо суммарный edge ограничен (дихотомия сатурации).

**Честные границы**: стационарность V и бюджет b — измеряемые
посылки (h_emp_-слой рантайма); дихотомия НЕ говорит, КАКОЕ
расширение окупается — только что «бесплатного» устойчивого
роста в замороженном классе не существует.
-/

open Finset Real

namespace Hagi

/-- Телескоп potential-сертификата: из пошагового
V(t+1) <= V(t) - eps_t + b_t и ограниченности V снизу -
кумулятивный edge ограничен начальным потенциалом плюс
бюджет расширений. -/
theorem potential_telescope (V eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    V T + ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hs := hstep T
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hΔ : V (T + 1) + eps T ≤ V T + b T := by linarith
      linarith

/-- **Ограничение суммарного edge**: Σ_{t<T} eps_t <= V(0)
+ Σ_{t<T} b_t — рост не «бесплатный»: каждый_nat прирост
оплачен потенциалом или расширением класса. -/
theorem edge_total_bound (V eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t := by
  have := potential_telescope V eps b T hVnn hstep
  linarith [hVnn T]

/-- **Сатурация замороженного класса**: при b = 0 (никаких
событий расширения) суммарный edge любого ОКНА [m, T)
ограничен потенциалом в начале окна: устойчивый поток
приростов обязан затухать в агрегате («eta_t -> 0» по
Чезаро на любом суффиксном окне). -/
theorem frozen_saturation (V eps : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t) :
    ∀ m ≤ T, ∑ t ∈ Finset.Ico m T, eps t ≤ V m := by
  intro m hm
  have hkey : ∀ k : ℕ, m + k ≤ T →
      V (m + k) + ∑ t ∈ Finset.range k, eps (m + t) ≤ V m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have hs := hstep (m + k)
        have hshift : m + (k + 1) = (m + k) + 1 := by omega
        rw [hshift, Finset.sum_range_succ]
        have hΔ : V ((m + k) + 1) + eps (m + k) ≤ V (m + k) := by
          linarith
        have hih := ih (by omega)
        linarith
  have hk := hkey (T - m) (by omega)
  have hconv : m + (T - m) = T := by omega
  rw [hconv] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  linarith [hVnn T, hk]

/-- **Устойчивый edge требует расширения класса**: если
кумулятивный edge не ниже G на КАЖДОМ горизонте T
(устойчивое самоподдерживающееся улучшение), то бюджет
событий расширения на каждом горизонте не меньше G - V(0):
«бесплатного» устойчивого роста в замороженном классе нет. -/
theorem expansion_required (V eps b : ℕ → ℝ) (G : ℝ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t)
    (hsustained : ∀ T : ℕ, G ≤ ∑ t ∈ Finset.range T, eps t)
    (T : ℕ) :
    G - V 0 ≤ ∑ t ∈ Finset.range T, b t := by
  have hb := edge_total_bound V eps b T hVnn hstep
  linarith [hsustained T]

/-- **Дихотомия сатурации** (порт 2609.34924, абстрактная
форма): для F3-петли с potential-сертификатом верно ровно
одно из двух (дизъюнкция конструктивна):

- ЛИБО бюджет расширений неограничен (∀ B ∃ T: B < Σ b_t —
  события расширения класса происходят вечно: ширина/биты/
  домены растут неограниченно);
- ЛИБО суммарный edge ограничен (∃ B ∀ T: Σ eps_t ≤ V(0) + B
  — рост сатурирует: вместе с `frozen_saturation` это
  затухание eta_t в агрегате на любом окне).

Совместно с `expansion_required`: устойчивый edge уровня
G > V(0) + B при бюджете ≤ B невозможен — «бесплатного»
устойчивого роста в замороженном классе не существует. -/
theorem growth_dichotomy (V eps b : ℕ → ℝ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t, V (t + 1) ≤ V t - eps t + b t) :
    (∀ B : ℝ, ∃ T : ℕ, B < ∑ t ∈ Finset.range T, b t)
      ∨ (∃ B : ℝ, ∀ T : ℕ,
          ∑ t ∈ Finset.range T, eps t ≤ V 0 + B) := by
  by_cases hB : ∃ B : ℝ, ∀ T : ℕ,
      ∑ t ∈ Finset.range T, b t ≤ B
  · right
    obtain ⟨B, hB⟩ := hB
    refine ⟨V 0 + B, fun T => ?_⟩
    have h := edge_total_bound V eps b T hVnn hstep
    have hbT := hB T
    linarith [h, hbT, hVnn 0]
  · left
    intro B
    by_contra hcon
    push_neg at hcon
    exact absurd ⟨B, hcon⟩ hB


end Hagi

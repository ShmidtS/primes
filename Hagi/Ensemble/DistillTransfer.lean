/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.Distill
set_option linter.style.header false

/-!
# R134: T3 DistillTransfer — реальный оператор T (замена R130)

FORMALIZATION_PLAN §7.1 T3 (P0): ревизия объявила GainOperator
(R130) промежуточным — η-метрика безразмерно смешивала
энергию весов и наты. Здесь — дистилл-канал в НАТАХ:

  CE_q(θ) − CE_q(E) ≤ KL(p_E‖p_θ) + M·‖q − p_E‖₁
  при |log(p_E/p_θ)| ≤ M (pointwise),

где E — учитель (ансамбль листьев), θ — студент (merged),
q — данные. Измеримый КПД: η = (CE_leafmean − CE_student)/
twoGap — в натах на единицу зазора ансамбля, без метрического
смешения.

**Теоремы:**

* `distill_kl_bridge` — KL-мост (ядро T3): проигрыш студента
  против учителя на ДАННЫХ ограничен KL-расхождением
  распределений плюс член уклонения данных от учителя,
  линейный по ‖q−p_E‖₁ с константой M (граница отношения
  логарифмов). Второй член может превысить 0.05 нат (план) →
  data-anchored таргет или second-order оценка.
* `distill_efficiency_pos` — КПД канала η > 0 ⟺ студент
  лучше среднего листьев: сертифицированный измеримый гейт
  оператора T (замена γ_eff из R130).
* `forward_kl_target` / `reverse_kl_target` — closed-form
  цели дистилляции (2609.38666): forward KL → взвешенная
  арифметическая смесь учителей (сохраняет вклад каждого
  эксперта — универсальность); reverse KL → нормализованное
  геометрическое среднее (misleading teacher подавляет
  верные ответы — модность). Выбор направления KL = выбор
  между универсальностью и модностью (докстринг).

**Честные границы:** cold-start collapse reverse-KL
(2607.16955: свежий студент ~нулевая масса → ваншинг-градиент;
merged-студент разделяет поддержку с листьями — риск ниже,
но on-policy фаза нужна); distillation floor (2607.15467:
argmax передаёт минимум, избыточен только dark knowledge);
Õ(log T) regret обеих сторон (2609.38666).
-/

open Finset

namespace Hagi

variable {V : Type*} [Fintype V]

/-- ‖·‖₁-норма уклонения (Σ |·|). -/
noncomputable def l1Norm (d : V → ℝ) : ℝ := ∑ v, |d v|

/-- **KL-мост (T3, ядро)**: проигрыш студента θ против учителя
E на данных q ограничен

  CE_q(θ) − CE_q(E) ≤ KL(p_E‖p_θ) + M·‖q − p_E‖₁

при pointwise |log(p_E/p_θ)| ≤ M. Перегруппировка:
разность CE = KL(p_E‖p_θ) + Σ(q−p_E)·(log p_E − log p_θ);
второй член ограничен M·‖q−p_E‖₁ треугольником. -/
theorem distill_kl_bridge (q pE pθ : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hE : ∀ v, 0 < pE v) (hθ : ∀ v, 0 < pθ v)
    (M : ℝ) (hM : ∀ v, |Real.log (pE v / pθ v)| ≤ M) :
    crossEntropy q pθ - crossEntropy q pE
      ≤ klDiv pE pθ + M * l1Norm (fun v => q v - pE v) := by
  -- разложение логарифма отношения
  have hlogsplit : ∀ v, Real.log (pE v / pθ v)
      = Real.log (pE v) - Real.log (pθ v) := by
    intro v
    exact Real.log_div (hE v).ne' (hθ v).ne'
  -- ключевая перегруппировка:
  -- CE_q(θ) − CE_q(E) = Σ q·(log pE − log pθ)
  --   = Σ pE·(log pE − log pθ) + Σ (q−pE)·(log pE − log pθ)
  --   = KL(pE‖pθ) + Σ (q−pE)·(log pE − log pθ)
  have hmain : crossEntropy q pθ - crossEntropy q pE
      = ∑ v, q v * (Real.log (pE v) - Real.log (pθ v)) := by
    unfold crossEntropy
    rw [neg_sub_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hsplit : ∑ v, q v * (Real.log (pE v) - Real.log (pθ v))
      = ∑ v, pE v * Real.log (pE v / pθ v)
        + ∑ v, (q v - pE v) * (Real.log (pE v) - Real.log (pθ v)) := by
    have hper : ∀ v, q v * (Real.log (pE v) - Real.log (pθ v))
        = pE v * Real.log (pE v / pθ v)
          + (q v - pE v) * (Real.log (pE v) - Real.log (pθ v)) := by
      intro v
      rw [hlogsplit v]
      ring
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hper v
  rw [hmain, hsplit]
  -- KL-часть
  have hkl : klDiv pE pθ = ∑ v, pE v * Real.log (pE v / pθ v) := rfl
  rw [hkl]
  -- второй член: |Σ (q−pE)·(log-ratio)| ≤ M·‖q−pE‖₁
  have hbound : ∑ v, (q v - pE v) * (Real.log (pE v) - Real.log (pθ v))
      ≤ M * l1Norm (fun v => q v - pE v) := by
    have htri : ∑ v, (q v - pE v) * (Real.log (pE v) - Real.log (pθ v))
        ≤ ∑ v, |(q v - pE v) * (Real.log (pE v / pθ v))| :=
      le_trans (le_of_eq (Finset.sum_congr rfl fun v _ => by
        rw [hlogsplit v]))
        (Finset.sum_le_sum fun v _ => le_abs_self _)
    have hper2 : ∀ v, |(q v - pE v) * Real.log (pE v / pθ v)|
        ≤ |q v - pE v| * M := by
      intro v
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM v) (abs_nonneg _)
    calc ∑ v, (q v - pE v) * (Real.log (pE v) - Real.log (pθ v))
        ≤ ∑ v, |(q v - pE v) * (Real.log (pE v / pθ v))| := htri
      _ ≤ ∑ v, |q v - pE v| * M :=
          Finset.sum_le_sum fun v _ => hper2 v
      _ = M * l1Norm (fun v => q v - pE v) := by
          rw [l1Norm, ← Finset.sum_mul]
          exact mul_comm _ _
  linarith [hbound]

/-- Измеримый КПД дистилл-канала: η в НАТАХ на единицу зазора
ансамбля (замена безразмерного γ_eff R130 по ревизии T3). -/
noncomputable def distillEfficiency (ceLeafmean ceStudent twoGap : ℝ) :
    ℝ := (ceLeafmean - ceStudent) / twoGap

/-- **КПД положителен ⟺ студент лучше среднего листьев**:
сертифицированный гейт оператора T — при η > 0 дистилл-канал
реально поднимает capability (перенос > компромисса). -/
theorem distill_efficiency_pos {ceLeafmean ceStudent twoGap : ℝ}
    (hgap : 0 < twoGap) :
    0 < distillEfficiency ceLeafmean ceStudent twoGap
      ↔ ceStudent < ceLeafmean := by
  constructor
  · intro h
    unfold distillEfficiency at h
    rcases div_pos_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · linarith
    · exact absurd hgap (by linarith)
  · intro h
    unfold distillEfficiency
    exact div_pos (by linarith) hgap

/-- Closed-form цель forward-KL (2609.38666): взвешенная
арифметическая смесь учителей — сохраняет вклад каждого
эксперта (универсальность). -/
noncomputable def forwardKlTarget {N : ℕ} (w : Fin N → ℝ)
    (ps : Fin N → (V → ℝ)) : V → ℝ :=
  fun v => ∑ k, w k * ps k v

/-- Closed-form цель reverse-KL (2609.38666): нормализованное
геометрическое среднее учителей — misleading teacher
подавляет верные ответы (модность); cold-start collapse
(2607.16955) — см. докстринг модуля. -/
noncomputable def reverseKlTarget {N : ℕ} (w : Fin N → ℝ)
    (ps : Fin N → (V → ℝ)) : V → ℝ :=
  fun v => (∏ k, (ps k v) ^ (w k))
    / (∑ v', ∏ k, (ps k v') ^ (w k))

end Hagi

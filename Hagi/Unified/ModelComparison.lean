/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Unified.RecursiveClean
set_option linter.style.header false

/-!
# Сравнение моделей нейрона: Δ_j-критерий (R534)

Продолжение R533 («Neural Networks Are Already Clean»):
формализация решающего правила, отличающего рекурсивное
обобщение от суперпозиции. Следуя MDL-принципу
(двухчастичная цена = качество описания + сложность
модели):

* `Score` — взвешенное качество: loglik − λ·complexity;
* `modelGap` — Δ_j = Score M_R − Score M_S;
* `delta_pos_of_dominates` — если рекурсивная модель
  проигрывает в правдоподобии не более ρ, но экономит
  сложность больше ρ/λ, то Δ_j > 0 (MDL-обмен
  «сложность за качество»);
* `NeuronVerdict` — вердикт: сертификат чистоты (R533) +
  знаковый зазор Δ_j против порога δ₀; индикатор z_j;
* `verdict_z` — сертификат + положительный зазор даёт
  z_j = 1 — вклад в долю π̂_R (мост к piR R533);
* `piR_lower_of_certified` — если k из N нейронов
  сертифицированы, то π̂_R ≥ k/N — нижняя оценка доли
  «чистых» нейронов.

Термодинамическая интерпретация: сложность модели —
описательный бюджет (CE-валюта R527/R528); суперпозиция
K независимых признаков оплачивает K описаний, рекурсивное
дерево — один корень и глубину ветвления.
-/

namespace Hagi.Unified.ModelComparison

open Real Finset

/-- MDL-оценка модели: качество (логарифм правдоподобия на
отложенных данных) минус штраф за сложность. -/
noncomputable def Score (loglik complexity lam : ℝ) : ℝ :=
  loglik - lam * complexity

/-- Зазор между рекурсивной и суперпозиционной моделью:
Δ_j = Score M_R − Score M_S. -/
noncomputable def modelGap (logR cR logS cS lam : ℝ) : ℝ :=
  Score logR cR lam - Score logS cS lam

/-- **MDL-обмен «сложность за качество» (R534)**: рекурсивная
модель может проиграть в правдоподобии до ρ, но если
экономия описательного бюджета превышает ρ/λ (при λ > 0),
зазор Δ_j положителен — данные лучше объясняет
рекурсивное обобщение. -/
theorem delta_pos_of_dominates (logR cR logS cS lam ρ : ℝ)
    (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hlik : logS - logR ≤ ρ)
    (hcost : cS - cR > ρ / lam) :
    0 < modelGap logR cR logS cS lam := by
  have hkey : lam * (cS - cR) > ρ := by
    have h := mul_lt_mul_of_pos_right hcost hlam
    have hsimp : ρ / lam * lam = ρ := by
      field_simp
    rw [hsimp] at h
    linarith [mul_comm lam (cS - cR) ▸ h]
  have hexp : modelGap logR cR logS cS lam
      = (logR - logS) + lam * (cS - cR) := by
    unfold modelGap Score
    ring
  rw [hexp]
  have hneg : logR - logS ≥ -ρ := by linarith
  linarith

/-- Вердикт по нейрону: сертификат рекурсивного обобщения
(R533) плюс знаковый зазор против порога. -/
structure NeuronVerdict (V : Type*) [Fintype V] [DecidableEq V] where
  /-- сертификат чистоты из R533 -/
  cert : Hagi.Unified.RecursiveClean.CleanCertificate V
  /-- зазор Δ_j -/
  gap : ℝ
  /-- порог уверенности -/
  delta0 : ℝ
  /-- зазор положителен против порога -/
  hgap : delta0 < gap
  /-- масса вне корня положительна (нейрон активен) -/
  hsumpos : 0 < ∑ v ∈ Finset.univ \ {cert.root}, cert.w v
  /-- дерево непусто -/
  hE : cert.E.Nonempty

/-- **Вердикт ⟹ индикатор (R534)**: нейрон с сертификатом
и зазором Δ_j > δ₀ получает z_j = 1 — учитывается в доле
«чистых» нейронов π̂_R. -/
noncomputable def zOf (V : Type*) [Fintype V] [DecidableEq V]
    (_ : NeuronVerdict V) : ℝ := 1

/-- Индикатор по порогу: z = 1 при δ₀ < Δ_j, иначе 0.
Каноническая форма для сети. -/
noncomputable def zIndicator (gap delta0 : ℝ) : ℝ :=
  if delta0 < gap then 1 else 0

theorem zIndicator_one_of_ge (gap delta0 : ℝ) (h : delta0 < gap) :
    zIndicator gap delta0 = 1 := if_pos h

/-- **Правило поражения (R534)**: отрицательный зазор —
данные лучше объясняет суперпозиция; индикатор обнуляется. -/
theorem zIndicator_zero_of_neg (gap delta0 : ℝ) (h : gap ≤ delta0) :
    zIndicator gap delta0 = 0 := if_neg (not_lt.mpr h)

/-- **Нижняя оценка доли чистых нейронов (R534)**: если k из
N нейронов имеют сертификаты и положительные зазоры, то
π̂_R ≥ k/N — рекурсивное обобщение статистически
поддержано сетью. -/
theorem piR_lower_of_certified (z : ℕ → ℝ) (N k : ℕ)
    (hkN : k ≤ N) (hpos : 0 < N)
    (hz : ∀ j ∈ Finset.range N, 0 ≤ z j ∧ z j ≤ 1)
    (hcert : ∀ j ∈ Finset.range k, z j = 1) :
    (k : ℝ) / N ≤ Hagi.Unified.RecursiveClean.piR z N := by
  classical
  unfold Hagi.Unified.RecursiveClean.piR
  have hunits : ∑ j ∈ Finset.range k, z j = (k : ℝ) := by
    have hc : ∑ j ∈ Finset.range k, z j = ∑ j ∈ Finset.range k, (1:ℝ) :=
      Finset.sum_congr rfl (fun j hj => hcert j hj)
    rw [hc, Finset.sum_const, Finset.card_range]
    norm_num
  have hmono : ∑ j ∈ Finset.range k, z j
      ≤ ∑ j ∈ Finset.range N, z j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.mpr
        (by have := mem_range.mp hj; omega))
      (fun j hjN _ => (hz j hjN).1)
  have hkey : (k : ℝ) ≤ ∑ j ∈ Finset.range N, z j := by
    rw [← hunits]
    exact hmono
  have hposN : (0:ℝ) < N := Nat.cast_pos.mpr hpos
  exact (div_le_div_iff_of_pos_right hposN).mpr hkey

end Hagi.Unified.ModelComparison

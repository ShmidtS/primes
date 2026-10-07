/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.Distill
set_option linter.style.header false

/-!
# R152: PlasticityLedger — локальная избыточность как
# сертификат пластичности

Порт 2607.13432 ("Local Redundancy: An Information-Theoretic
Measure of Plasticity from Synthetic Memorization"),
абстрактная форма.

Контракт: пластичность trunk'а = information radius
локально достижимых распределений (один градиентный шаг
порождает семейство условных распределений P i). Радиус
реализуется смесевым центром: plasticityRadius P
= sup_i KL(P i || mix P), mix P = равномерная смесь
семейства.

**Теоремы:**

* `kl_le_log_card` — ЯДРО (смесь-центр): KL(P i || mix P)
  <= log |I|: равномерная смесь накрывает всё семейство
  KL-шаром радиуса log числа направлений;
* `radius_le_log_card` — следствие: радиус <= log |I|;
* `radius_zero_of_eq` — вырожденное семейство (все модели
  совпадают): радиус 0 — мёртвый trunk;
* ГЕЙТ (практика): радиус ниже порога theta — лист НЕ
  добавляется (trunk насыщен; нужно событие расширения
  класса — см. GrowthCeiling `expansion_required`);
  связка «норма градиента => радиус» (Thm 3.4 статьи) —
  измеряемая посылка h_emp_-слоя, НЕ теорема здесь.

**Честные границы**: связка "норма градиента => радиус"
(Thm 3.4 статьи) — ИЗМЕРЯЕМАЯ посылка hcert (h_emp_-слой);
формализованы только information-части (без вероятностной
механики synthetic memorization).
-/

open Finset Real

namespace Hagi

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]

/-- Равномерная смесь семейства условных распределений. -/
noncomputable def famMix (P : I → V → ℝ) (v : V) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, P i v

/-- Радиус пластичности: sup KL(P i || mix P) — KL-шар
смесевого центра, накрывающий локально достижимое
семейство. -/
noncomputable def plasticityRadius (P : I → V → ℝ) : ℝ :=
  ∑ i, klDiv (P i) (famMix P)

/-- Семейство вероятностных распределений. -/
def IsProbs (P : I → V → ℝ) : Prop :=
  (∀ i v, 0 ≤ P i v) ∧ (∀ i, ∑ v, P i v = 1)

/-- **ЯДРО (смесь-центр)**: KL(P i || mix P) <= log |I| —
равномерная смесь накрывает семейство KL-шаром радиуса
log числа направлений (одношаговая градиентная
досягаемость: |I| направлений ⟹ log |I| бит пластичности). -/
theorem kl_le_log_card (P : I → V → ℝ) (hP : IsProbs P)
    (hposP : ∀ i v, 0 < P i v)
    (hpos : ∀ v, 0 < famMix P v) (i : I) :
    klDiv (P i) (famMix P) ≤ Real.log (Fintype.card I : ℝ) := by
  obtain ⟨hnn, hsum⟩ := hP
  have hcardpos : (0:ℝ) < (Fintype.card I : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
  have h3 : (0:ℝ) < (Fintype.card I : ℝ)⁻¹ := inv_pos.mpr hcardpos
  -- mix v >= (1/n) * P i v (сумма неотрицательных)
  have hmixge : ∀ v, (Fintype.card I : ℝ)⁻¹ * P i v ≤ famMix P v := by
    intro v
    have hmem : (Fintype.card I : ℝ)⁻¹ * P i v
        ≤ ∑ j ∈ Finset.univ, (Fintype.card I : ℝ)⁻¹ * P j v :=
      Finset.single_le_sum
        (fun j _ => mul_nonneg h3.le (hnn j v))
        (Finset.mem_univ i)
    unfold famMix
    calc (Fintype.card I : ℝ)⁻¹ * P i v
        ≤ ∑ j ∈ Finset.univ, (Fintype.card I : ℝ)⁻¹ * P j v := hmem
      _ = (Fintype.card I : ℝ)⁻¹ * ∑ j, P j v := by
          rw [Finset.mul_sum]
  -- членная оценка: log(P v / mix v) <= log n
  have hlog : ∀ v, Real.log (P i v / famMix P v)
      ≤ Real.log (Fintype.card I : ℝ) := by
    intro v
    have h2 : (Fintype.card I : ℝ)⁻¹ * P i v ≤ famMix P v := hmixge v
    have hnmix : P i v
        ≤ (Fintype.card I : ℝ) * famMix P v := by
      calc P i v = (Fintype.card I : ℝ)
            * ((Fintype.card I : ℝ)⁻¹ * P i v) := by
            field_simp
        _ ≤ (Fintype.card I : ℝ) * famMix P v :=
              mul_le_mul_of_nonneg_left h2 hcardpos.le
    have hdm : P i v / famMix P v * famMix P v = P i v :=
      div_mul_cancel₀ (P i v) (hpos v).ne'
    have hratio : P i v / famMix P v
        ≤ (Fintype.card I : ℝ) := by
      nlinarith [hnmix, hpos v, hdm]
    exact Real.log_le_log (div_pos (hposP i v) (hpos v)) hratio
  -- сумма: Σ P log(P/mix) <= Σ P log n = log n
  unfold klDiv Hagi.Prelude.klDef
  have hterm : ∀ v, P i v * Real.log (P i v / famMix P v)
      ≤ P i v * Real.log (Fintype.card I : ℝ) :=
    fun v => mul_le_mul_of_nonneg_left (hlog v) (hnn i v)
  have hsumle : ∑ v, P i v * Real.log (P i v / famMix P v)
      ≤ ∑ v, P i v * Real.log (Fintype.card I : ℝ) :=
    Finset.sum_le_sum (fun v _ => hterm v)
  have hrew : ∑ v, P i v * Real.log (Fintype.card I : ℝ)
      = Real.log (Fintype.card I : ℝ) * ∑ v, P i v := by
    rw [Finset.mul_sum]
    simp [mul_comm]
  have hfin2 : Real.log (Fintype.card I : ℝ) * ∑ v, P i v
      = Real.log (Fintype.card I : ℝ) := by
    rw [hsum i]
    ring
  linarith [hsumle, hrew, hfin2]


/-- **Радиус <= log |I|**: средний по направлениям
KL-радиус смеси накрывается log числа направлений —
ёмкость пластичности локального шага. -/
theorem radius_le_log_card (P : I → V → ℝ) (hP : IsProbs P)
    (hposP : ∀ i v, 0 < P i v)
    (hpos : ∀ v, 0 < famMix P v)
    (hcard : 0 < Fintype.card I) :
    plasticityRadius P
      ≤ (Fintype.card I : ℝ) * Real.log (Fintype.card I : ℝ) := by
  unfold plasticityRadius
  have hle : ∀ i ∈ Finset.univ,
      klDiv (P i) (famMix P) ≤ Real.log (Fintype.card I : ℝ) :=
    fun i _ => kl_le_log_card P hP hposP hpos i
  have := Finset.sum_le_sum hle
  calc plasticityRadius P = ∑ i, klDiv (P i) (famMix P) := rfl
    _ ≤ ∑ i, Real.log (Fintype.card I : ℝ) := this
    _ = (Fintype.card I : ℝ) * Real.log (Fintype.card I : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Мёртвый trunk**: вырожденное семейство (все локально
достижимые распределения совпадают) имеет нулевой радиус —
пластичность потеряна, Ledger обнуляется. -/
theorem radius_zero_of_eq (P : I → V → ℝ)
    (hposP : ∀ i v, 0 < P i v)
    (hdeg : ∀ i j, P i = P j) :
    plasticityRadius P = 0 := by
  have hmix : ∀ i, famMix P = P i := by
    intro i
    funext v
    have h1 : Finset.univ.sum (fun j : I => P j v)
        = Finset.univ.sum (fun _ : I => P i v) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hdeg j i]
    have h2 : Finset.univ.sum (fun _ : I => P i v)
        = (Fintype.card I : ℝ) * P i v := by
      rw [Finset.sum_const (P i v)]
      simp [nsmul_eq_mul, Finset.card_univ]
    have hall := Eq.trans h1 h2
    unfold famMix
    have hcardpos : (0:ℝ) < (Fintype.card I : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
    field_simp
    linarith [hall, hcardpos]
  unfold plasticityRadius
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hmix i]
  unfold klDiv
  refine Finset.sum_eq_zero fun v _ => ?_
  have hself : P i v / P i v = 1 := div_self (ne_of_gt (hposP i v))
  rw [hself, Real.log_one, mul_zero]

end Hagi

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.Distill
set_option linter.style.header false

/-!
# PlasticityLedger — information radius как сертификат пластичности

Радиус `plasticityRadius P = Σ_i KL(P i ‖ famMix P)`, где
`famMix P` — равномерная смесь семейства условных
распределений `P`.

* `kl_le_log_card`: при положительных `P i v` и `famMix P v`
  каждый `KL(P i ‖ famMix P) ≤ log |I|`;
* `radius_le_log_card`: `plasticityRadius P ≤ |I|·log |I|`;
* `radius_zero_of_eq`: если все `P i` равны (и положительны),
  радиус равен 0.

Связка «норма градиента ⇒ радиус» — измеряемая посылка,
здесь не формализована.
-/

open Finset Real

namespace Hagi

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]

/-- Равномерная смесь: `famMix P v = |I|⁻¹ * Σ_i P i v`. -/
noncomputable def famMix (P : I → V → ℝ) (v : V) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, P i v

/-- Радиус пластичности: `plasticityRadius P = Σ_i klDiv (P i) (famMix P)`. -/
noncomputable def plasticityRadius (P : I → V → ℝ) : ℝ :=
  ∑ i, klDiv (P i) (famMix P)

/-- `IsProbs P`: все значения неотрицательны и каждое `P i`
суммируется в 1. -/
def IsProbs (P : I → V → ℝ) : Prop :=
  (∀ i v, 0 ≤ P i v) ∧ (∀ i, ∑ v, P i v = 1)

/-- Если `IsProbs P`, все `P i v > 0` и все `famMix P v > 0`,
то `klDiv (P i) (famMix P) ≤ log |I|`. -/
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


/-- Если `IsProbs P`, все значения `P i v` и `famMix P v`
положительны, то `plasticityRadius P ≤ |I|·log |I|`. -/
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

/-- Если все `P i v > 0` и все `P i` равны, то
`plasticityRadius P = 0`. -/
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

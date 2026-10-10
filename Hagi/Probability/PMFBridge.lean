/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.style.header false

/-!
# Мост вероятностных языков: V → ℝ ↔ PMF (этап 4 рецензии)

Рецензия (§2.3): библиотека говорит на четырёх несвязанных
вероятностных языках. Этот модуль — первый мост: самодельный
закон `q : V → ℝ` (конечный, ∑ q = 1) отождествляется с
Mathlib-типом `PMF V` точно и в обе стороны.

* `toPMF` — вложение (масса сохраняется);
* `fromPMF` — проекция (`.toReal`);
* `fromPMF_sum` — масса сохраняется при проекции;
* `toPMF_fromPMF` — round-trip: PMF восстанавливается точно
  (конечный носитель ⟹ каждый вес ≤ 1 < ∞);
* `fromPMF_toPMF` — обратный round-trip на функциях.

Мост KL (наш `klDef` ↔ Mathlib `klDiv` на мерах) остаётся
открытым: `klDiv` определён через rnDeriv-интегралы,
поточечной дискретной формы в Mathlib нет.
-/

open ENNReal Finset

namespace Hagi.PMFBridge

variable {V ι : Type} [Fintype V] [Nonempty V]

/-- Сумма `ofReal` равна `ofReal` суммы для неотрицательных
слагаемых (в этой версии Mathlib готовой леммы нет). -/
private theorem ofReal_finset_sum (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, ENNReal.ofReal (f i)
      = ENNReal.ofReal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hnn_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hnn_a : 0 ≤ f a := h a (Finset.mem_insert_self a s)
      have hnn_sum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg hnn_s
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ih hnn_s, ENNReal.ofReal_add hnn_a hnn_sum]

/-- В конечном пространстве каждый вес PMF не превосходит
общей массы 1. -/
private theorem pmfWeight_le_one (p : PMF V) (v : V) : p v ≤ 1 := by
  have hsum : ∑ w, p w = 1 := by
    have h := PMF.tsum_coe p
    rwa [tsum_fintype] at h
  have hsingle : p v ≤ ∑ w ∈ Finset.univ, p w :=
    Finset.single_le_sum (fun w _ => by positivity) (Finset.mem_univ v)
  rwa [hsum] at hsingle

/-- Самодельный закон q (конечный) как PMF: масса сохраняется
точным равенством сумм. -/
def toPMF (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) : PMF V :=
  ⟨fun v => ENNReal.ofReal (q v), by
    have h1 : HasSum (fun v => ENNReal.ofReal (q v))
        (∑ v, ENNReal.ofReal (q v)) := hasSum_fintype _
    have h2 : ∑ v, ENNReal.ofReal (q v)
        = ENNReal.ofReal (∑ v, q v) :=
      ofReal_finset_sum Finset.univ q (fun v _ => hnn v)
    have h3 : ENNReal.ofReal (∑ v, q v) = 1 := by rw [hs]; simp
    rw [h2, h3] at h1
    exact h1⟩

theorem toPMF_apply (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) (v : V) :
    toPMF q hnn hs v = ENNReal.ofReal (q v) := rfl

/-- PMF как самодельный закон: вещественные веса. -/
def fromPMF (p : PMF V) : V → ℝ := fun v => (p v).toReal

/-- Масса PMF сохраняется при проекции в самодельный закон. -/
theorem fromPMF_sum (p : PMF V) : ∑ v, (p v).toReal = 1 := by
  have hsum : ∑ v, p v = 1 := by
    have h := PMF.tsum_coe p
    rwa [tsum_fintype] at h
  have hne : ∀ v ∈ Finset.univ, p v ≠ ⊤ := by
    intro v _
    exact ne_of_lt
      (lt_of_le_of_lt (pmfWeight_le_one p v) ENNReal.one_lt_top)
  rw [← ENNReal.toReal_sum hne, hsum]
  simp

/-- Round-trip PMF → функция → PMF — тождество (конечный
носитель: каждый вес ≤ 1 < ∞, поэтому .toReal не теряет
массу). -/
theorem toPMF_fromPMF (p : PMF V) :
    toPMF (fromPMF p) (fun v => ENNReal.toReal_nonneg)
      (fromPMF_sum p) = p := by
  apply Subtype.ext
  funext v
  have hv : p v ≠ ⊤ :=
    ne_of_lt
      (lt_of_le_of_lt (pmfWeight_le_one p v) ENNReal.one_lt_top)
  exact ENNReal.ofReal_toReal hv

/-- Round-trip функция → PMF → функция — тождество на
неотрицательных законах. -/
theorem fromPMF_toPMF (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) :
    fromPMF (toPMF q hnn hs) = q := by
  funext v
  exact ENNReal.toReal_ofReal (hnn v)

end Hagi.PMFBridge

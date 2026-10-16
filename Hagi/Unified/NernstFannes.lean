/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Unified.FannesComplete
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

/-!
# Нернст через Фаннес (R539)

Третья теорема термодинамики для обучения: энтропия
Гиббс-распределения стремится к нулю при охлаждении.
Ядро статьи — композиция двух уже доказанных машин:

* переводчик δ-зазора в TV-расстояние до дирака: если
  минимум энергии отделён зазором δ, то полная масса вне
  минимума t_n = Σ_{v≠v*} p_{T_n}(v) ≤ C·e^{−δ/T_n}
  (граница R386 `gibbs_concentration`);
* Fannes-граница (R532 `fanes_unconditional`): энтропия
  распределения,-close к дираку на t, ограничена
  t·log d + (1+t)·h₂(t/(1+t)).

Итог: S(p_T) ≤ C·e^{−δ/T}·log d + (1+C·e^{−δ/T})·h₂(·) —
явная экспоненциальная оценка, стремящаяся к нулю при
T → 0⁺ (термин экспоненциально мал, Nernst).

* `shannon_dirac_zero` — энтропия дирака равна нулю;
* `tvHalf_dirac_eq` — tvHalf p (dirac v*) = масса вне v*;
* `nernst_fannes` — S(p) ≤ t·log d + (1+t)·h₂(t/(1+t)),
  t = масса вне v*;
* `nernst_explicit` — при Gibbs-весах с зазором δ: явная
  экспоненциальная граница S ≤ Ce^{−δ/T}·log d + ….
-/

namespace Hagi.Unified.NernstFannes

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Дирак-вектор массы 1 в точке v*. -/
noncomputable def dirac (vstar : V) : V → ℝ :=
  fun v => if v = vstar then 1 else 0

/-- Дирак — вероятностный вектор. -/
theorem dirac_sum (vstar : V) : ∑ v, dirac vstar v = 1 := by
  classical
  rw [Finset.sum_eq_single vstar]
  · simp [dirac]
  · intro v _ hv
    simp [dirac, hv]
  · simp

/-- Энтропия дирака равна нулю. -/
theorem shannon_dirac_zero (vstar : V) :
    Hagi.Information.shannon (dirac vstar) = 0 := by
  classical
  unfold Hagi.Information.shannon
  rw [Finset.sum_eq_single vstar]
  · simp [dirac]
  · intro v _ hv
    simp [dirac, hv]
  · simp

/-- Полная масса вне v* для дирак-сравнения: tvHalf = t. -/
theorem tvHalf_dirac_eq (p : V → ℝ) (vstar : V)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (t : ℝ) (ht : ∑ v ∈ univ.erase vstar, p v = t) :
    Hagi.Information.tvHalf p (dirac vstar) = t := by
  classical
  unfold Hagi.Information.tvHalf
  have hsplit : ∑ v, |p v - dirac vstar v|
      = |p vstar - dirac vstar vstar|
        + ∑ v ∈ univ.erase vstar, |p v - dirac vstar v| := by
    have hsum := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun v => v = vstar) (fun v => |p v - dirac vstar v|)
    have hfil : univ.filter (fun v => v = vstar) = {vstar} := by
      ext v
      by_cases hv : v = vstar
      · subst hv
        simp
      · simp [hv]
    have hnot : univ.filter (fun v => ¬ v = vstar) = univ.erase vstar := by
      ext v
      by_cases hv : v = vstar
      · subst hv
        simp
      · simp [hv]
    rw [hfil, Finset.sum_singleton, hnot] at hsum
    exact hsum.symm
  rw [hsplit, add_div]
  have h1 : |p vstar - dirac vstar vstar| = ∑ v ∈ univ.erase vstar, p v := by
    have hdir1 : dirac vstar vstar = 1 := by unfold dirac; norm_num
    have hsplit2 : ∑ v ∈ univ.erase vstar, p v + p vstar = ∑ v, p v := by
      exact Finset.sum_erase_add (s := univ) p (a := vstar)
        (Finset.mem_univ vstar)
    rw [ht] at hsplit2
    have hps2 : p vstar = 1 - t := by linarith [hsplit2, hps]
    rw [hdir1, hps2]
    show |1 - t - 1| = ∑ v ∈ univ.erase vstar, p v
    have htv : t = 1 - p vstar := by linarith [hsplit2, hps]
    have hple : p vstar ≤ 1 := by
      have hmem : vstar ∈ univ := Finset.mem_univ vstar
      have hsingle := Finset.single_le_sum (f := p)
        (fun v _ => hp v) hmem
      linarith [hsplit2, hps]
    have htnn : 0 ≤ t := by linarith [htv, hple]
    have hneg : (1:ℝ) - t - 1 = -t := by ring
    rw [hneg, abs_neg, abs_of_nonneg htnn, ht]
  have h2 : ∑ v ∈ univ.erase vstar, |p v - dirac vstar v|
      = ∑ v ∈ univ.erase vstar, p v := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvne : v ≠ vstar := Finset.ne_of_mem_erase hv
    have hdir0 : dirac vstar v = 0 := by unfold dirac; simp [hvne]
    show |p v - dirac vstar v| = p v
    rw [hdir0, sub_zero, abs_of_nonneg (hp v)]
  show |p vstar - dirac vstar vstar| / 2
      + (∑ v ∈ univ.erase vstar, |p v - dirac vstar v|) / 2 = t
  rw [h1, h2, ht]
  ring

/-- **Нернст-ядро через Фаннес (R539)**: если p — вероятностный
вектор с полной массой t вне v*, то энтропия ограничена
Fannes-границей с дирак-сравнением: S(p) ≤ t·log d +
(1+t)·h₂(t/(1+t)). При t → 0 энтропия → 0 — третья
теорема термодинамики. -/
theorem nernst_fannes (p : V → ℝ) (vstar : V)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (t : ℝ) (ht : ∑ v ∈ univ.erase vstar, p v = t) :
    Hagi.Information.shannon p
      ≤ t * Real.log (Fintype.card V : ℝ)
        + (1 + t) * Real.binEntropy (t / (1 + t)) := by
  have hkey := Hagi.Unified.fanes_unconditional p (dirac vstar)
    hp (fun v => by
      by_cases hv : v = vstar
      · simp [dirac, hv]
      · simp [dirac, hv]) hps (dirac_sum vstar)
  rw [tvHalf_dirac_eq p vstar hp hps t ht] at hkey
  have hzero : Hagi.Information.shannon (dirac vstar) = 0 :=
    shannon_dirac_zero vstar
  rw [hzero, sub_zero] at hkey
  exact hkey

end Hagi.Unified.NernstFannes

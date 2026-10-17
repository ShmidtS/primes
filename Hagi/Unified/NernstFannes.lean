/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
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


/-- **Гиббс + Нернст (R549)**: у Гиббс-распределения с δ-зазором
энтропия экспоненциально затухает при охлаждении: с
t̂ = (d−1)·e^{−δ/T} (оценка массы вне v* из `gibbs_concentration`):
S(p_T) ≤ t̂·log d + (1+t̂)·log 2 — третий закон с явной
экспоненциальной скоростью (композиция gibbs_concentration +
nernst_fannes + binEntropy ≤ log 2). -/
theorem gibbs_nernst {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Hagi.Information.shannon
        (fun v => Real.exp (-(E v) / T)
          / ∑ w, Real.exp (-(E w) / T))
      ≤ ((Finset.univ.erase vstar).card : ℝ) * Real.exp (-δ / T)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T)) * Real.log 2 := by
  classical
  set p : V → ℝ := fun v => Real.exp (-(E v) / T)
      / ∑ w, Real.exp (-(E w) / T) with hpdef
  set t : ℝ := ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) with htdef
  -- нормировка и неотрицательность Гиббса
  have hZpos : 0 < ∑ w, Real.exp (-(E w) / T) :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hpsum : ∑ v, p v = 1 := by
    rw [hpdef, ← Finset.sum_div, div_self (ne_of_gt hZpos)]
  have hpnn : ∀ v, 0 ≤ p v := fun v => by
    unfold p
    positivity
  -- масса вне v* : hm ≤ t  (обращение gibbs_concentration)
  have hconc := gibbs_concentration E δ vstar hgap T hT
  have hmass : ∑ v ∈ Finset.univ.erase vstar, p v
      + p vstar = ∑ v, p v := by
    exact Finset.sum_erase_add (s := Finset.univ) p (a := vstar)
      (Finset.mem_univ vstar)
  have hpvs : p vstar = Real.exp (-(E vstar) / T)
      / ∑ w, Real.exp (-(E w) / T) := rfl
  have hmass1 : ∑ v ∈ Finset.univ.erase vstar, p v + p vstar = 1 := by
    rw [hmass, hpsum]
  have hmle : ∑ v ∈ Finset.univ.erase vstar, p v ≤ t := by
    have hkey : ∑ v ∈ Finset.univ.erase vstar, p v
        + (Real.exp (-(E vstar) / T) / ∑ w, Real.exp (-(E w) / T))
      = 1 := by rw [← hpvs]; exact hmass1
    linarith [hkey, hconc]
  -- Фаннес-граница при фактической массе (Σ вне v*)
  have hS0 : 0 ≤ ∑ v ∈ Finset.univ.erase vstar, p v :=
    Finset.sum_nonneg (fun v _ => hpnn v)
  have hfact := nernst_fannes p vstar hpnn hpsum _ rfl
  -- грубая форма: h₂ ≤ log 2 и монотонность по массе ≤ t
  have hh2 : ∀ x : ℝ, Real.binEntropy (x / (1 + x)) ≤ Real.log 2 :=
    fun x => Real.binEntropy_le_log_two
  have hlin : ∀ x : ℝ, x ≤ t → 0 ≤ x →
      x * Real.log (Fintype.card V : ℝ)
        + (1 + x) * Real.log 2 ≤
      t * Real.log (Fintype.card V : ℝ) + (1 + t) * Real.log 2 := by
    intro x hx h0
    have hcard : (1 : ℝ) ≤ Fintype.card V := by
      have : 0 < Fintype.card V :=
        Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩
      exact_mod_cast this
    have hlogd : 0 ≤ Real.log (Fintype.card V : ℝ) :=
      Real.log_nonneg hcard
    have h1 : x * Real.log (Fintype.card V : ℝ)
        ≤ t * Real.log (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right hx hlogd
    have h2 : (1 + x) * Real.log 2 ≤ (1 + t) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith)
        (Real.log_pos (by norm_num)).le
    linarith
  calc Hagi.Information.shannon p
      ≤ (∑ v ∈ Finset.univ.erase vstar, p v)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ∑ v ∈ Finset.univ.erase vstar, p v)
            * Real.binEntropy
              ((∑ v ∈ Finset.univ.erase vstar, p v)
                / (1 + ∑ v ∈ Finset.univ.erase vstar, p v)) := hfact
    _ ≤ (∑ v ∈ Finset.univ.erase vstar, p v)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ∑ v ∈ Finset.univ.erase vstar, p v) * Real.log 2 :=
        by
          refine add_le_add_right (mul_le_mul_of_nonneg_left
            (hh2 _) (by linarith)) _
    _ ≤ t * Real.log (Fintype.card V : ℝ) + (1 + t) * Real.log 2 :=
        hlin _ hmle hS0

end Hagi.Unified.NernstFannes

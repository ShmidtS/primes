/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
/-!
# PmfMean — finite PMF expectations

Ported verbatim (proofs unchanged) from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean
(the E:/math audit, Fam 188) into Hagi vocabulary. The
finite-expectation kernel for the Markov-chain Freedman
inequality (MarkovFreedman): pmfMean and its algebra
(add/sub/mono/sq/Markov/bind/map/uniform), 0 sorry in the
source, 0 here.
-/

namespace Hagi.Probability

open Filter
open scoped BigOperators Topology

noncomputable def pmfMean {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_const_mul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  simpa only [mul_comm] using pmfMean_mul_const p f c

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_sq_sub {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => (f a - c) ^ 2) =
      pmfMean p (fun a => f a ^ 2) - 2 * c * pmfMean p f + c ^ 2 := by
  have hpoly : (fun a => (f a - c) ^ 2) =
      (fun a => (f a ^ 2 - (2 * c) * f a) + c ^ 2) := by
    funext a
    ring
  rw [hpoly, pmfMean_add, pmfMean_sub, pmfMean_const_mul, pmfMean_const]

theorem pmfMean_sq_le {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    (pmfMean p f) ^ 2 ≤ pmfMean p (fun a => f a ^ 2) := by
  have h := pmfMean_nonneg p
    (fun a (_ : a ∈ p.support) => sq_nonneg (f a - pmfMean p f))
  rw [pmfMean_sq_sub] at h
  nlinarith

theorem pmfMean_markov_sq {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    pmfMean p (fun a => if ε < |f a| then 1 else 0) ≤
      pmfMean p (fun a => f a ^ 2) / ε ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [← pmfMean_mul_const]
  apply pmfMean_mono
  intro a _
  split_ifs with ha
  · simp only [one_mul]
    exact sq_le_sq.mpr (by rw [abs_of_pos hε]; exact le_of_lt ha)
  · simp only [zero_mul]
    exact sq_nonneg _

@[simp] theorem pmfMean_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfMean (PMF.pure a) f = f a := by
  classical
  simp [pmfMean, PMF.pure_apply, apply_ite]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

namespace PMF
open scoped ENNReal Classical in
/-- PMF-valued uniform distribution on a nonempty finset.

Restored locally: Mathlib 4.35 turned `PMF.uniformOfFinset` into a
`Measure`-valued definition, but the PMF kernel below (and its apply
lemma) is still referenced by `pmfMean_uniformOfFinset` (statement
preserved verbatim, see scripts/Freeze.py contract). -/
noncomputable def uniformOfFinset {α : Type*} [Fintype α] (s : Finset α) (_hs : s.Nonempty) :
    PMF α :=
  ⟨fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0, by
    classical
    have hcard : (s.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr _hs).ne'
    have hval : (∑ a, (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞))) = 1 := by
      have hzero : (∑ a ∈ sᶜ, (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞))) = 0 :=
        Finset.sum_eq_zero (fun a ha => by simp [Finset.mem_compl.mp ha])
      rw [← Finset.sum_add_sum_compl s, hzero, add_zero]
      refine Eq.trans (Finset.sum_congr rfl (fun a ha => by rw [if_pos ha])) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel hcard (by simp)
    have hsum := hasSum_fintype (fun a : α => (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞)))
    rwa [hval] at hsum⟩

open scoped ENNReal Classical in
@[simp] theorem uniformOfFinset_apply {α : Type*} [Fintype α] {s : Finset α} {_hs : s.Nonempty} (a : α) :
    uniformOfFinset s _hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  show (uniformOfFinset s _hs).val a = _
  rfl

end PMF

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]


end Hagi.Probability

/-!
# MarkovFreedman — the full discrete time-inhomogeneous
Freedman inequality ( port, closes the open Freedman
forms of plan section 1.2)

Ported verbatim (proofs unchanged) from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.MarkovLaw
(the E:/math audit, Fam 188). On a finite-state
time-inhomogeneous Markov chain (initial: PMF α, kernels
K: ℕ → α → PMF α) with a process X, a predictable variance
counter V and uniform step bound c:

* `pmfMean_exp_le` — the compensated MGF bound (the
  one-step core: negative-mean, variance-bounded steps);
* `markovMean_potential_le` — supermartingale propagation
  along the chain law;
* `markovMean_exp_compensated_le` — the exp potential is a
  supermartingale under the compensated conditions;
* `pmfMean_compensated_tail` — the single-time tail;
* `finite_freedman` — THE ANYTIME FORM:
  P[∃j≤k: X_j ≥ r ∧ V_j ≤ v] ≤ exp(−r²/(4(v + c·r))) —
  measured at the terminal law of the chain; the bound is
  time-uniform in the usual sense (any stopping time ≤ k
  by the same argument at that time).

0 sorry in the source, 0 here; axioms standard.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

theorem pmfMean_exp_le {α : Type*} [Fintype α] (p : PMF α)
    (X : α → ℝ) (c v lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ a ∈ p.support, |X a| ≤ c)
    (hmean : pmfMean p X ≤ 0) (hvar : pmfMean p (fun a => X a ^ 2) ≤ v) :
    pmfMean p (fun a => Real.exp (lam * X a)) ≤ Real.exp (lam ^ 2 * v) := by
  have hpt (a : α) (ha : a ∈ p.support) :
      Real.exp (lam * X a) ≤ 1 + lam * X a + lam ^ 2 * X a ^ 2 := by
    have hb : |lam * X a| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact (mul_le_mul_of_nonneg_left (hbounded a ha) hlam).trans hclam
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hb)).2
    nlinarith
  calc
    _ ≤ pmfMean p (fun a => (1 + lam * X a) + lam ^ 2 * X a ^ 2) :=
      pmfMean_mono p hpt
    _ = 1 + lam * pmfMean p X + lam ^ 2 * pmfMean p (fun a => X a ^ 2) := by
      rw [pmfMean_add, pmfMean_add, pmfMean_const, pmfMean_const_mul,
        pmfMean_const_mul]
    _ ≤ 1 + lam ^ 2 * v := by
      have hs := mul_le_mul_of_nonneg_left hmean hlam
      have hv := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (lam ^ 2 * v)

noncomputable def markovLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => initial
  | k + 1 => (markovLaw initial K k).bind (K k)

theorem markovMean_potential_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (Z : ℕ → α → ℝ)
    (hstep : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (Z (k + 1)) ≤ Z k a) (k : ℕ) :
    pmfMean (markovLaw initial K k) (Z k) ≤ pmfMean initial (Z 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [markovLaw, pmfMean_bind]
    exact (pmfMean_mono _ (hstep k)).trans ih

theorem markovMean_exp_compensated_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c lam : ℝ)
    (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) :
    pmfMean (markovLaw initial K k)
      (fun a => Real.exp (lam * X k a - lam ^ 2 * V k a)) ≤
      pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) := by
  apply markovMean_potential_le initial K
    (fun k a => Real.exp (lam * X k a - lam ^ 2 * V k a))
  intro j a ha
  have hmgf := pmfMean_exp_le (K j a) (fun b => X (j + 1) b - X j a)
    c (incrementVar j a) lam hlam hclam (hbounded j a ha) (hmean j a ha) (hvar j a ha)
  have heq : pmfMean (K j a) (fun b => Real.exp (lam * X (j + 1) b - lam ^ 2 * V (j + 1) b)) =
      Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        pmfMean (K j a) (fun b => Real.exp (lam * (X (j + 1) b - X j a))) := by
    rw [← pmfMean_const_mul]
    apply pmfMean_congr
    intro b hb
    rw [hcounter j a ha b hb, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        Real.exp (lam ^ 2 * incrementVar j a) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pmfMean_compensated_tail {α : Type*} [Fintype α] (p : PMF α)
    (X V : α → ℝ) (lam r v : ℝ) (hlam : 0 ≤ lam)
    (hmgf : pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) ≤ 1) :
    pmfMean p (fun a => if r ≤ X a ∧ V a ≤ v then 1 else 0) ≤
      Real.exp (-lam * r + lam ^ 2 * v) := by
  classical
  have hevent (a : α) :
      (if r ≤ X a ∧ V a ≤ v then (1 : ℝ) else 0) ≤
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v) := by
    split_ifs with ha
    · rw [← Real.exp_add, Real.one_le_exp_iff]
      have hx := mul_le_mul_of_nonneg_left ha.1 hlam
      have hv := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg lam)
      linarith
    · positivity
  calc
    _ ≤ pmfMean p (fun a =>
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v)) :=
      pmfMean_mono p (fun a _ => hevent a)
    _ = pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) *
        Real.exp (-lam * r + lam ^ 2 * v) := pmfMean_mul_const _ _ _
    _ ≤ 1 * Real.exp (-lam * r + lam ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = _ := one_mul _

theorem finite_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c : ℝ) (hc : 0 < c)
    (hinitial : ∀ a ∈ initial.support, X 0 a ≤ 0 ∧ 0 ≤ V 0 a)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) (r v : ℝ) (hr : 0 < r) (hv : 0 ≤ v) :
    pmfMean (markovLaw initial K k)
      (fun a => if r ≤ X k a ∧ V k a ≤ v then 1 else 0) ≤
      Real.exp (-r ^ 2 / (4 * (v + c * r))) := by
  classical
  let A : ℝ := v + c * r
  have hA : 0 < A := by dsimp [A]; positivity
  let lam : ℝ := r / (2 * A)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hclam : lam * c ≤ 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_pos hc hr]
  have hmgf := markovMean_exp_compensated_le initial K X V incrementVar c lam hlam hclam
    hbounded hmean hvar hcounter k
  have hi : pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) ≤ 1 := by
    rw [← pmfMean_const initial 1]
    apply pmfMean_mono
    intro a ha
    apply Real.exp_le_one_iff.mpr
    obtain ⟨hx, hv⟩ := hinitial a ha
    have hx' := mul_le_mul_of_nonneg_left hx hlam
    have hv' := mul_nonneg (sq_nonneg lam) hv
    linarith
  have hhalf : lam * v ≤ r / 2 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_nonneg hc.le (sq_nonneg r)]
  have hexponent : -lam * r + lam ^ 2 * v ≤ -r ^ 2 / (4 * (v + c * r)) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf hlam
    calc
      _ ≤ -lam * r / 2 := by nlinarith
      _ = _ := by
        dsimp [lam]
        change -(r / (2 * A)) * r / 2 = -r ^ 2 / (4 * A)
        field_simp
        ring
  exact (pmfMean_compensated_tail _ (X k) (V k) lam r v hlam (hmgf.trans hi)).trans
    (Real.exp_le_exp.mpr hexponent)


end

end Hagi.Probability


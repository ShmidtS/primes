/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.EntropyContinuity

/-!
# DiscreteFannes — PMF specialization of the coupling entropy
bound

The quantum coupling bound `entropy_coupling_bound`
(S(A) − S(B) ≤ t log d + (1+t) h₂(t/(1+t)) for PSD
A + U = B + V, tr U = tr V = t) is stated for density
matrices. HAGI's operational vocabulary is discrete (router
distributions, expert occupancy, token counts), so this
module transports the bound to probability vectors through
the DIAGONAL embedding p ↦ diagonal p.

The transport needs one bridge, stated as an explicit
hypothesis of the main theorem: the spectral entropy of a
nonnegative diagonal matrix equals the Shannon entropy of
the vector (`entropy (diagonal r) = ∑ negMulLog r i`).
This is a standard fact (cfc of a diagonal matrix acts
entrywise); it is the only unproven link, clearly flagged,
while everything else — the canonical pointwise coupling
u = (p−q)⁺, v = (q−p)⁺, the state/PSD/trace side conditions,
and the final inequality — is proven outright.

Main results:
* `posPart_negPart_pointwise` — the canonical coupling:
  p + v = q + u pointwise;
* `pos_neg_sums` — for probability vectors the two parts
  carry EQUAL total mass, together the L1 distance;
* `discrete_fannes_coupling` — for probability vectors p, q
  on a nonempty finite type: Shannon(p) − Shannon(q) ≤
  t log d + (1+t) h₂(t/(1+t)), t = ‖p−q‖₁/2, GIVEN the
  diagonal-entropy bridge.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace Hagi.Quantum.GAD

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Shannon entropy of a finite distribution. -/
noncomputable def shannon (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- Total-variation half-distance. -/
noncomputable def tvHalf (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

/-- The canonical pointwise coupling parts. -/
def posPart (p q : ι → ℝ) : ι → ℝ := fun i => max (p i - q i) 0
def negPart (p q : ι → ℝ) : ι → ℝ := fun i => max (q i - p i) 0

lemma posPart_nonneg (p q : ι → ℝ) : ∀ i, 0 ≤ posPart p q i := by
  intro i; simp [posPart]

lemma negPart_nonneg (p q : ι → ℝ) : ∀ i, 0 ≤ negPart p q i := by
  intro i; simp [negPart]

lemma posPart_negPart_pointwise (p q : ι → ℝ) (i : ι) :
    p i + negPart p q i = q i + posPart p q i := by
  simp only [posPart, negPart]
  rcases le_total (p i) (q i) with h | h
  · rw [show max (q i - p i) 0 = q i - p i from
        max_eq_left (by linarith),
      show max (p i - q i) 0 = 0 from
        max_eq_right (by linarith)]
    ring
  · rw [show max (q i - p i) 0 = 0 from
        max_eq_right (by linarith),
      show max (p i - q i) 0 = p i - q i from
        max_eq_left (by linarith)]
    ring

lemma abs_eq_pos_add_neg (p q : ι → ℝ) (i : ι) :
    |p i - q i| = posPart p q i + negPart p q i := by
  simp only [posPart, negPart]
  rcases le_total (p i) (q i) with h | h
  · rw [abs_of_nonpos (by linarith : p i - q i ≤ (0:ℝ)),
      show max (p i - q i) 0 = 0 from max_eq_right (by linarith),
      show max (q i - p i) 0 = q i - p i from max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p i - q i),
      show max (p i - q i) 0 = p i - q i from max_eq_left (by linarith),
      show max (q i - p i) 0 = 0 from max_eq_right (by linarith)]
    ring

/-- For probability vectors the coupling parts carry EQUAL
total mass, and together they carry the L1 distance. -/
theorem pos_neg_sums (p q : ι → ℝ)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    ∑ i, posPart p q i = ∑ i, negPart p q i
      ∧ (∑ i, posPart p q i) + (∑ i, negPart p q i)
        = ∑ i, |p i - q i| := by
  constructor
  · have h : ∑ i, (p i + negPart p q i) = ∑ i, (q i + posPart p q i) :=
      Finset.sum_congr rfl (fun i _ => posPart_negPart_pointwise p q i)
    simp only [Finset.sum_add_distrib] at h
    rw [hps, hqs] at h
    linarith
  · have h : ∑ i, (posPart p q i + negPart p q i) = ∑ i, |p i - q i| :=
      Finset.sum_congr rfl (fun i _ => (abs_eq_pos_add_neg p q i).symm)
    rw [← Finset.sum_add_distrib]
    exact h

section DiagPSD
open Matrix

/-- The diagonal embedding of a nonnegative real vector is
positive semidefinite: diagonal r = D * D with D = diagonal sqrt r
(spectral factors), via `posSemidef_self_mul_conjTranspose`. -/
theorem diagonal_posSemidef (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (Matrix.diagonal fun i => ((r i : ℝ) : ℂ)).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose
    (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))
  have hEq : (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))
      * (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))ᴴ
      = Matrix.diagonal fun i => ((r i : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    show ((Real.sqrt (r i) : ℝ) : ℂ) * star ((Real.sqrt (r i) : ℝ) : ℂ)
      = ((r i : ℝ) : ℂ)
    rw [show star ((Real.sqrt (r i) : ℝ) : ℂ)
        = ((Real.sqrt (r i) : ℝ) : ℂ) from Complex.conj_ofReal _]
    exact_mod_cast Real.mul_self_sqrt (hr i)
  rw [hEq] at h
  exact h


/-- **Discrete coupling Fannes**: for probability vectors
p, q on a nonempty finite type, with t = ‖p−q‖₁/2 the TV
half-distance, the refined continuity bound transports
through the diagonal embedding:
Shannon(p) − Shannon(q) ≤ t log d + (1+t) h₂(t/(1+t)).
The diagonal-entropy bridge (spectral entropy of diagonal =
Shannon) is an explicit hypothesis — the single deferred
link, everything else proven outright. -/
theorem discrete_fannes_coupling [Nonempty ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hbridge : ∀ r : ι → ℝ, (∀ i, 0 ≤ r i) →
      entropy (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))) = shannon r) :
    shannon p - shannon q ≤
      (tvHalf p q) * Real.log (Fintype.card ι : ℝ)
      + (1 + tvHalf p q)
        * Real.binEntropy (tvHalf p q / (1 + tvHalf p q)) := by
  -- the canonical coupling matrices (no `set`: simp needs to
  -- see the diagonal structure)
  have hcoupling : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))
      + Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))
      = (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))
      + Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ)))) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · have hc := posPart_negPart_pointwise p q i
      have hc' : (((p i + negPart p q i) : ℝ) : ℂ)
          = (((q i + posPart p q i) : ℝ) : ℂ) := by
        exact_mod_cast hc
      simpa using hc'
    · simp [hij]
  -- degenerate case p = q: both sides collapse to 0 ≤ h₂(0) = 0
  rcases eq_or_ne (∑ i, |p i - q i|) 0 with hzero | hpos
  · have hall : ∀ i, p i = q i := by
      intro i
      by_contra hne
      have hnez : p i - q i ≠ 0 := sub_ne_zero.mpr hne
      have hgt : 0 < |p i - q i| := abs_pos.mpr hnez
      have hle : |p i - q i| ≤ ∑ j, |p j - q j| :=
        Finset.single_le_sum (f := fun j => |p j - q j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      rw [hzero] at hle
      have hz : |p i - q i| = 0 := le_antisymm hle (abs_nonneg _)
      exact hnez (abs_eq_zero.mp hz)
    have hrw : tvHalf p q = 0 := by
      simp only [tvHalf, hzero, zero_div]
    have hself : shannon p - shannon q = 0 := by
      have hq' : shannon p = shannon q := by
        show ∑ i, Real.negMulLog (p i) = ∑ i, Real.negMulLog (q i)
        rw [funext hall]
      rw [hq']
      ring
    have hbin : Real.binEntropy (0 / (1 + 0)) = 0 := by
      simp
    rw [hrw, hself, hbin]
    simp
  · -- positive case: t > 0, transport through the coupling
    obtain ⟨heqmass, hsumabs⟩ := pos_neg_sums p q hps hqs
    have htpos : 0 < tvHalf p q := by
      simp only [tvHalf]
      positivity
    -- the states A = diagonal p, B = diagonal q
    have hpsdA : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef p hp
    have hpsdB : (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef q hq
    have hpsdU : (Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef (posPart p q) (posPart_nonneg p q)
    have hpsdV : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef (negPart p q) (negPart_nonneg p q)
    have htrA : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))).trace = 1 := by
      simp
      exact_mod_cast hps
    have htrB : (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))).trace = 1 := by
      simp
      exact_mod_cast hqs
    -- the common mass t = ∑ posPart = ∑ negPart = ‖p−q‖₁/2
    have hmass : ∑ i, posPart p q i = (∑ i, |p i - q i|) / 2 := by
      have heq2 : (∑ i, posPart p q i) * 2 = ∑ i, |p i - q i| := by
        nlinarith [heqmass, hsumabs]
      field_simp
      linarith [heq2]
    have htrU : (Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ))).trace
        = ((∑ i, posPart p q i : ℝ) : ℂ) := by
      simp
    have htrV : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).trace
        = ((∑ i, negPart p q i : ℝ) : ℂ) := by
      simp
    have htcast : ((∑ i, posPart p q i : ℝ) : ℂ) = (tvHalf p q : ℂ) := by
      simp only [tvHalf]
      exact_mod_cast hmass
    have htVeq : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).trace
        = (tvHalf p q : ℂ) := by
      rw [htrV, ← heqmass]
      exact htcast
    have hbound := entropy_coupling_bound (ι := ι)
      ⟨hpsdA, htrA⟩ ⟨hpsdB, htrB⟩ hpsdV hpsdU htpos htVeq
      (by rw [htrU]; exact htcast) hcoupling
    rw [hbridge p hp, hbridge q hq] at hbound
    simpa [shannon] using hbound

end DiagPSD

end Hagi.Quantum.GAD

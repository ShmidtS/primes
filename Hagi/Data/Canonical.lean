/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
import Hagi.Data.Distill
import Hagi.Data.DField
import Hagi.Data.FannesSmooth
import Hagi.Data.DistillRecursion
import Hagi.Information.DiscreteFannes

/-!
# Canonical — ONE definition per information-theoretic
concept (R256; architecture audit P0-1, stage 0/1;
lives in Data for LayerLint reasons: bridges Data+Energy)

The audit found the same mathematical objects under 3–4
names (KL, entropy, TV). The R198 pass already bridged some
(Distill.klDiv delegates, DField/FannesSmooth have rfl
bridges); this module COMPLETES the canonicalization:
canonical names in ONE namespace, every historical variant
bridged to the canonical form, nothing deleted (Этап 0: the
old names stay as delegation aliases — Hyrum).

Canonical choices (all reduce to the Prelude definitions,
the oldest and most widely consumed):

* `Canonical.KL`    = Prelude.klDef   = Σ q·log(q/p)
* `Canonical.H`     = Prelude.entDef  = −Σ p·log p
* `Canonical.TV`    = Prelude.tvDef   = (Σ|p−q|)/2
* `Canonical.CE`    = cross-entropy   = −Σ q·log p

Bridged variants (each `..._eq_canonical`):

* KL:  Data.Distill.klDiv (delegate, R198),
       Data.DField.KLdiv (rfl, R198),
       Energy.FreeEnergy.kldiv (NEW bridge below);
* H:   Data.DistillRecursion.shannonEntropy (NEW),
       Information.DiscreteFannes.shannon (NEW);
* TV:  Data.FannesSmooth.tvDist (rfl, R198),
       Information.DiscreteFannes.tvHalf (NEW).

NOT unified (deliberately, per the audit §2/§24): the
matrix/spectral entropy `Information.EntropyDefs.entropy`
is a different mathematical object (cfc of a PSD matrix);
it is related to the classical H only through the
diagonal-entropy bridge hypothesis of DiscreteFannes.
-/

open scoped BigOperators

namespace Hagi.Canonical

variable {V : Type*} [Fintype V]

/-- THE Kullback–Leibler divergence (canonical). -/
noncomputable def KL (q p : V → ℝ) : ℝ := Hagi.Prelude.klDef q p

/-- THE Shannon entropy (canonical). -/
noncomputable def H (p : V → ℝ) : ℝ := Hagi.Prelude.entDef p

/-- THE total variation distance, half-L1 (canonical). -/
noncomputable def TV (p q : V → ℝ) : ℝ := Hagi.Prelude.tvDef p q

/-- THE cross-entropy CE_q(p) = −Σ q·log p (canonical;
matches Data.Distill.crossEntropy). -/
noncomputable def CE (q p : V → ℝ) : ℝ := -∑ v, q v * Real.log (p v)

/-! ## Bridge theorems: every variant IS the canonical form -/

theorem klDiv_eq_canonical (q p : V → ℝ) :
    Hagi.klDiv q p = KL q p := rfl

theorem KLdiv_eq_canonical (q p : V → ℝ) :
    Hagi.KLdiv q p = KL q p := rfl

-- (the Energy.FreeEnergy.kldiv bridge lives in
-- Energy/FreeEnergy.lean itself: same-layer import rule)

theorem shannonEntropy_eq_canonical (p : V → ℝ) :
    Hagi.shannonEntropy p = H p := rfl

theorem shannon_eq_canonical {ι : Type*} [Fintype ι]
    (p : ι → ℝ) :
    Hagi.Quantum.GAD.shannon p = -∑ i, p i * Real.log (p i) := by
  have h1 : Hagi.Quantum.GAD.shannon p
      = ∑ i, Real.negMulLog (p i) := rfl
  have h2 : ∀ i : ι, Real.negMulLog (p i)
      = -(p i * Real.log (p i)) := fun i => by
    unfold Real.negMulLog
    ring
  rw [h1, Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_neg_distrib]

theorem tvDist_eq_canonical {W : Type} [Fintype W] [Nonempty W]
    (p q : W → ℝ) :
    Hagi.Data.tvDist p q = (∑ v, |p v - q v|) / 2 := rfl

theorem tvHalf_eq_canonical {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    Hagi.Quantum.GAD.tvHalf p q = (∑ i, |p i - q i|) / 2 := rfl

/-- The canonical cross-entropy matches the Distill
definition (same carrier, same form). -/
theorem crossEntropy_eq_canonical (q p : V → ℝ) :
    Hagi.Canonical.CE q p = Hagi.crossEntropy (V := V) q p := rfl

/-! ## The canonical identity block (one place) -/

/-- KL is the excess cross-entropy over the entropy
baseline — the canonical form of the R198 law. -/
theorem kl_excess_cross_entropy (q p : V → ℝ)
    (hq : ∀ v, q v ≠ 0) (hp : ∀ v, p v ≠ 0) :
    KL q p = CE q p - CE q q := by
  have h1 : ∀ x : V → ℝ, CE q x = -∑ v, q v * Real.log (x v) := by
    intro x; exact rfl
  unfold KL
  rw [h1 p, h1 q]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun v _ => by
    rw [Real.log_div (hq v) (hp v)]
    ring)

end Hagi.Canonical

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
import Hagi.Data.Distill
import Hagi.Data.DField
import Hagi.Data.FannesSmooth
import Hagi.Data.DistillRecursion
import Hagi.Data.DField

set_option linter.style.header false

/-!
# InfoNCE — нижняя граница взаимной информации

Формализация ядра InfoNCE-неравенства (van den Oord et al.,
«Representation Learning with Contrastive Predictive Coding»;
корпус-подтверждение: SSL-HSICIC 2106.08320 — «InfoNCE, a
variational lower bound on the mutual information»):
контрастивный лосс (кросс-энтропия softmax-модели против
целевого индекса) НЕ МОЖЕТ опуститься ниже энтропии цели —
потому log K − L_NCE ≤ log K − H: InfoNCE-оценка никогда не
переоценивает взаимную информацию.

Доказано (на канонических CE/KL/H из Data/Canonical):
* `ce_ge_entropy`: CE q p ≥ H q — кросс-энтропия не ниже
  собственной энтропии цели;
* `infonce_never_overestimates`: log k − CE q p ≤
  log k − H q — InfoNCE-оценка MI не выше log K − H(q);
* `infonce_gap_is_kl`: зазор «MI − InfoNCE-оценка» — ТОЧНО
  KL(post ‖ model): контрастивная оценка терминально точна
  ⟺ модель равна постериору.

Плановая переформулировка IB-строк (§2 плана): вместо
НЕоцениваемого MI — surrogate-bound; здесь он доказан.
-/

open Finset

/-!
# Canonical — ONE definition per information-theoretic
concept (; architecture audit P0-1, stage 0/1;
lives in Data for LayerLint reasons: bridges Data+Energy)

The audit found the same mathematical objects under 3–4
names (KL, entropy, TV). The pass already bridged some
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

* KL:  Data.Distill.klDiv (delegate,),
       Data.DField (rfl; сам KLdiv удалён, аудит 2026-10-24,),
       Energy.FreeEnergy.kldiv (new bridge below);
* H:   Data.DistillRecursion.shannonEntropy (new),
       Information.DiscreteFannes.shannon (new);
* TV:  Data.FannesSmooth.tvDist (rfl,),
       Information.DiscreteFannes.tvHalf (new).

not unified (deliberately, per the audit §2/§24): the
matrix/spectral entropy `Information.EntropyDefs.entropy`
is a different mathematical object (cfc of a PSD matrix);
it is related to the classical H only through the
diagonal-entropy bridge hypothesis of DiscreteFannes.
-/

open scoped BigOperators

namespace Hagi.Data

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



-- (the Energy.FreeEnergy.kldiv bridge lives in
-- Energy/FreeEnergy.lean itself: same-layer import rule)


theorem shannon_eq_canonical {ι : Type*} [Fintype ι]
    (p : ι → ℝ) :
    Hagi.Information.shannon p = -∑ i, p i * Real.log (p i) := by
  have h1 : Hagi.Information.shannon p
      = ∑ i, Real.negMulLog (p i) := rfl
  have h2 : ∀ i : ι, Real.negMulLog (p i)
      = -(p i * Real.log (p i)) := fun i => by
    unfold Real.negMulLog
    ring
  rw [h1, Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_neg_distrib]


theorem tvHalf_eq_canonical {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    Hagi.Information.tvHalf p q = (∑ i, |p i - q i|) / 2 := rfl

/-- The canonical cross-entropy matches the Distill
definition (same carrier, same form). -/
theorem crossEntropy_eq_canonical (q p : V → ℝ) :
    Hagi.Data.CE q p = Hagi.crossEntropy (V := V) q p := rfl

/-! ## The canonical identity block (one place) -/

/-- KL is the excess cross-entropy over the entropy
baseline — the canonical form of the law. -/
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

end Hagi.Data

open Finset

namespace Hagi.Data

variable {V : Type} [Fintype V] [DecidableEq V]

/-- CE q q в точности равен энтропии H q (знак-соглашения
канонических определений совпадают). -/
theorem ce_self_eq_entropy (q : V → ℝ) :
    Hagi.Data.CE q q = Hagi.Data.H q := rfl

/-- Кросс-энтропия не ниже энтропии цели: CE q p ≥ H q
(KL ≥ 0 в ce-разложении kl_excess_cross_entropy). -/
theorem ce_ge_entropy (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    Hagi.Data.H q ≤ Hagi.Data.CE q p := by
  have hex := Hagi.Data.kl_excess_cross_entropy q p
    (fun v => ne_of_gt (hq v))
    (fun v => ne_of_gt (hp v))
  have hkl : 0 ≤ Hagi.Data.KL q p :=
    Hagi.kl_nonneg q p hq hp hsumq hsump
  rw [ce_self_eq_entropy] at hex
  linarith [hex, hkl]

/-- InfoNCE никогда не переоценивает MI: log k − лосс
не выше log k − энтропийного пола. -/
theorem infonce_never_overestimates (k : ℝ) (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    k - Hagi.Data.CE q p ≤ k - Hagi.Data.H q := by
  have h := ce_ge_entropy q p hsumq hsump hq hp
  linarith

/-- Зазор «MI − InfoNCE-оценка» — ТОЧНО KL(post ‖ model):
контрастивная оценка терминально точна ⟺ модель совпадает
с постериором (зазор нулевой ⟺ KL нулевой). -/
theorem infonce_gap_is_kl (k : ℝ) (q p : V → ℝ)
    (hq : ∀ v, q v ≠ 0) (hp : ∀ v, p v ≠ 0) :
    (k - Hagi.Data.H q) - (k - Hagi.Data.CE q p)
      = Hagi.Data.KL q p := by
  have hex := Hagi.Data.kl_excess_cross_entropy q p hq hp
  rw [ce_self_eq_entropy] at hex
  linarith

end Hagi.Data

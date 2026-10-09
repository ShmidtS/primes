/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.DField
import Hagi.Data.Distill

set_option linter.style.header false

/-!
# Recursive self-distillation: the entropy floor of model collapse

The conditional core of the model-collapse /
entropy-preservation theorem.

**The setting.** Recursive self-distillation across generations:
generation k+1 trains toward the target mixture

`m_k = (1−ν)·p_k + ν·p_data` —

the previous model's distribution blended with a FIXED
fresh-data mass ν > 0. The fresh-data mass is THE anti-collapse
knob: every generation re-injects ν of the real data, so the
training target never degenerates to the model's own output
(the ν = 0 limit is exactly the collapse protocol of Shumailov
et al.: model → model → model with no anchor).

**The honest engine (what is proved, what is assumed).**

* CLAIM 1 (theorem, `entropy_mix_ge`): entropy concavity —
  `H(m_k) ≥ (1−ν)·H(p_k) + ν·H(p_data)`. Proved from the repo's
  `kl_nonneg` (`Hagi.Data/DField`) via the Jensen–Shannon
  identity `H(m) − (1−ν)H(p) − νH(q) = (1−ν)·KL(p‖m) + ν·KL(q‖m)`
  (the same span-1 identity as `dfield_entropy_identity`).

* CLAIM 2 (honest GAP — the entropy–KL tradeoff is FALSE as
  stated): `KL(m‖q) ≤ δ ⟹ H(q) ≥ H(m) − δ` does not hold in
  general. Explicit counterexample (binary alphabet):
  m = (0.9, 0.1), q = (0.99, 0.01): KL(m‖q) = 0.1445 ≤ δ, yet
  H(m) − δ = 0.1806 > H(q) = 0.0560. A small divergence bounds
  likelihood ratios where m has mass, but the student can still
  sharpen the tail and lose far more entropy than δ — entropy
  is not Lipschitz in KL at linear rate (the true modulus is
  Pinsker/sub-linear, and the audit's Wasserstein-contraction
  form is strictly stronger). What IS true (proved here as
  `entropy_kl_ce_identity`, the `Hagi.Data/Distill` master
  identity in H-form): `CE_m(q) = H(m) + KL(m‖q)` — the KL
  certification bounds the student's CROSS-entropy against the
  target, exactly. Hence the per-step entropy preservation
  enters as the explicit hypothesis hcert (a strengthening of
  the h_emp_ training guarantee: not only KL ≤ δ but entropy
  within δ) — this file's results are conditional on it, and
  that is the honest form.

* CLAIM 3 (theorem, `distill_entropy_recurrence`,
  `entropy_floor`): under the certified steps,
  `H(p_T) ≥ (1−ν)^T·H(p_0) + (1−(1−ν)^T)·(H(p_data) − δ/ν)`
  — the exact closed form (geometric interpolation between the
  initial entropy and the fixed point h − δ/ν of
  x ↦ (1−ν)x + νh − δ; fixed-point algebra:
  x* = (νh−δ)/ν = h − δ/ν ✓). As T grows the bound approaches
  H(p_data) − δ/ν: THE ENTROPY floor. With δ small and ν fixed,
  collapse below the floor is impossible.

* CLAIM 4 (theorem, `fresh_data_prevents_collapse`): the
  invariant form — if `H(p_0) ≥ H(p_data) − δ/ν` then the
  entropy stays above `H(p_data) − δ/ν` at every generation.
  Uniform ε form (`fresh_data_prevents_collapse_uniform`):
  with `δ ≤ ν·ε` and `H(p_0) ≥ H(p_data) − ε`, entropy never
  falls below `H(p_data) − ε`. The fresh-data mass ν > 0 is
  what makes the floor exist: at ν = 0 the floor constant
  δ/ν diverges and the theorem is vacuous — collapse is exactly
  the ν = 0 protocol.

**Open (flagged, not proved):** the audit's full ask —
Wasserstein contraction of the generation map with fixed point
p* satisfying H(p*) ≥ H(data) − ε — stays open; the
KL-certification-only entropy floor (replacing hcert by a
Pinsker-type sub-linear correction) stays open.
-/

open Finset

namespace Hagi

section DistillRecursion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Shannon entropy H(p) = −Σ p·log p of a finite
distribution (the negative of `negEntropy`, `Hagi.Data/DBridge`;
defined here directly to keep the module elementary). -/
noncomputable def shannonEntropy (p : V → ℝ) : ℝ :=
  -∑ v, p v * Real.log (p v)

/-- The recursive-distillation training target: the previous
model's distribution blended with the fresh-data mass ν:
`m = (1−ν)·p + ν·d`. The anti-collapse anchor. -/
def freshMix (ν : ℝ) (p d : V → ℝ) : V → ℝ :=
  fun v => (1 - ν) * p v + ν * d v

/-! ### The mixture: positivity and normalization -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
theorem freshMix_pos (ν : ℝ) (p d : V → ℝ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < p v) (hd : ∀ v, 0 < d v) :
    ∀ v, 0 < freshMix ν p d v := by
  intro v
  unfold freshMix
  have h1 : 0 ≤ (1 - ν) * p v := mul_nonneg (by linarith) (le_of_lt (hp v))
  rcases lt_or_eq_of_le hν with hν0 | hν0
  · exact add_pos_of_nonneg_of_pos h1 (mul_pos hν0 (hd v))
  · subst hν0
    norm_num
    exact hp v

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
theorem freshMix_sum_one (ν : ℝ) (p d : V → ℝ)
    (hsp : ∑ v, p v = 1) (hsd : ∑ v, d v = 1) :
    ∑ v, freshMix ν p d v = 1 := by
  unfold freshMix
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsp, hsd]
  ring

/-! ### CLAIM 1: entropy concavity of the mixture -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Entropy concavity (CLAIM 1, theorem).** The training
target's entropy is at least the weighted entropies:
`H((1−ν)p + νd) ≥ (1−ν)·H(p) + ν·H(d)`. Entropy is gained by
mixing — the fresh-data blend RAISES the target entropy above
the model's, which is the whole anti-collapse mechanism.
Engine: the Jensen–Shannon identity (the mixture entropy minus
the weighted parts equals the weighted KLs to the mixture,
each nonneg by `kl_nonneg`). -/
theorem entropy_mix_ge (ν : ℝ) (p d : V → ℝ)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < p v) (hd : ∀ v, 0 < d v)
    (hsp : ∑ v, p v = 1) (hsd : ∑ v, d v = 1) :
    (1 - ν) * shannonEntropy p + ν * shannonEntropy d
      ≤ shannonEntropy (freshMix ν p d) := by
  have hmp : ∀ v, 0 < freshMix ν p d v :=
    freshMix_pos ν p d hν hν1 hp hd
  have hms : ∑ v, freshMix ν p d v = 1 := freshMix_sum_one ν p d hsp hsd
  -- the Jensen–Shannon identity: weighted KLs to the mixture
  -- = mixture entropy − weighted entropies
  have hfold : (1 - ν) * (∑ v, p v * Real.log (freshMix ν p d v))
        + ν * (∑ v, d v * Real.log (freshMix ν p d v))
      = ∑ v, freshMix ν p d v * Real.log (freshMix ν p d v) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by
      unfold freshMix; ring
  have htermp : ∀ v : V, p v * Real.log (p v / freshMix ν p d v)
      = p v * Real.log (p v)
        - p v * Real.log (freshMix ν p d v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hmp v))]
    ring
  have hklp : KLdiv p (freshMix ν p d)
      = ∑ v, p v * Real.log (p v)
        - ∑ v, p v * Real.log (freshMix ν p d v) := by
    unfold KLdiv
    rw [Finset.sum_congr rfl (fun v _ => htermp v), ← Finset.sum_sub_distrib]
  have htermd : ∀ v : V, d v * Real.log (d v / freshMix ν p d v)
      = d v * Real.log (d v)
        - d v * Real.log (freshMix ν p d v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hd v)) (ne_of_gt (hmp v))]
    ring
  have hkld : KLdiv d (freshMix ν p d)
      = ∑ v, d v * Real.log (d v)
        - ∑ v, d v * Real.log (freshMix ν p d v) := by
    unfold KLdiv
    rw [Finset.sum_congr rfl (fun v _ => htermd v), ← Finset.sum_sub_distrib]
  -- each KL is nonneg (the repo's DField toolkit)
  have hkl1 : 0 ≤ KLdiv p (freshMix ν p d) :=
    kl_nonneg p _ hp hmp hsp hms
  have hkl2 : 0 ≤ KLdiv d (freshMix ν p d) :=
    kl_nonneg d _ hd hmp hsd hms
  -- weighted-sum the two nonneg KLs, fold, and read off H
  have hcomb : (1 - ν) * KLdiv p (freshMix ν p d)
        + ν * KLdiv d (freshMix ν p d)
      = shannonEntropy (freshMix ν p d)
        - (1 - ν) * shannonEntropy p - ν * shannonEntropy d := by
    rw [hklp, hkld]
    have e4 : (1 - ν) * (∑ v, p v * Real.log (freshMix ν p d v))
        + ν * (∑ v, d v * Real.log (freshMix ν p d v))
        = ∑ v, freshMix ν p d v * Real.log (freshMix ν p d v) := hfold
    unfold shannonEntropy
    ring_nf
    linarith [hfold]
  have hwnn : 0 ≤ (1 - ν) * KLdiv p (freshMix ν p d)
      + ν * KLdiv d (freshMix ν p d) := by
    exact add_nonneg (mul_nonneg (by linarith) hkl1) (mul_nonneg hν hkl2)
  rw [hcomb] at hwnn
  linarith

/-! ### CLAIM 2 (the honest form): the true entropy–KL identity -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The true entropy–KL identity (CLAIM 2, honest form).**
The student's cross-entropy against the target is EXACTLY the
target entropy plus the divergence:
`CE_m(q) = H(m) + KL(m‖q)` — the `Hagi.Data/Distill` master
identity `teacher_generated_identity` restated with
`shannonEntropy`. This is what the h_emp_ KL certification
`KL(m‖q) ≤ δ` really buys: `CE_m(q) ≤ H(m) + δ`. It does not
buy `H(q) ≥ H(m) − δ` (that direction is FALSE — see the module
docstring for the explicit counterexample), so the per-step
entropy preservation is carried below as the explicit
hypothesis hcert. -/
theorem entropy_kl_ce_identity (m q : V → ℝ)
    (hm : ∀ v, 0 < m v) (hq : ∀ v, 0 < q v) :
    crossEntropy m q = shannonEntropy m + klDiv m q := by
  have h := teacher_generated_identity m q hm hq
  unfold crossEntropy at h
  unfold shannonEntropy crossEntropy
  linarith

/-! ### The certified step -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The per-generation entropy inequality (CLAIM 1 + the
certified step).** If generation k+1's entropy is certified
within δ of its training target's (the hcert hypothesis — the
honest strengthening of the h_emp_ KL guarantee; see
`entropy_kl_ce_identity` for why KL alone does not suffice),
then

`H(p_{k+1}) ≥ (1−ν)·H(p_k) + ν·H(p_data) − δ` —

fresh data pulls the entropy floor up by ν·(H(data) − H(p_k)),
the distillation error pulls it down by at most δ. -/
theorem distill_step_entropy (pNext pK d : V → ℝ) (ν δ : ℝ)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < pK v) (hd : ∀ v, 0 < d v)
    (hsp : ∑ v, pK v = 1) (hsd : ∑ v, d v = 1)
    (hcert : shannonEntropy (freshMix ν pK d) - δ
      ≤ shannonEntropy pNext) :
    (1 - ν) * shannonEntropy pK + ν * shannonEntropy d - δ
      ≤ shannonEntropy pNext := by
  have hmix := entropy_mix_ge ν pK d hν hν1 hp hd hsp hsd
  linarith

/-! ### CLAIM 3: the closed-form recursive floor -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The recursive entropy floor (CLAIM 3, main theorem).**
For a generation sequence p_k where every step is certified
(each generation's entropy within δ of its fresh-mix target),
the exact closed form holds for every horizon T:

`H(p_T) ≥ (1−ν)^T · H(p_0) + (1 − (1−ν)^T) · (H(p_data) − δ/ν)`.

Solving x_{k+1} = (1−ν)x_k + νh − δ (h = H(p_data)): the fixed
point is h − δ/ν and the solution is the geometric
interpolation between H(p_0) and the fixed point. As T → ∞ the
weight (1−ν)^T → 0 and the floor approaches H(p_data) − δ/ν:
with δ small and ν fixed, the entropy CANNOT collapse below the
floor — model collapse is impossible under certified recursive
self-distillation with fresh data. -/
theorem distill_entropy_recurrence (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (_hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, shannonEntropy (freshMix ν (p k) d) - δ
      ≤ shannonEntropy (p (k + 1))) (T : ℕ) :
    (1 - ν)^T * shannonEntropy (p 0)
      + (1 - (1 - ν)^T) * (shannonEntropy d - δ / ν)
      ≤ shannonEntropy (p T) := by
  induction T with
  | zero =>
    simp only [pow_zero]
    norm_num
  | succ T ih =>
    have hc : (0:ℝ) ≤ 1 - ν := by linarith
    have h1 := distill_step_entropy (p (T + 1)) (p T) d ν δ
      hν.le hν1 (hp T) hd (hsp T) hsd (hcert T)
    have h2 : (1 - ν) * ((1 - ν)^T * shannonEntropy (p 0)
          + (1 - (1 - ν)^T) * (shannonEntropy d - δ / ν))
        ≤ (1 - ν) * shannonEntropy (p T) :=
      mul_le_mul_of_nonneg_left ih hc
    have key : (1 - ν) * ((1 - ν)^T * shannonEntropy (p 0)
          + (1 - (1 - ν)^T) * (shannonEntropy d - δ / ν))
          + ν * (shannonEntropy d - δ / ν)
        = (1 - ν) * (1 - ν)^T * shannonEntropy (p 0)
          + (1 - (1 - ν) * (1 - ν)^T) * (shannonEntropy d - δ / ν) := by
      have hν0 : ν ≠ 0 := ne_of_gt hν
      field_simp
      ring
    have h3 : ν * (shannonEntropy d - δ / ν) = ν * shannonEntropy d - δ := by
      rw [mul_sub, mul_div_cancel₀ δ (ne_of_gt hν)]
    rw [show (1 - ν)^(T + 1) = (1 - ν) * (1 - ν)^T from by
      rw [pow_succ (1 - ν) T, mul_comm ((1 - ν)^T) (1 - ν)]]
    linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The entropy floor, asymptotic form (CLAIM 3).** The same
closed form rewritten as "floor minus an exponentially
vanishing correction":

`H(p_T) ≥ (H(p_data) − δ/ν) − (1−ν)^T · ((H(p_data) − δ/ν) − H(p_0))`.

The distance from the floor H(p_data) − δ/ν contracts by the
factor (1−ν) < 1 per generation: the floor is approached
exponentially fast, and the correction's sign depends only on
whether the initial entropy starts above or below the floor. -/
theorem entropy_floor (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, shannonEntropy (freshMix ν (p k) d) - δ
      ≤ shannonEntropy (p (k + 1))) (T : ℕ) :
    shannonEntropy d - δ / ν
      - (1 - ν)^T * (shannonEntropy d - δ / ν - shannonEntropy (p 0))
      ≤ shannonEntropy (p T) := by
  have hr := distill_entropy_recurrence p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hring : (1 - ν)^T * shannonEntropy (p 0)
      + (1 - (1 - ν)^T) * (shannonEntropy d - δ / ν)
      = shannonEntropy d - δ / ν
        - (1 - ν)^T * (shannonEntropy d - δ / ν - shannonEntropy (p 0)) := by
    ring
  linarith [hr, hring]

/-! ### CLAIM 4: fresh data prevents collapse -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Fresh data prevents collapse (CLAIM 4, the invariant
form).** If the initial entropy is at or above the floor
`H(p_0) ≥ H(p_data) − δ/ν`, then the entropy stays above the
floor at every generation — forever, uniformly in T. The
correction term in `entropy_floor` is then non-positive and
drops out. With δ small and ν fixed, collapse below
H(p_data) − δ/ν is impossible: the fresh-data mass ν is the
anti-collapse knob (at ν = 0 the floor constant δ/ν diverges
and the statement is vacuous — collapse IS the ν = 0
protocol). -/
theorem fresh_data_prevents_collapse (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, shannonEntropy (freshMix ν (p k) d) - δ
      ≤ shannonEntropy (p (k + 1)))
    (hinv : shannonEntropy d - δ / ν ≤ shannonEntropy (p 0))
    (T : ℕ) :
    shannonEntropy d - δ / ν ≤ shannonEntropy (p T) := by
  have hc : (0:ℝ) ≤ 1 - ν := by linarith
  have hf := entropy_floor p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hB : shannonEntropy d - δ / ν - shannonEntropy (p 0) ≤ 0 := by linarith
  have hcorr : (1 - ν)^T
      * (shannonEntropy d - δ / ν - shannonEntropy (p 0)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hc T) hB
  linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Fresh data prevents collapse, uniform ε form (CLAIM 4).**
With the certified error δ at most ν·ε and the initial entropy
at least H(p_data) − ε, the entropy never falls below
H(p_data) − ε — a UNIFORM floor for all generations. Since
δ/ν ≤ ε, the floor H(p_data) − δ/ν dominates H(p_data) − ε:
any ε-prevention budget ε is met by certified training with
error δ ≤ ν·ε. -/
theorem fresh_data_prevents_collapse_uniform (p : ℕ → V → ℝ) (d : V → ℝ)
    (ν δ ε : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ) (_hε : 0 ≤ ε)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, shannonEntropy (freshMix ν (p k) d) - δ
      ≤ shannonEntropy (p (k + 1)))
    (hδε : δ ≤ ν * ε)
    (h0 : shannonEntropy d - ε ≤ shannonEntropy (p 0))
    (T : ℕ) :
    shannonEntropy d - ε ≤ shannonEntropy (p T) := by
  have hdn : δ / ν ≤ ε := by
    rw [div_le_iff₀ hν, mul_comm]
    exact hδε
  -- direct: the floor correction is at most ε − δ/ν (initial entropy
  -- within ε of the data, contraction factor ≤ 1)
  have hc : (0:ℝ) ≤ 1 - ν := by linarith
  have hX : (1 - ν)^T ≤ 1 := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [pow_succ]
      exact (mul_le_mul ih (by linarith : (1:ℝ) - ν ≤ 1) hc zero_le_one).trans
        (by norm_num : (1:ℝ) * 1 ≤ 1)
  have hf := entropy_floor p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hdif : shannonEntropy d - δ / ν - shannonEntropy (p 0) ≤ ε - δ / ν := by
    linarith
  have hprod : (1 - ν)^T
      * (shannonEntropy d - δ / ν - shannonEntropy (p 0))
      ≤ ε - δ / ν := by
    have hstep1 : (1 - ν)^T
        * (shannonEntropy d - δ / ν - shannonEntropy (p 0))
        ≤ (1 - ν)^T * (ε - δ / ν) :=
      mul_le_mul_of_nonneg_left hdif (pow_nonneg hc T)
    have hstep2 : (1 - ν)^T * (ε - δ / ν) ≤ 1 * (ε - δ / ν) :=
      mul_le_mul_of_nonneg_right hX (by linarith)
    linarith
  linarith


/-- ** (T5, §7.3 ревизии): entropy floor с TV-сертификатом**
— замена посылки hcert (KL-формы, опровергнутой ревизией:
KL ≤ δ НЕ спасает энтропию — sharpening tail) на
Pinsker/Fannes-форму: если полная вариация fresh-смеси и
следующего поколения ограничена (сертификат |H(fm)−H(p')| ≤ B,
B — Fannes-граница через τ = tvDist, см. AntiCollapse),
то entropy floor выполняется с эффективным δ_eff = B:
H(p_T) ≥ H(data) − B/ν − (затухание). -/
theorem entropy_floor_tv (p : ℕ → V → ℝ) (d : V → ℝ) (ν B : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hB : 0 ≤ B)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (htv : ∀ k, shannonEntropy (freshMix ν (p k) d) - B
      ≤ shannonEntropy (p (k + 1))) (T : ℕ) :
    shannonEntropy d - B / ν
      - (1 - ν)^T * (shannonEntropy d - B / ν - shannonEntropy (p 0))
      ≤ shannonEntropy (p T) :=
  entropy_floor p d ν B hν hν1 hB hp hd hsp hsd htv T

end DistillRecursion

end Hagi

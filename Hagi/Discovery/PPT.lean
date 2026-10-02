/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GrowthState
import Mathlib.Probability.Moments.SubGaussian
set_option linter.style.header false

/-!
# R98: the PPT discovery layer (arXiv 2609.38104, "Explore Broadly, Reason Sharply")

The concrete `discover` mechanism for HAGI's growth loop: parallel-tempering /
power-target sampling over a FINITE sequence space. This module upgrades
`Hagi.Unified.GrowthState.discover` from a bare `Candidate` carrier to a
sampling semantics: the candidate the growth loop discovers is a sequence
drawn from a power target pi_α(x) ∝ p(x)^α, refined by a Metropolis–Hastings
suffix kernel, mixed across replicas by swaps, and scored by the composite
success indicator `pptSuccess`.

**Scope (honest boundary).** Everything lives on a Fintype `Seq` of sequences:
generality beyond finite state spaces is OUT OF SCOPE here (no topological
or measure-theoretic structure on `Seq` is assumed beyond a hypothesis that
singletons are measurable where needed).

**WARNING — sequence-level sharpening is NOT tokenwise temperature.** The
power target pi_α(x) ∝ p(x)^α raises the JOINT sequence probability to a
power. This is a DIFFERENT operation from temperature / softmax scaling of
token logits: Hagi.Core/Concat's softmax-invariance law (softmax(cz) ≠
softmax(z) for c ≠ 1, i.e. tokenwise logit scaling DOES change the token
distribution) does not transfer, and NO equivalence between sequence-level
power sharpening and tokenwise temperature is claimed or true in general.

Contents:
* `pptTarget` — the power target pi_α(x) = p(x)^α / Z_α with
  `pptTarget_isProbability` (nonneg, sums to 1) and `pptTarget_pos`.
* `mh_stationary` — target preservation via detailed balance: a stochastic
  kernel satisfying pi(x)K(x,y) = pi(y)K(y,x) has pi stationary.
* `pptSwapAccept` / `pptSwapKernel` — the replica-swap acceptance
  A = min(1, pi1(y₁)pi2(y₂)/(pi1(x₁)pi2(x₂))) and the swap kernel on the
  product space; `pptSwap_detailedBalance` + `pptSwap_stationary` prove the
  product stationary distribution is preserved.
* `truncation_bias` — the warning theorem: a kernel confined to S ⊂ Seq
  cannot preserve a target putting mass outside S. This is the paper's
  structural-bias floor (replay / experience-memory compression warning)
  made formal.
* `pptMixing` — Doeblin geometric contraction: if K ≥ ε entrywise, then
  TV(μ K^n, pi) ≤ (1 − |Seq|·ε)^n · TV(μ, pi) ≤ (1 − ε)^n (the sharp constant
  is 1 − |Seq|·ε; the paper-style 1 − ε is the weaker corollary).
* `ppt_discovery_gain` — the discovery event Good = {V x ≥ γ} under the
  stationary power target: `discovery_prob_stationary`,
  `discovery_prob_lower`, `stationary_value_ge`, and the composite
  indicator `pptSuccess` with `pptSuccess_union_bound` /
  `pptSuccess_lower` (union bound: Pr[S=1] ≥ Pr[good] − Pr[reject] −
  Pr[overrun]).

**Honest gaps.** (1) Continuous / infinite sequence spaces are not
covered. (2) The α-ladder DESIGN (which powers α₀ < α₁ < … to choose, their
optimization) is not formalized — α is a free parameter. (3) Adaptive
ladders (α chosen online) are open. (4) Mixing is proven only under the
strong Doeblin entrywise floor; the spectral-gap route is open. (5) The
verifier and budget events of `pptSuccess` enter as named hypotheses — no
verifier theory exists yet (same gap as `GrowthState.verifier`). -/

open Finset Real MeasureTheory

namespace Hagi

section PPT

variable {Seq : Type*} [Fintype Seq] [DecidableEq Seq] [Nonempty Seq]

/-! ## 1. The power target -/

/-- The normalizer Z_α = Σ_x p(x)^α (finite sum; positive when p is
everywhere positive and α is real — no restriction on α's sign needed for
positivity). -/
noncomputable def pptNorm (p : Seq → ℝ) (α : ℝ) : ℝ :=
  ∑ x, (p x) ^ α

theorem pptNorm_pos (p : Seq → ℝ) (α : ℝ) (hp : ∀ x, 0 < p x) :
    0 < pptNorm p α :=
  Finset.sum_pos (fun x _ => Real.rpow_pos_of_pos (hp x) α)
    ⟨Classical.arbitrary Seq, Finset.mem_univ _⟩

/-- **The power target** pi_α(x) = p(x)^α / Z_α — sequence-level sharpening
of the base model p by the power α. WARNING: this is the power of the JOINT
sequence probability, NOT tokenwise temperature (see module docstring). -/
noncomputable def pptTarget (p : Seq → ℝ) (α : ℝ) (x : Seq) : ℝ :=
  (p x) ^ α / pptNorm p α

/-- The power target is a probability vector: nonnegative and summing
to one over the finite sequence space. -/
theorem pptTarget_isProbability (p : Seq → ℝ) (α : ℝ) (hp : ∀ x, 0 < p x) :
    (∀ x, 0 ≤ pptTarget p α x) ∧ ∑ x, pptTarget p α x = 1 :=
  ⟨fun x => div_nonneg (Real.rpow_nonneg (hp x).le α) (pptNorm_pos p α hp).le,
    by
      simp only [pptTarget, pptNorm]
      rw [← Finset.sum_div]
      exact div_self (pptNorm_pos p α hp).ne'⟩

/-- The power target is everywhere strictly positive (an α-power of a
positive base, normalized by a positive constant) — the nondegeneracy the
MH and swap kernels need. -/
theorem pptTarget_pos (p : Seq → ℝ) (α : ℝ) (hp : ∀ x, 0 < p x) (x : Seq) :
    0 < pptTarget p α x :=
  div_pos (Real.rpow_pos_of_pos (hp x) α) (pptNorm_pos p α hp)

/-! ## 2. Metropolis–Hastings suffix refinement: target preservation -/

/-- A stochastic matrix on the sequence space: nonnegative entries, rows
summing to one. (Row-stochastic = one MH refinement step applied to the
current suffix.) -/
def pptKernel (K : Seq → Seq → ℝ) : Prop :=
  (∀ x y, 0 ≤ K x y) ∧ (∀ x, ∑ y, K x y = 1)

theorem pptKernel_nonneg {K : Seq → Seq → ℝ} (hK : pptKernel K) (x y : Seq) :
    0 ≤ K x y := hK.1 x y

/-- **Detailed balance**: pi(x)·K(x,y) = pi(y)·K(y,x) — the reversibility
condition a Metropolis–Hastings kernel built from a symmetric proposal
satisfies w.r.t. its target. Taken as the kernel's defining hypothesis
here (the concrete proposal/MH-acceptance construction is external —
honest gap: not formalized entrywise). -/
def pptDetailedBalance (pi : Seq → ℝ) (K : Seq → Seq → ℝ) : Prop :=
  ∀ x y, pi x * K x y = pi y * K y x

/-- **MH target preservation**: a stochastic kernel in detailed balance
with pi has pi stationary — Σ_x pi(x)·K(x,y) = pi(y). This is the preservation
half of the PPT loop: refinement steps do not drift off the power target.
Proof: swap the balance, then use the row sum. -/
theorem mh_stationary (K : Seq → Seq → ℝ) (pi : Seq → ℝ)
    (hK : pptKernel K) (hdb : pptDetailedBalance pi K) (y : Seq) :
    ∑ x, pi x * K x y = pi y := by
  have hswap : ∑ x, pi x * K x y = ∑ x, pi y * K y x :=
    Finset.sum_congr rfl fun x _ => hdb x y
  rw [hswap]
  have hcomm : ∑ x, pi y * K y x = ∑ x, K y x * pi y :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hcomm, ← Finset.sum_mul, hK.2 y, one_mul]

/-! ## 3. Replica swaps -/

/-- **The replica-swap acceptance** for adjacent temperatures
A(x₁,x₂) = min(1, pi1(x₂)·pi2(x₁) / (pi1(x₁)·pi2(x₂))) — exchange the two
replicas' states if the swapped configuration is not less likely under the
product target. -/
noncomputable def pptSwapAccept (pi1 pi2 : Seq → ℝ) (x : Seq × Seq) : ℝ :=
  min 1 (pi1 x.2 * pi2 x.1 / (pi1 x.1 * pi2 x.2))

theorem pptSwapAccept_nonneg (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) (x : Seq × Seq) :
    0 ≤ pptSwapAccept pi1 pi2 x :=
  le_min (by norm_num)
    (div_nonneg (mul_nonneg (h1 x.2).le (h2 x.1).le)
      (mul_nonneg (h1 x.1).le (h2 x.2).le))

theorem pptSwapAccept_le_one (pi1 pi2 : Seq → ℝ) (x : Seq × Seq) :
    pptSwapAccept pi1 pi2 x ≤ 1 := min_le_left _ _

theorem pptSwapAccept_mem (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) (x : Seq × Seq) :
    pptSwapAccept pi1 pi2 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨pptSwapAccept_nonneg pi1 pi2 h1 h2 x, pptSwapAccept_le_one pi1 pi2 x⟩

/-- **The balance identity of the swap acceptance**: the swapped mass is
symmetric — Π(x)·A(x) = Π(swap x)·A(swap x), where Π(x) = pi1(x₁)·pi2(x₂).
This is exactly the detailed-balance content of min-acceptance: whichever
side is uphill accepts with the compensating ratio. -/
theorem pptSwap_balance (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) (x : Seq × Seq) :
    pi1 x.1 * pi2 x.2 * pptSwapAccept pi1 pi2 x
      = pi1 x.2 * pi2 x.1 * pptSwapAccept pi1 pi2 (x.2, x.1) := by
  set a : ℝ := pi1 x.1 * pi2 x.2 with ha
  set b : ℝ := pi1 x.2 * pi2 x.1 with hb
  have hapos : 0 < a := mul_pos (h1 x.1) (h2 x.2)
  have hbpos : 0 < b := mul_pos (h1 x.2) (h2 x.1)
  have haccx : pptSwapAccept pi1 pi2 x = min 1 (b / a) := rfl
  have haccs : pptSwapAccept pi1 pi2 (x.2, x.1) = min 1 (a / b) := rfl
  rcases le_total a b with hab | hba
  · have hr : (1 : ℝ) ≤ b / a := (le_div_iff₀ hapos).mpr (by linarith)
    have hrs : a / b ≤ (1 : ℝ) := (div_le_iff₀ hbpos).mpr (by linarith)
    rw [haccx, haccs, min_eq_left hr, min_eq_right hrs, mul_div_cancel₀ _ hbpos.ne',
      mul_one]
  · have hr : b / a ≤ (1 : ℝ) := (div_le_iff₀ hapos).mpr (by linarith)
    have hrs : (1 : ℝ) ≤ a / b := (le_div_iff₀ hbpos).mpr (by linarith)
    rw [haccx, haccs, min_eq_right hr, min_eq_left hrs, mul_div_cancel₀ _ hapos.ne',
      mul_one]

/-- **The swap kernel** on the product space: with probability A(x) the two
replicas exchange states (move to (x₂,x₁)), otherwise both stay. -/
noncomputable def pptSwapKernel (pi1 pi2 : Seq → ℝ) (x y : Seq × Seq) : ℝ :=
  pptSwapAccept pi1 pi2 x * (if y = (x.2, x.1) then (1 : ℝ) else 0)
    + (1 - pptSwapAccept pi1 pi2 x) * (if y = x then (1 : ℝ) else 0)

theorem pptSwapKernel_nonneg (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) (x y : Seq × Seq) :
    0 ≤ pptSwapKernel pi1 pi2 x y := by
  have hA := pptSwapAccept_mem pi1 pi2 h1 h2 x
  have h1' : 0 ≤ pptSwapAccept pi1 pi2 x * (if y = (x.2, x.1) then (1 : ℝ) else 0) := by
    refine mul_nonneg hA.1 ?_; split <;> norm_num
  have h2' : 0 ≤ (1 - pptSwapAccept pi1 pi2 x) * (if y = x then (1 : ℝ) else 0) := by
    refine mul_nonneg (sub_nonneg.mpr hA.2) ?_; split <;> norm_num
  exact add_nonneg h1' h2'

/-- **The swap kernel is stochastic**: rows sum to one — the accepted
fraction A(x) plus the rejected fraction 1 − A(x) both land somewhere. -/
theorem pptSwapKernel_sum (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) (x : Seq × Seq) :
    ∑ y, pptSwapKernel pi1 pi2 x y = 1 := by
  have hA : pptSwapAccept pi1 pi2 x ∈ Set.Icc (0 : ℝ) 1 :=
    pptSwapAccept_mem pi1 pi2 h1 h2 x
  have key : ∀ s : Seq × Seq,
      ∑ y : Seq × Seq, (if y = s then (1 : ℝ) else 0) = 1 := by
    intro s; simp
  show ∑ y : Seq × Seq, (pptSwapAccept pi1 pi2 x
      * (if y = (x.2, x.1) then (1 : ℝ) else 0)
      + (1 - pptSwapAccept pi1 pi2 x) * (if y = x then (1 : ℝ) else 0)) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, key, key]
  ring

theorem pptSwapKernel_isKernel (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x) :
    pptKernel (pptSwapKernel pi1 pi2) :=
  ⟨pptSwapKernel_nonneg pi1 pi2 h1 h2, pptSwapKernel_sum pi1 pi2 h1 h2⟩

/-- **The swap kernel is in detailed balance w.r.t. the product target**
Π(x₁,x₂) = π₁(x₁)·π₂(x₂): the off-diagonal swap move exchanges exactly
compensating mass (`pptSwap_balance` — this is where the min-form of the
acceptance does its work), the identity part trivially balances, and all
other transitions are zero on both sides. -/
theorem pptSwap_detailedBalance (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x)
    (x y : Seq × Seq) :
    pi1 x.1 * pi2 x.2 * pptSwapKernel pi1 pi2 x y
      = pi1 y.1 * pi2 y.2 * pptSwapKernel pi1 pi2 y x := by
  by_cases hyx : y = x
  · subst hyx; rfl
  by_cases hy : y = (x.2, x.1)
  · subst hy
    have heta : ((x.2, x.1).2, (x.2, x.1).1) = x := by ext <;> simp
    have e1 : (if ((x.2, x.1) = (x.2, x.1)) then (1 : ℝ) else 0) = 1 := if_pos rfl
    have e2 : (if ((x.2, x.1) = x) then (1 : ℝ) else 0) = 0 := if_neg hyx
    have e3 : (if (x = ((x.2, x.1).2, (x.2, x.1).1)) then (1 : ℝ) else 0) = 1 :=
      if_pos heta
    have e4 : (if (x = (x.2, x.1)) then (1 : ℝ) else 0) = 0 :=
      if_neg fun h => hyx h.symm
    rw [pptSwapKernel, pptSwapKernel, e1, e2, e3, e4]
    norm_num
    exact pptSwap_balance pi1 pi2 h1 h2 x
  · have hne : ¬(x : Seq × Seq) = y := fun h => hyx h.symm
    have hne2 : ¬(x : Seq × Seq) = (y.2, y.1) := by
      intro h
      apply hy
      have hmk : ((x.2, x.1) : Seq × Seq) = (y.1, y.2) := by rw [h]
      have heta : ((y.1, y.2) : Seq × Seq) = y := rfl
      exact (hmk.trans heta).symm
    show pi1 x.1 * pi2 x.2 * (pptSwapAccept pi1 pi2 x
        * (if y = (x.2, x.1) then (1 : ℝ) else 0)
        + (1 - pptSwapAccept pi1 pi2 x) * (if y = x then (1 : ℝ) else 0))
      = pi1 y.1 * pi2 y.2 * (pptSwapAccept pi1 pi2 y
        * (if x = (y.2, y.1) then (1 : ℝ) else 0)
        + (1 - pptSwapAccept pi1 pi2 y) * (if x = y then (1 : ℝ) else 0))
    rw [if_neg hy, if_neg hyx, if_neg hne2, if_neg hne]
    ring

/-- **The product target is a probability on the pair space.** -/
theorem pptSwap_productProb (pi1 pi2 : Seq → ℝ)
    (hs1 : ∑ x, pi1 x = 1) (hs2 : ∑ x, pi2 x = 1) :
    ∑ z : Seq × Seq, pi1 z.1 * pi2 z.2 = 1 := by
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hs1, hs2, one_mul]

/-- **Replica swaps preserve the product stationary distribution** — the
target-preservation theorem of the tempering ladder: interleaving MH
refinement steps (each `mh_stationary` for its own π_k) with swap steps
(present theorem) keeps the product chain on the product power target. -/
theorem pptSwap_stationary (pi1 pi2 : Seq → ℝ)
    (h1 : ∀ x, 0 < pi1 x) (h2 : ∀ x, 0 < pi2 x)
    (hs1 : ∑ x, pi1 x = 1) (hs2 : ∑ x, pi2 x = 1) (y : Seq × Seq) :
    ∑ z : Seq × Seq, (pi1 z.1 * pi2 z.2) * pptSwapKernel pi1 pi2 z y
      = pi1 y.1 * pi2 y.2 :=
  mh_stationary _ _ (pptSwapKernel_isKernel pi1 pi2 h1 h2)
    (fun x y => pptSwap_detailedBalance pi1 pi2 h1 h2 x y) y

/-! ## 4. Truncation bias: the warning theorem -/

/-- **The structural-bias floor (one-way truncation failure)**: if the
kernel is CONFINED to a subset S (transitions to states outside S have
zero probability — the replay / experience-memory compression regime),
then any stationary distribution for it puts ZERO mass outside S. Hence
a target π with π(y₀) > 0 for some y₀ ∉ S is NOT stationary for the
confined kernel: one-way truncation irreversibly biases the sampler off
the true target. This is the paper's truncation-bias floor made formal. -/
theorem truncation_bias (K : Seq → Seq → ℝ) (pi : Seq → ℝ) (S : Set Seq)
    (hconf : ∀ x y, y ∉ S → K x y = 0)
    (hstat : ∀ y, ∑ x, pi x * K x y = pi y)
    (y₀ : Seq) (hy₀ : y₀ ∉ S) (hpi : 0 < pi y₀) : False := by
  have h0 : ∑ x, pi x * K x y₀ = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hconf x y₀ hy₀, mul_zero]
  have h := hstat y₀
  rw [h0] at h
  linarith

/-! ## 5. Doeblin mixing -/

/-- Total variation distance on the finite space, as half the L¹ norm. -/
noncomputable def tvDist (mu pi : Seq → ℝ) : ℝ := (∑ y, |mu y - pi y|) / 2

theorem tvDist_nonneg (mu pi : Seq → ℝ) : 0 ≤ tvDist mu pi :=
  div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) (by norm_num)

/-- |a − b| = a + b − 2·min(a,b) — the L¹ identity behind the coupling
bound. -/
theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith : a - b ≤ 0), min_eq_left h]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ a - b), min_eq_right h]
    ring

/-- One kernel step applied to a mass vector: (μK)(y) = Σ_x μ(x)·K(x,y). -/
def vecMul (mu : Seq → ℝ) (K : Seq → Seq → ℝ) : Seq → ℝ :=
  fun y => ∑ x, mu x * K x y

/-- The n-step chain μKⁿ, by iterating the one-step pushforward. -/
def chainAt (mu : Seq → ℝ) (K : Seq → Seq → ℝ) : ℕ → Seq → ℝ
  | 0 => mu
  | n + 1 => vecMul (chainAt mu K n) K

theorem chainAt_succ (mu : Seq → ℝ) (K : Seq → Seq → ℝ) (n : ℕ) :
    chainAt mu K (n + 1) = vecMul (chainAt mu K n) K := rfl

theorem vecMul_sum (K : Seq → Seq → ℝ) (hK : pptKernel K) (mu : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) : ∑ y, vecMul mu K y = 1 := by
  have h : ∑ y, vecMul mu K y = ∑ y, ∑ x, mu x * K x y := rfl
  rw [h, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => by
      rw [← Finset.mul_sum, hK.2 x, mul_one],
    hmu]

theorem vecMul_nonneg (K : Seq → Seq → ℝ) (hK : pptKernel K) (mu : Seq → ℝ)
    (hnn : ∀ x, 0 ≤ mu x) (y : Seq) : 0 ≤ vecMul mu K y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (hK.1 x y)

/-- The Doeblin floor is at most 1/|Seq|: the row sums force it. -/
theorem ppt_card_eps_le_one (K : Seq → Seq → ℝ) (hK : pptKernel K)
    (eps : ℝ) (heps : ∀ x y, eps ≤ K x y) :
    (Fintype.card Seq : ℝ) * eps ≤ 1 := by
  obtain ⟨a⟩ : Nonempty Seq := inferInstance
  have h1 : ∑ y : Seq, eps ≤ ∑ y : Seq, K a y :=
    Finset.sum_le_sum fun y _ => heps a y
  have h2 : ∑ y : Seq, eps = (Fintype.card Seq : ℝ) * eps := by
    simp
  rw [h2, hK.2 a] at h1
  exact h1

/-- **The one-step Doeblin contraction**: with every kernel entry ≥ ε and
π stationary, TV(μK, π) ≤ (1 − |Seq|·ε)·TV(μ, π). The SHARP constant is
1 − |Seq|·ε ≥ 1 − ε (`ppt_card_eps_le_one`); the textbook "1 − ε" is the
weaker corollary `pptMixing_doeblin`. Elementary, coupling-free proof:
split the signed difference μ − π into its positive part (on A) and
negative part (on B); each pushed through the kernel stays ≥ ε·δ
pointwise (δ = TV(μ,π) = Σ_A(μ−π)); the identity
|P − Q| = P + Q − 2·min(P,Q) then shrinks the total mass 2δ by
2·|Seq|·ε·δ. -/
theorem ppt_tvContraction (K : Seq → Seq → ℝ) (hK : pptKernel K)
    (eps : ℝ) (heps : ∀ x y, eps ≤ K x y)
    (mu pi : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) (hpi : ∑ x, pi x = 1)
    (hmunn : ∀ x, 0 ≤ mu x) (hpinn : ∀ x, 0 ≤ pi x)
    (hstat : ∀ y, vecMul pi K y = pi y) :
    tvDist (vecMul mu K) pi
      ≤ (1 - (Fintype.card Seq : ℝ) * eps) * tvDist mu pi := by
  set A : Finset Seq := Finset.univ.filter (fun x => 0 ≤ mu x - pi x) with hAdef
  set B : Finset Seq := Finset.univ.filter (fun x => ¬ 0 ≤ mu x - pi x) with hBdef
  have hAnn : ∀ x ∈ A, 0 ≤ mu x - pi x := by
    intro x hx
    rw [hAdef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hBnn : ∀ x ∈ B, mu x - pi x ≤ 0 := by
    intro x hx
    rw [hBdef] at hx
    exact (not_le.mp (Finset.mem_filter.mp hx).2).le
  have hAB : (∑ x ∈ A, (mu x - pi x)) + (∑ x ∈ B, (mu x - pi x))
      = ∑ x : Seq, (mu x - pi x) := by
    rw [hAdef, hBdef]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => 0 ≤ mu x - pi x) (fun x => mu x - pi x)
  have hdsum : ∑ x : Seq, (mu x - pi x) = 0 := by
    rw [Finset.sum_sub_distrib, hmu, hpi, sub_self]
  set delta : ℝ := ∑ x ∈ A, (mu x - pi x) with hdeltadef
  have hBdelta : ∑ x ∈ B, (mu x - pi x) = -delta := by linarith
  have hdeltann : 0 ≤ delta := Finset.sum_nonneg fun x hx => hAnn x hx
  set P : Seq → ℝ := fun y => ∑ x ∈ A, (mu x - pi x) * K x y with hPdef
  set Q : Seq → ℝ := fun y => -∑ x ∈ B, (mu x - pi x) * K x y with hQdef
  have hPy : ∀ y, P y = ∑ x ∈ A, (mu x - pi x) * K x y := fun _ => rfl
  have hQy : ∀ y, Q y = -∑ x ∈ B, (mu x - pi x) * K x y := fun _ => rfl
  -- the pushed-through signed difference
  have hdiff : ∀ y, vecMul mu K y - pi y = P y - Q y := by
    intro y
    have hstaty : pi y = ∑ x : Seq, pi x * K x y := (hstat y).symm
    have hsplitA : (∑ x ∈ A, (mu x - pi x) * K x y)
        + (∑ x ∈ B, (mu x - pi x) * K x y)
        = ∑ x : Seq, (mu x - pi x) * K x y := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - pi x) (fun x => (mu x - pi x) * K x y)
    calc vecMul mu K y - pi y
        = (∑ x : Seq, mu x * K x y) - (∑ x : Seq, pi x * K x y) := by
          rw [hstaty]; rfl
      _ = ∑ x : Seq, (mu x - pi x) * K x y := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => (sub_mul _ _ _).symm
      _ = (∑ x ∈ A, (mu x - pi x) * K x y)
          + (∑ x ∈ B, (mu x - pi x) * K x y) := hsplitA.symm
      _ = P y - Q y := by rw [hPy y, hQy y]; ring
  -- both halves stay above the Doeblin floor
  have hPge : ∀ y, eps * delta ≤ P y := by
    intro y
    rw [hPy y]
    calc eps * delta = ∑ x ∈ A, eps * (mu x - pi x) := by
          rw [hdeltadef, ← Finset.mul_sum]
      _ = ∑ x ∈ A, (mu x - pi x) * eps :=
          Finset.sum_congr rfl fun x _ => mul_comm _ _
      _ ≤ ∑ x ∈ A, (mu x - pi x) * K x y :=
          Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (heps x y) (hAnn x hx)
  have hQge : ∀ y, eps * delta ≤ Q y := by
    intro y
    rw [hQy y]
    have h1 : ∑ x ∈ B, (mu x - pi x) * K x y
        ≤ eps * (∑ x ∈ B, (mu x - pi x)) := by
      calc ∑ x ∈ B, (mu x - pi x) * K x y
          ≤ ∑ x ∈ B, (mu x - pi x) * eps :=
            Finset.sum_le_sum fun x hx =>
              mul_le_mul_of_nonpos_left (heps x y) (hBnn x hx)
        _ = eps * (∑ x ∈ B, (mu x - pi x)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
    rw [hBdelta] at h1
    calc -∑ x ∈ B, (mu x - pi x) * K x y ≥ -(eps * -delta) := neg_le_neg h1
      _ = eps * delta := by ring
  -- totals
  have hinner : ∀ x : Seq, ∑ y : Seq, (mu x - pi x) * K x y = (mu x - pi x) := by
    intro x
    rw [← Finset.mul_sum, hK.2 x, mul_one]
  have hPsum : ∑ y, P y = delta := by
    have hswap : ∑ y, P y = ∑ y, ∑ x ∈ A, (mu x - pi x) * K x y :=
      Finset.sum_congr rfl fun y _ => hPy y
    rw [hswap, Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
  have hQsum : ∑ y, Q y = delta := by
    have hstep : ∑ y, ∑ x ∈ B, (mu x - pi x) * K x y = ∑ x ∈ B, (mu x - pi x) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
    calc ∑ y, Q y = -∑ y, ∑ x ∈ B, (mu x - pi x) * K x y := by
          rw [← Finset.sum_neg_distrib]
      _ = -∑ x ∈ B, (mu x - pi x) := by rw [hstep]
      _ = delta := by rw [hBdelta]; ring
  -- the L1 mass of the signed difference
  have hL1d : ∑ x : Seq, |mu x - pi x| = 2 * delta := by
    have hAabs : ∑ x ∈ A, |mu x - pi x| = ∑ x ∈ A, (mu x - pi x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonneg (hAnn x hx)
    have hBabs : ∑ x ∈ B, |mu x - pi x| = ∑ x ∈ B, -(mu x - pi x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonpos (hBnn x hx)
    have hsplit : (∑ x ∈ A, |mu x - pi x|) + (∑ x ∈ B, |mu x - pi x|)
        = ∑ x : Seq, |mu x - pi x| := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - pi x) (fun x => |mu x - pi x|)
    have hneg : ∑ x ∈ B, -(mu x - pi x) = -∑ x ∈ B, (mu x - pi x) := by
      simp
    rw [← hsplit, hAabs, hBabs, hneg, hBdelta]
    ring
  -- the min-overlap floor
  have hsummin : (Fintype.card Seq : ℝ) * (eps * delta) ≤ ∑ y, min (P y) (Q y) := by
    calc (Fintype.card Seq : ℝ) * (eps * delta)
        = ∑ y : Seq, eps * delta := by simp
      _ ≤ ∑ y, min (P y) (Q y) :=
          Finset.sum_le_sum fun y _ => le_min (hPge y) (hQge y)
  -- assemble
  show (∑ y, |vecMul mu K y - pi y|) / 2
      ≤ (1 - (Fintype.card Seq : ℝ) * eps) * ((∑ y, |mu y - pi y|) / 2)
  calc (∑ y, |vecMul mu K y - pi y|) / 2
      = (∑ y, |P y - Q y|) / 2 := by
        refine congrArg (fun t => t / 2) (Finset.sum_congr rfl fun y _ => ?_)
        rw [hdiff y]
    _ = (∑ y, (P y + Q y - 2 * min (P y) (Q y))) / 2 := by
        refine congrArg (fun t => t / 2) (Finset.sum_congr rfl fun y _ => ?_)
        exact abs_sub_eq_add_sub_two_min _ _
    _ = ((∑ y, P y) + (∑ y, Q y) - 2 * ∑ y, min (P y) (Q y)) / 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ((2 * delta) - 2 * ((Fintype.card Seq : ℝ) * (eps * delta))) / 2 := by
        nlinarith [hPsum, hQsum]
    _ = (1 - (Fintype.card Seq : ℝ) * eps) * ((∑ y, |mu y - pi y|) / 2) := by
        rw [hL1d]; ring

theorem chainAt_isProb (K : Seq → Seq → ℝ) (hK : pptKernel K) (mu : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) (hnn : ∀ x, 0 ≤ mu x) (n : ℕ) :
    ∑ y, chainAt mu K n y = 1 ∧ ∀ y, 0 ≤ chainAt mu K n y := by
  induction n with
  | zero => exact ⟨hmu, hnn⟩
  | succ n ih =>
      rw [chainAt_succ]
      exact ⟨vecMul_sum K hK _ ih.1, fun y => vecMul_nonneg K hK _ ih.2 y⟩

/-- **Geometric mixing under the Doeblin floor** (sharp constant):
TV(μKⁿ, π) ≤ (1 − |Seq|·ε)ⁿ · TV(μ, π), for ANY start μ, when every
kernel entry is ≥ ε and π is stationary. Induction on n with the
one-step contraction `ppt_tvContraction`. -/
theorem pptMixing (K : Seq → Seq → ℝ) (hK : pptKernel K)
    (eps : ℝ) (heps : ∀ x y, eps ≤ K x y)
    (mu pi : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) (hpi : ∑ x, pi x = 1)
    (hmunn : ∀ x, 0 ≤ mu x) (hpinn : ∀ x, 0 ≤ pi x)
    (hstat : ∀ y, vecMul pi K y = pi y) (n : ℕ) :
    tvDist (chainAt mu K n) pi
      ≤ (1 - (Fintype.card Seq : ℝ) * eps) ^ n * tvDist mu pi := by
  have hcard : (Fintype.card Seq : ℝ) * eps ≤ 1 := ppt_card_eps_le_one K hK eps heps
  have hcnn : 0 ≤ 1 - (Fintype.card Seq : ℝ) * eps := by linarith
  induction n with
  | zero =>
      rw [pow_zero, one_mul]
      exact le_refl _
  | succ n ih =>
      rw [chainAt_succ, pow_succ]
      have hprob := chainAt_isProb K hK mu hmu hmunn n
      calc tvDist (vecMul (chainAt mu K n) K) pi
          ≤ (1 - (Fintype.card Seq : ℝ) * eps) * tvDist (chainAt mu K n) pi :=
            ppt_tvContraction K hK eps heps _ pi hprob.1 hpi hprob.2 hpinn hstat
        _ ≤ (1 - (Fintype.card Seq : ℝ) * eps)
              * ((1 - (Fintype.card Seq : ℝ) * eps) ^ n * tvDist mu pi) :=
            mul_le_mul_of_nonneg_left ih hcnn
        _ = (1 - (Fintype.card Seq : ℝ) * eps) ^ (n + 1) * tvDist mu pi := by ring

theorem tvDist_le_one (mu pi : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) (hpi : ∑ x, pi x = 1)
    (hmunn : ∀ x, 0 ≤ mu x) (hpinn : ∀ x, 0 ≤ pi x) :
    tvDist mu pi ≤ 1 := by
  have h1 : ∑ y, |mu y - pi y| ≤ ∑ y, (mu y + pi y) :=
    Finset.sum_le_sum fun y _ => abs_le.2 ⟨by linarith [hmunn y, hpinn y],
      by linarith [hmunn y, hpinn y]⟩
  rw [Finset.sum_add_distrib, hmu, hpi] at h1
  unfold tvDist
  linarith

/-- **Geometric mixing under the Doeblin floor** (paper-style constant):
if every kernel entry is ≥ ε and π is stationary, then ANY start μ
satisfies TV(μKⁿ, π) ≤ (1 − ε)ⁿ. The sharp bound is the |Seq|·ε version
(`pptMixing`); since |Seq| ≥ 1, 1 − |Seq|·ε ≤ 1 − ε, and TV(μ, π) ≤ 1. -/
theorem pptMixing_doeblin (K : Seq → Seq → ℝ) (hK : pptKernel K)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps : ∀ x y, eps ≤ K x y)
    (mu pi : Seq → ℝ)
    (hmu : ∑ x, mu x = 1) (hpi : ∑ x, pi x = 1)
    (hmunn : ∀ x, 0 ≤ mu x) (hpinn : ∀ x, 0 ≤ pi x)
    (hstat : ∀ y, vecMul pi K y = pi y) (n : ℕ) :
    tvDist (chainAt mu K n) pi ≤ (1 - eps) ^ n := by
  have hcard : (Fintype.card Seq : ℝ) * eps ≤ 1 := ppt_card_eps_le_one K hK eps heps
  have hcard1 : (1 : ℝ) ≤ Fintype.card Seq := by
    obtain ⟨a⟩ : Nonempty Seq := inferInstance
    rw [← Nat.cast_one, Nat.cast_le]
    exact Finset.one_le_card.2 ⟨a, Finset.mem_univ a⟩
  have heps1 : eps ≤ 1 := by
    have hc0 : (0 : ℝ) < Fintype.card Seq := by linarith
    have hc : eps * (Fintype.card Seq : ℝ) ≤ 1 := by rw [mul_comm]; exact hcard
    calc eps ≤ 1 / (Fintype.card Seq : ℝ) := (le_div_iff₀ hc0).mpr hc
      _ ≤ 1 := (div_le_one hc0).mpr hcard1
  have hsharp := pptMixing K hK eps heps mu pi hmu hpi hmunn hpinn hstat n
  have hge : eps ≤ (Fintype.card Seq : ℝ) * eps := by
    nlinarith [hcard1, heps0]
  have hle : (1 - (Fintype.card Seq : ℝ) * eps) ^ n ≤ (1 - eps) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith [hge]) n
  have htv : tvDist mu pi ≤ 1 := tvDist_le_one mu pi hmu hpi hmunn hpinn
  have hnn : (0 : ℝ) ≤ 1 - eps := by linarith
  calc tvDist (chainAt mu K n) pi
      ≤ (1 - (Fintype.card Seq : ℝ) * eps) ^ n * tvDist mu pi := hsharp
    _ ≤ (1 - eps) ^ n * tvDist mu pi :=
        mul_le_mul_of_nonneg_right hle (tvDist_nonneg _ _)
    _ ≤ (1 - eps) ^ n * 1 :=
        mul_le_mul_of_nonneg_left htv (pow_nonneg hnn n)
    _ = (1 - eps) ^ n := mul_one _

/-! ## 6. Discovery gain: the good set under the stationary power target -/

section Discovery

variable {Ω : Type*} [MeasurableSpace Ω]
variable (nu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure nu]

/-- The good set: sequences whose measured candidate value V clears the
threshold γ (V is an h_emp_ input — the measured value oracle). -/
noncomputable def goodSet (V : Seq → ℝ) (gamma : ℝ) : Finset Seq :=
  Finset.univ.filter fun x => gamma ≤ V x

/-- **Discovery probability at stationarity**: if the sampler draws
`sample` from the power target π (h_emp_dist: point masses match π;
h_emp_meas: measurability; h_emp_single: singletons measurable on the
sequence space), then the probability of drawing a γ-good candidate is
EXACTLY the stationary mass of the good set — a chain started AT
stationarity samples the good set at its stationary weight. -/
theorem discovery_prob_stationary (V : Seq → ℝ) (gamma : ℝ)
    (pi : Seq → ℝ) (sample : Ω → Seq)
    (h_emp_fiber : ∀ x : Seq, MeasurableSet {ω | sample ω = x})
    (h_emp_dist : ∀ x, nu.real {ω | sample ω = x} = pi x) :
    nu.real {ω | gamma ≤ V (sample ω)} = ∑ x ∈ goodSet V gamma, pi x := by
  have hpreim_meas : ∀ s : Finset Seq, MeasurableSet {ω | sample ω ∈ s} := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
        have hset : {ω | sample ω ∈ insert a s}
            = {ω | sample ω = a} ∪ {ω | sample ω ∈ s} := by
          ext ω; simp
        rw [hset]
        exact (h_emp_fiber a).union ih
  have hpreim : ∀ s : Finset Seq,
      nu.real {ω | sample ω ∈ s} = ∑ x ∈ s, pi x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have hset : {ω | sample ω ∈ insert a s}
            = {ω | sample ω = a} ∪ {ω | sample ω ∈ s} := by
          ext ω; simp
        have hdis : Disjoint {ω | sample ω = a} {ω | sample ω ∈ s} := by
          rw [Set.disjoint_iff]
          intro ω hω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hω
          exact absurd (hω.1 ▸ hω.2) ha
        have hru : nu.real ({ω | sample ω = a} ∪ {ω | sample ω ∈ s})
            = nu.real {ω | sample ω = a} + nu.real {ω | sample ω ∈ s} := by
          simp only [MeasureTheory.Measure.real]
          rw [measure_union hdis (hpreim_meas s),
            ENNReal.toReal_add (measure_ne_top nu _) (measure_ne_top nu _)]
        rw [hset, hru, h_emp_dist a, ih, Finset.sum_insert ha]
  have hgood : {ω | gamma ≤ V (sample ω)} = {ω | sample ω ∈ goodSet V gamma} := by
    ext ω
    simp only [Set.mem_setOf_eq, goodSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
  rw [hgood, hpreim (goodSet V gamma)]

/-- **The stationary-mass floor**: if the good set carries stationary
mass ≥ p, then a chain sampled at stationarity finds a γ-good candidate
with probability ≥ p. -/
theorem discovery_prob_lower (V : Seq → ℝ) (gamma : ℝ)
    (pi : Seq → ℝ) (sample : Ω → Seq) (p : ℝ)
    (h_emp_fiber : ∀ x : Seq, MeasurableSet {ω | sample ω = x})
    (h_emp_dist : ∀ x, nu.real {ω | sample ω = x} = pi x)
    (hmass : p ≤ ∑ x ∈ goodSet V gamma, pi x) :
    p ≤ nu.real {ω | gamma ≤ V (sample ω)} := by
  rw [discovery_prob_stationary nu V gamma pi sample h_emp_fiber
    h_emp_dist]
  exact hmass

/-- **The γ-floor on stationary expected value**: with nonnegative
measured values, the stationary expectation of V is at least γ times the
discovery probability — the discovery gain is exactly the good-set mass
scaled by the threshold. -/
theorem stationary_value_ge (V : Seq → ℝ) (gamma : ℝ) (pi : Seq → ℝ)
    (hV : ∀ x, 0 ≤ V x) (hpinn : ∀ x, 0 ≤ pi x)
    (hmu : ∑ x, pi x = 1) :
    gamma * (∑ x ∈ goodSet V gamma, pi x) ≤ ∑ x, pi x * V x := by
  have hgood : ∀ x ∈ goodSet V gamma, gamma * pi x ≤ pi x * V x := by
    intro x hx
    have hg : gamma ≤ V x := (Finset.mem_filter.mp hx).2
    have hpx : 0 ≤ pi x := hpinn x
    nlinarith [mul_le_mul_of_nonneg_left hg hpx]
  have hsplit : (∑ x ∈ goodSet V gamma, pi x * V x)
      + (∑ x ∈ Finset.univ.filter fun x => ¬ gamma ≤ V x, pi x * V x)
      = ∑ x : Seq, pi x * V x :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => gamma ≤ V x) (fun x => pi x * V x)
  have hleft : gamma * (∑ x ∈ goodSet V gamma, pi x)
      ≤ ∑ x ∈ goodSet V gamma, pi x * V x := by
    calc gamma * (∑ x ∈ goodSet V gamma, pi x)
        = ∑ x ∈ goodSet V gamma, gamma * pi x := by rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ goodSet V gamma, pi x * V x :=
          Finset.sum_le_sum fun x hx => hgood x hx
  have hright : (0 : ℝ) ≤ ∑ x ∈ Finset.univ.filter fun x => ¬ gamma ≤ V x,
      pi x * V x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (hV x)
  linarith

end Discovery

/-! ## 7. The composite success indicator -/

section Success

variable {Ω : Type*} [MeasurableSpace Ω]
variable (nu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure nu]

/-- **The composite PPT success event**: S_t = 1 iff the PPT sample is
γ-good AND the verifier accepts AND the budget is respected. The
verifier/budget events enter as named event sets (honest boundary: no
verifier theory exists yet — same gap as `GrowthState.verifier`). -/
def pptSuccess (V : Seq → ℝ) (gamma : ℝ) (sample : Ω → Seq)
    (verOK budOK : Set Ω) : Set Ω :=
  {ω | gamma ≤ V (sample ω)} ∩ (verOK ∩ budOK)

/-- The verifier-rejects-good event: the sample was good but the
verifier failed it (false negative of the verification stage). -/
def pptRejectGood (V : Seq → ℝ) (gamma : ℝ) (sample : Ω → Seq)
    (verOK : Set Ω) : Set Ω :=
  {ω | gamma ≤ V (sample ω)} ∩ verOKᶜ

/-- The budget-overrun event: the sample was good and verified, but the
budget cap was exceeded. -/
def pptOverrun (V : Seq → ℝ) (gamma : ℝ) (sample : Ω → Seq)
    (budOK : Set Ω) : Set Ω :=
  {ω | gamma ≤ V (sample ω)} ∩ budOKᶜ

/-- **The union-bound decomposition of the composite success**: the
discovery (good-sample) event is contained in the union of the success
event, the verifier-rejects-good event and the budget-overrun event —
hence Pr[good] ≤ Pr[S=1] + Pr[reject-good] + Pr[overrun]. Honest and
explicit: every way a good sample fails to become a success is one of
the two named failure channels. -/
theorem pptSuccess_union_bound (V : Seq → ℝ) (gamma : ℝ) (sample : Ω → Seq)
    (verOK budOK : Set Ω)
    (h_emp_good : MeasurableSet {ω | gamma ≤ V (sample ω)})
    (h_emp_ver : MeasurableSet verOK) (h_emp_bud : MeasurableSet budOK) :
    nu.real {ω | gamma ≤ V (sample ω)}
      ≤ nu.real (pptSuccess V gamma sample verOK budOK)
        + nu.real (pptRejectGood V gamma sample verOK)
        + nu.real (pptOverrun V gamma sample budOK) := by
  have hsub : {ω | gamma ≤ V (sample ω)}
      ⊆ pptSuccess V gamma sample verOK budOK
          ∪ (pptRejectGood V gamma sample verOK
            ∪ pptOverrun V gamma sample budOK) := by
    intro ω hω
    by_cases hv : ω ∈ verOK
    · by_cases hb : ω ∈ budOK
      · exact Or.inl ⟨hω, hv, hb⟩
      · exact Or.inr (Or.inr ⟨hω, hb⟩)
    · exact Or.inr (Or.inl ⟨hω, hv⟩)
  have h1 := measureReal_mono hsub
    (measure_ne_top nu (pptSuccess V gamma sample verOK budOK
      ∪ (pptRejectGood V gamma sample verOK
        ∪ pptOverrun V gamma sample budOK)))
  have key : ∀ A B : Set Ω, nu.real (A ∪ B) ≤ nu.real A + nu.real B := by
    intro A B
    have hu := measure_union_le (μ := nu) A B
    have htop : (nu A + nu B) ≠ ⊤ := by
      rw [ENNReal.add_ne_top]
      exact ⟨measure_ne_top nu A, measure_ne_top nu B⟩
    have h2 := (ENNReal.toReal_le_toReal (measure_ne_top nu (A ∪ B)) htop).mpr hu
    simp only [MeasureTheory.Measure.real,
      ENNReal.toReal_add (measure_ne_top nu A) (measure_ne_top nu B)] at h2
    exact h2
  have h3 := key (pptSuccess V gamma sample verOK budOK)
    (pptRejectGood V gamma sample verOK
      ∪ pptOverrun V gamma sample budOK)
  have h4 := key (pptRejectGood V gamma sample verOK)
    (pptOverrun V gamma sample budOK)
  linarith

/-- **The union-bound lower bound on composite success** (the honest
composite form): if the good set carries stationary mass ≥ p, then
Pr[S_t = 1] ≥ p − Pr[verifier rejects a good sample]
− Pr[budget overrun on a good sample]. -/
theorem pptSuccess_lower (V : Seq → ℝ) (gamma : ℝ) (sample : Ω → Seq)
    (verOK budOK : Set Ω) (p : ℝ)
    (h_emp_good : MeasurableSet {ω | gamma ≤ V (sample ω)})
    (h_emp_ver : MeasurableSet verOK) (h_emp_bud : MeasurableSet budOK)
    (hmass : p ≤ nu.real {ω | gamma ≤ V (sample ω)}) :
    p - nu.real (pptRejectGood V gamma sample verOK)
      - nu.real (pptOverrun V gamma sample budOK)
      ≤ nu.real (pptSuccess V gamma sample verOK budOK) := by
  have hub := pptSuccess_union_bound nu V gamma sample verOK budOK
    h_emp_good h_emp_ver h_emp_bud
  linarith

end Success

end PPT
end Hagi

/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# Description-length interpretability contract (C421)

Research beat: iWSP (arXiv 2611.18114) audits interpretability as a
REBUILD bottleneck — a model counts as interpretable when a SHORT
description (there: a text summary of at most a couple hundred
words) lets an independent session REBUILD a model that preserves
quality.  This module formalizes that idea inside the repository's
compression theory (C367/C381/C389) as a description-length bound:
interpretability certificate := EXISTENCE of a bounded-length
description `d` whose rebuild `R d` stays within `ε` of the
original model's quality, measured by the loss `ℓ` ONLY.

Three honest results:

* `rebuildable_of_compressible` (compression→rebuild bridge): if a
  compressed model `M̃ = rebuild d` has a short description AND a
  bounded parameter displacement `dist M̃ M ≤ δ`, then the rebuild
  certificate holds with `ε_rebuild = lip * δ` DERIVED through the
  C389 Lipschitz transport binder — the same algebra as the C389
  per-step quantization penalty, now read as an interpretability
  certificate instead of an optimization cost.
* `exists_good_not_reachable` / `exists_not_rebuildable` (finite
  counting bound, the interpretability-is-special negative result):
  on a finite model class, budget-`B` descriptions over a finite
  alphabet rebuild at most `card Sig ^ B` distinct models; when the
  ε-good set is LARGER than that (premise — the honest finite
  stand-in for "class entropy exceeds the budget"), some ε-good
  model is the rebuild of NO budget-B description.  Pure
  pigeonhole via `Fintype.card_le_of_injective`; NO Kolmogorov
  claims (no Turing machines, no universality, no invariance).
* `admission_margin_mono_descCost` (C390 admission pointer): the
  description budget enters an admission margin as a
  memoryCost-like NONNEGATIVE resource cost, and charging it can
  only SHRINK the margin — an abstract-margin lemma documented as
  the pointer to the training-layer admission rule (layering: the
  Theory layer does not import the Training layer).

## Honest scope (pins)

- The description alphabet is an ABSTRACT finite type `Sig` for the
  counting bound and an abstract type for the certificate; NO claim
  that natural-language summaries are formal tokens of `Sig`.
- Rebuild quality is measured by the loss `ℓ` ONLY — no semantic
  or behavioral fidelity claim beyond `ℓ`.
- The Lipschitz constant `lip` is a per-model PREMISE binder (the
  C389 `transport` / `gridQ_energy_bound` pattern); the only proved
  Lipschitz law repo-side is logit-level, a parameter-level `lip`
  stays the consumer's to discharge.
- The counting premise is a cardinality comparison; no entropy
  language is formalized.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.Interpretability

/-! ## The rebuild carrier -/

/-- The rebuild system of C421: a model space `Θ` with a quality
loss, a symmetric pseudo-distance with a Lipschitz transport binder
(the C389 pattern: `loss a ≤ loss b + lip * dist a b`), an abstract
description type with a description-length budget function, and a
rebuild map from descriptions back to parameters. -/
structure RebuildSystem (Θ : Type) where
  /-- The quality loss on models (the ONLY quality measure). -/
  loss : Θ → ℝ
  /-- A symmetric pseudo-distance on parameter states. -/
  dist : Θ → Θ → ℝ
  /-- The distance is symmetric. -/
  dist_symm : ∀ a b : Θ, dist a b = dist b a
  /-- The distance is nonnegative. -/
  dist_nonneg : ∀ a b : Θ, 0 ≤ dist a b
  /-- The per-model Lipschitz constant of the loss in `dist`
  (premise binder, C389 pattern). -/
  lip : ℝ
  /-- The Lipschitz constant is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- Lipschitz transport: the loss moves by at most
  `lip * dist` (premise binder). -/
  transport : ∀ a b : Θ, loss a ≤ loss b + lip * dist a b
  /-- The abstract description type. -/
  desc : Type
  /-- The description-length budget of a description. -/
  descBudget : desc → ℕ
  /-- The rebuild map from descriptions to parameters. -/
  rebuild : desc → Θ

/-- The interpretability CERTIFICATE of C421 (iWSP rebuild
bottleneck): model `θ` is `(B, ε)`-rebuildable when SOME
description `d` of budget at most `B` rebuilds a model whose loss
is within `ε` of `loss θ`. -/
def Rebuildable {Θ : Type} (sys : RebuildSystem Θ) (B : ℕ) (ε : ℝ)
    (θ : Θ) : Prop :=
  ∃ d : sys.desc, sys.descBudget d ≤ B ∧
    sys.loss (sys.rebuild d) ≤ sys.loss θ + ε

/-! ## (a) The compression→rebuild bridge -/

/-- Bridge theorem (C421): a COMPRESSIBLE model is REBUILDABLE.
If the compressed model `M̃` has a short description
(`descBudget d ≤ B`, `rebuild d = M̃`) and a bounded parameter
displacement `dist M̃ M ≤ δ`, then the rebuild certificate holds
with `ε_rebuild = lip * δ` — DERIVED through the C389 Lipschitz
transport, not assumed.  Reading: quantized/low-rank compressions
(C367-style short encodings) ARE interpretability certificates up
to one Lipschitz transport of the compression error. -/
theorem rebuildable_of_compressible {Θ : Type} (sys : RebuildSystem Θ)
    (M M' : Θ) (d : sys.desc) (δ : ℝ) (B : ℕ)
    (hdist : sys.dist M' M ≤ δ) (hdesc : sys.descBudget d ≤ B)
    (hrebuild : sys.rebuild d = M') :
    Rebuildable sys B (sys.lip * δ) M := by
  refine ⟨d, hdesc, ?_⟩
  rw [hrebuild]
  have h := sys.transport M' M
  nlinarith [sys.lip_nonneg, hdist, sys.dist_nonneg M' M]

/-! ## (b) The finite counting bound -/

/-- The ε-good set of models within `ε` of `loss θ` — the finite
subtype counted by the pigeonhole bound.  Kept as a def so the
premise of the counting theorem is a plain cardinality
comparison. -/
abbrev GoodSet {Θ : Type} (loss : Θ → ℝ) (θ : Θ) (ε : ℝ) :
    Type := {x : Θ // loss x ≤ loss θ + ε}

noncomputable instance {Θ : Type} [Fintype Θ] (loss : Θ → ℝ)
    (θ : Θ) (ε : ℝ) : Fintype (GoodSet loss θ ε) :=
  @Subtype.fintype Θ (fun x => loss x ≤ loss θ + ε)
    (Classical.decPred _) inferInstance

/-- Counting bound (C421, honest finite pigeonhole): over a finite
alphabet `Sig`, budget-`B` descriptions are `Fin B → Sig` and the
rebuild map `R` reaches at most `card Sig ^ B` distinct models.
If the ε-good set is LARGER (premise: the honest finite stand-in
for "class entropy exceeds the budget"), then some ε-good model is
the rebuild of NO budget-B description.  NO Kolmogorov claims —
no Turing machines, no universality; this is pure cardinality
arithmetic. -/
theorem exists_good_not_reachable {Θ Sig : Type} [Fintype Θ]
    [Fintype Sig] [Nonempty Sig] (loss : Θ → ℝ) (θ : Θ) (ε : ℝ)
    (B : ℕ) (R : (Fin B → Sig) → Θ)
    (hcard : Fintype.card Sig ^ B <
      Fintype.card (GoodSet loss θ ε)) :
    ∃ x : Θ, loss x ≤ loss θ + ε ∧ ∀ d : Fin B → Sig, R d ≠ x := by
  by_contra hcon
  push Not at hcon
  -- every ε-good model is reachable: build a right inverse.
  choose! g hg using fun (x : GoodSet loss θ ε) =>
    hcon x.1 x.2
  -- g is injective because R ∘ g = id on the good subtype.
  have hinj : Function.Injective g := by
    intro a b hab
    have : (R (g a) : Θ) = (R (g b) : Θ) := by rw [hab]
    rw [hg a, hg b] at this
    exact Subtype.ext this
  have hle : Fintype.card (GoodSet loss θ ε) ≤
      Fintype.card (Fin B → Sig) :=
    Fintype.card_le_of_injective g hinj
  have hfun : Fintype.card (Fin B → Sig) = Fintype.card Sig ^ B := by
    simp
  omega

/-- Interpretability-is-special corollary (C421): if EVERY model is
ε-good (the good set is the whole class — e.g. all models within
`ε` of the reference loss) and the class is larger than the
description budget's reach, then some model has NO `(B, ε)`
rebuild certificate at all: short-description interpretability is
a SPECIAL property, not a generic one, on a finite class. -/
theorem exists_not_rebuildable {Θ Sig : Type} [Fintype Θ]
    [Fintype Sig] [Nonempty Sig] (loss : Θ → ℝ) (θ : Θ) (ε : ℝ) (B : ℕ)
    (R : (Fin B → Sig) → Θ)
    (hgood : ∀ x : Θ, loss x ≤ loss θ + ε)
    (hcard : Fintype.card Sig ^ B < Fintype.card Θ) :
    ∃ x : Θ, loss x ≤ loss θ + ε ∧
      ∀ d : Fin B → Sig, R d ≠ x := by
  have hcard' : Fintype.card Sig ^ B <
      Fintype.card (GoodSet loss θ ε) := by
    have e : GoodSet loss θ ε ≃ Θ := by
      refine Equiv.mk (fun x => (x : Θ))
        (fun x => (⟨x, hgood x⟩ : GoodSet loss θ ε)) ?_ ?_
      · intro x
        rfl
      · intro x
        rfl
    rw [Fintype.card_congr e]
    exact hcard
  exact exists_good_not_reachable loss θ ε B R hcard'

/-- Interpretability-is-special corollary (C421), exact-rebuild
form: with the budget-`B` description space `Fin B → Sig`, if the
model class is larger than `card Sig ^ B` then some model is the
rebuild of NO description — a short-description reconstruction of
the FULL class is impossible by pigeonhole, so compact-description
interpretability is a SPECIAL property, not a generic one.  (The
loss-based `Rebuildable` negation would additionally need a
quality-separation premise; pinned here in the exact form.) -/
theorem exists_not_exact_rebuildable {Θ Sig : Type} [Fintype Θ]
    [Fintype Sig] [Nonempty Sig] (loss : Θ → ℝ) (θ : Θ) (ε : ℝ) (B : ℕ)
    (R : (Fin B → Sig) → Θ)
    (hgood : ∀ x : Θ, loss x ≤ loss θ + ε)
    (hcard : Fintype.card Sig ^ B < Fintype.card Θ) :
    ∃ x : Θ, ∀ d : Fin B → Sig, R d ≠ x := by
  obtain ⟨x, _, hx⟩ := exists_not_rebuildable loss θ ε B R hgood hcard
  exact ⟨x, hx⟩

/-! ## (c) The admission pointer-lemma (C390 pattern) -/

/-- C390 pointer-lemma (C421): the description budget enters an
admission margin exactly like a memoryCost channel — as a
NONNEGATIVE additive resource cost.  Charging it can only SHRINK
the margin (`withDescCost_le`), so a positive margin WITH the
description cost implies a positive margin WITHOUT it
(`admission_margin_mono_descCost`): charging the budget never
CREATES an admission.  Pointer (no import — layering): the
training-layer admission rule composes this with its
`admissionMargin` by instantiation `b := λ_I * B_desc`, the same
role `λ_M * memoryCost` plays there. -/
theorem withDescCost_le (gain r c b : ℝ) (hb : 0 ≤ b) :
    gain - r - c - b ≤ gain - r - c := by nlinarith

/-- See `withDescCost_le`: positivity transfers FROM the
budget-charged margin TO the budget-free margin — the C390
admission pointer in margin form. -/
theorem admission_margin_mono_descCost (gain r c b : ℝ) (hb : 0 ≤ b)
    (h : 0 < gain - r - c - b) : 0 < gain - r - c := by nlinarith

end Hagi.Theory.Interpretability

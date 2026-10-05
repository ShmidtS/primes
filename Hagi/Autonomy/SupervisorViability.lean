/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# SupervisorViability: when can a monitor class police itself (R153)

The last open core round of FORMALIZATION_PLAN.md (§6 item 3):
the supervisor of the F3 loop must catch its own mistakes, and
the source theorem (arXiv:2609.36049) says co-trained monitors
achieve vanishing monitoring error iff the monitor class has
finite Littlestone dimension — while majority-vote
self-training does NOT invert wrong verdicts, making an
external verdict anchor (the Red-Queen scheme of
arXiv:2606.26294) mandatory.

**What is proved here (finite core, pure math, no `h_emp_`).**

* `LittlestoneDim` — the Littlestone dimension of a finite
  hypothesis class, defined by shattering of binary instance
  trees. DEFINITION ONLY in this round: the mistake–dimension
  equivalence of 2609.36049 is future work and claimed
  nowhere.

* `halving_mistake_halves` — THE HALVING LEMMA: if the
  majority-vote (halving) monitor over the version space is
  wrong on a labeled example, the surviving version space at
  least halves: `2·|VS'| ≤ |VS|`.

* `halving_mistake_bound` — VIABILITY, finite ⟸ direction of
  2609.36049: for ANY realizable labeled sequence, the number
  `M` of halving-monitor mistakes satisfies `2 ^ M ≤ |H|` —
  a finite, horizon-independent mistake budget. A finite
  monitor class can police itself to vanishing error on
  realizable data.

* `majority_wrong_verdict` — vote counting: a strict wrong
  majority forces a wrong majority verdict.

* `majority_wrong_persists` — the impossibility kernel of
  "majority-vote self-training does not invert wrong
  verdicts": a self-training round that rebuilds the class by
  an injection preserving every member's verdict on `x`
  transports a strict wrong majority to the new class.
  Correcting the verdict requires changing class membership
  against an EXTERNAL anchor — the Red-Queen rule is a
  necessity, not a style choice.

**Honest boundary.** Only the sufficiency direction (finite
class ⟹ bounded mistakes) is proved; the converse (vanishing
error ⟹ finite Ldim, via adversarial trees) is open. The
Red-Queen evaluator-switching policy is a runtime protocol,
not a Lean object.

Sources: arXiv:2609.36049 (co-trained monitors, Littlestone
characterisation); arXiv:2606.26294 (Red-Queen evaluator
switching); the halving algorithm is classical (Littlestone
'88).
-/

namespace Hagi.Autonomy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Binary instance trees and the Littlestone dimension

Definition only (this round): the shattering predicate and the
dimension. No property of `LittlestoneDim` is claimed. -/

/-- `H` shatters a binary instance tree `t` of depth `d` (the
instance at each internal node as a function of the binary
answers given so far) when every
root-to-leaf answer path of length `d` is realized by some
hypothesis in `H` consistent with the tree along that path. -/
def Shatters (H : Finset (X → Bool)) (d : ℕ) (t : List Bool → X) : Prop :=
  ∀ path : List Bool, ∀ hpath : path.length = d,
    ∃ h ∈ H, ∀ i : ℕ, ∀ hi : i < d,
      h (t (path.take i)) = path.get ⟨i, hpath ▸ hi⟩

/-- The Littlestone dimension of a finite class: the supremum
of shattered tree depths (`0` when no positive-depth tree is
shattered). DEFINITION ONLY in this module; the
mistake–dimension equivalence is future work. -/
noncomputable def LittlestoneDim (H : Finset (X → Bool)) : ℕ :=
  sSup {d : ℕ | ∃ t : List Bool → X, Shatters H d t}

/-! ## The version space and the halving monitor -/

/-- Consistency of a hypothesis with a labeled sequence. -/
def ConsistentWith (h : X → Bool) (L : List (X × Bool)) : Prop :=
  ∀ p ∈ L, h p.1 = p.2

/-- The version space: hypotheses of `H` consistent with the
labeled sequence `L`. -/
def versionSpace (H : Finset (X → Bool)) (L : List (X × Bool)) :
    Finset (X → Bool) :=
  H.filter (fun h => L.all (fun p => h p.1 = p.2))

/-- The halving (majority) verdict on `x`: `true` iff strictly
more than half of the version space answers `true`. -/
def halvingVerdict (H : Finset (X → Bool)) (L : List (X × Bool)) (x : X) : Bool :=
  decide (2 * ((versionSpace H L).filter (fun h => h x)).card
    > (versionSpace H L).card)

/-- The halving monitor errs on example `(x, y)` when its
verdict on `x` (from the history `L`) differs from `y`. -/
def IsMistake (H : Finset (X → Bool)) (L : List (X × Bool)) (p : X × Bool) : Prop :=
  halvingVerdict H L p.1 ≠ p.2

theorem versionSpace_mono (H : Finset (X → Bool))
    (L₁ L₂ : List (X × Bool)) (hsub : ∀ e ∈ L₁, e ∈ L₂) :
    versionSpace H L₂ ⊆ versionSpace H L₁ := by
  intro h hh
  simp only [versionSpace, Finset.mem_filter, List.all_eq_true] at hh ⊢
  refine ⟨hh.1, fun p hp => hh.2 p (hsub p hp)⟩

theorem versionSpace_append_singleton (H : Finset (X → Bool))
    (L : List (X × Bool)) (x : X) (y : Bool) :
    versionSpace H (L ++ [(x, y)])
      = (versionSpace H L).filter (fun h => h x = y) := by
  ext h
  simp only [versionSpace, Finset.mem_filter, List.all_eq_true,
    List.mem_append, List.mem_singleton, decide_eq_true_eq]
  constructor
  · rintro ⟨hH, hall⟩
    refine ⟨⟨hH, fun p hp => hall p (Or.inl hp)⟩, ?_⟩
    have hxy := hall (x, y) (Or.inr rfl)
    simpa using hxy
  · rintro ⟨⟨hH, hall⟩, hxy⟩
    refine ⟨hH, fun p hp => ?_⟩
    rcases hp with hp | rfl
    · exact hall p hp
    · simpa using hxy

/-- **The halving lemma.** A wrong halving verdict at least
halves the version space: the members that voted with the
wrong majority are eliminated by consistency, and they are at
least half of the survivors. -/
theorem halving_mistake_halves (H : Finset (X → Bool))
    (L : List (X × Bool)) (x : X) (y : Bool)
    (hm : IsMistake H L (x, y)) :
    2 * (versionSpace H (L ++ [(x, y)])).card
      ≤ (versionSpace H L).card := by
  rw [versionSpace_append_singleton]
  have hA : ((versionSpace H L).filter (fun h => h x)).card
      + ((versionSpace H L).filter (fun h => ¬h x)).card
      = (versionSpace H L).card :=
    Finset.card_filter_add_card_filter_not (s := versionSpace H L) (p := fun h => h x)
  cases y with
  | true =>
      -- the verdict came out false: the true-voters are a minority
      have hfilter : (versionSpace H L).filter (fun h => h x = true)
          = (versionSpace H L).filter (fun h => h x) := by
        ext h; simp
      have hcond : ¬ (2 * ((versionSpace H L).filter (fun h => h x)).card
          > (versionSpace H L).card) := by
        simpa [IsMistake, halvingVerdict] using hm
      rw [hfilter]
      omega
  | false =>
      -- the verdict came out true: the false-voters survive
      have hfilter : (versionSpace H L).filter (fun h => h x = false)
          = (versionSpace H L).filter (fun h => ¬h x) := by
        ext h; simp
      have hcond : 2 * ((versionSpace H L).filter (fun h => h x)).card
          > (versionSpace H L).card := by
        simpa [IsMistake, halvingVerdict] using hm
      rw [hfilter]
      omega

/-- The number of halving-monitor mistakes along a labeled
sequence, processed left to right (accumulator = seen
history). -/
def mistakesAux (H : Finset (X → Bool)) :
    List (X × Bool) → List (X × Bool) → ℕ
  | _, [] => 0
  | acc, p :: rest =>
      (if halvingVerdict H acc p.1 != p.2 then 1 else 0)
        + mistakesAux H (acc ++ [p]) rest

/-- Total halving-monitor mistakes on a fresh sequence. -/
def mistakeCount (H : Finset (X → Bool)) (L : List (X × Bool)) : ℕ :=
  mistakesAux H [] L

theorem mistakesAux_bound (H : Finset (X → Bool)) :
    ∀ (rest acc : List (X × Bool)),
      2 ^ mistakesAux H acc rest * (versionSpace H (acc ++ rest)).card
        ≤ (versionSpace H acc).card := by
  intro rest
  induction rest with
  | nil => intro acc; simp [mistakesAux]
  | cons p rest' ih =>
      intro acc
      simp only [mistakesAux]
      by_cases hmist : halvingVerdict H acc p.1 != p.2
      · -- mistake at p: the version space at least halves
        have hm : IsMistake H acc (p.1, p.2) := by
          simpa [IsMistake] using hmist
        have hsplit : 2 * (versionSpace H (acc ++ [p])).card
            ≤ (versionSpace H acc).card :=
          halving_mistake_halves H acc p.1 p.2 hm
        have hih := ih (acc ++ [p])
        rw [List.append_assoc, List.singleton_append] at hih
        rw [ite_eq_left hmist]
        calc 2 ^ (1 + mistakesAux H (acc ++ [p]) rest')
              * (versionSpace H (acc ++ p :: rest')).card
            = 2 * (2 ^ mistakesAux H (acc ++ [p]) rest'
                * (versionSpace H (acc ++ p :: rest')).card) := by
                rw [Nat.add_comm, Nat.pow_succ]; ring
            _ ≤ 2 * (versionSpace H (acc ++ [p])).card :=
                Nat.mul_le_mul_left _ hih
            _ ≤ (versionSpace H acc).card := hsplit
      · -- no mistake: the version space only shrinks
        rw [ite_eq_right hmist, Nat.zero_add]
        have hih := ih (acc ++ [p])
        rw [List.append_assoc, List.singleton_append] at hih
        have hmono2 : versionSpace H (acc ++ [p]) ⊆ versionSpace H acc :=
          versionSpace_mono H _ _ (fun e he => List.mem_append.mpr (Or.inl he))
        have hcard2 : (versionSpace H (acc ++ [p])).card
            ≤ (versionSpace H acc).card :=
          Finset.card_le_card hmono2
        exact Nat.le_trans hih hcard2

/-- **Viability of the halving supervisor** (finite ⟸
direction of 2609.36049). For any labeled sequence realizable
by `H`, the number `M` of halving-monitor mistakes satisfies
`2 ^ M ≤ |H|`: a finite, horizon-independent mistake budget.
The realizable witness stays in every version space, so the
monitor's residual error on realizable data vanishes after
finitely many verified mistakes. -/
theorem halving_mistake_bound (H : Finset (X → Bool))
    (L : List (X × Bool))
    (hreal : ∃ h ∈ H, ConsistentWith h L) :
    2 ^ mistakeCount H L ≤ H.card := by
  obtain ⟨hstar, hH, hcons⟩ := hreal
  have hkey := mistakesAux_bound H L []
  simp only [List.nil_append] at hkey
  have hnil : (versionSpace H []).card = H.card := by
    simp [versionSpace]
  rw [hnil] at hkey
  have hVS : hstar ∈ versionSpace H L := by
    simp only [versionSpace, Finset.mem_filter, List.all_eq_true,
      decide_eq_true_eq]
    exact ⟨hH, hcons⟩
  have hpos : 1 ≤ (versionSpace H L).card := by
    have : 0 < (versionSpace H L).card := Finset.card_pos.mpr ⟨hstar, hVS⟩
    omega
  have h1 : 2 ^ mistakeCount H L * 1 ≤ 2 ^ mistakeCount H L
      * (versionSpace H L).card := Nat.mul_le_mul_left _ hpos
  have h2 : 2 ^ mistakeCount H L
      ≤ 2 ^ mistakeCount H L * (versionSpace H L).card := by
    simpa using h1
  exact Nat.le_trans h2 hkey

/-! ## The no-self-correction lemma (the Red-Queen anchor) -/

omit [Fintype X] [DecidableEq X] in
/-- **A wrong majority votes wrong** (vote counting). If a
strict majority of `H` is wrong on `x` (true label `y`), the
majority verdict on `x` is not `y`. -/
theorem majority_wrong_verdict (H : Finset (X → Bool)) (x : X) (y : Bool)
    (hmaj : 2 * (H.filter (fun h => h x ≠ y)).card > H.card) :
    halvingVerdict H [] x ≠ y := by
  have hVS : versionSpace H [] = H := by simp [versionSpace]
  have hsplit : (H.filter (fun h => h x)).card
      + (H.filter (fun h => ¬h x)).card = H.card :=
    Finset.card_filter_add_card_filter_not (s := H) (p := fun h => h x)
  cases y with
  | true =>
      -- wrong on x means answering false: the wrong side is the ¬-side
      have hset : H.filter (fun h => h x ≠ true)
          = H.filter (fun h => ¬h x) := by
        ext h; simp
      rw [hset] at hmaj
      intro hcontra
      simp [halvingVerdict, hVS] at hcontra
      omega
  | false =>
      -- wrong on x means answering true: the wrong side is the yes-side
      have hset : H.filter (fun h => h x ≠ false)
          = H.filter (fun h => h x) := by
        ext h; simp
      rw [hset] at hmaj
      intro hcontra
      simp [halvingVerdict, hVS] at hcontra
      omega

omit [Fintype X] [DecidableEq X] in
/-- **Majority-vote self-training does not invert wrong
verdicts** (2609.36049, finite transport form). Suppose the
self-training round rebuilds the class by a map `φ` that
(a) carries `H` into the new class `H'`, (b) is injective on
`H`, and (c) preserves every member's verdict on `x`. Then a
strict wrong majority of `H` on `x` transports to a strict
wrong majority of `H'` on `x`: the wrong majority verdict
persists. Flipping the verdict requires changing class
membership against an EXTERNAL anchor (the Red-Queen ground
truth), not more voting. -/
theorem majority_wrong_persists (H H' : Finset (X → Bool)) (x : X) (y : Bool)
    (φ : (X → Bool) → (X → Bool))
    (hmap : ∀ h ∈ H, φ h ∈ H')
    (hinj : ∀ a ∈ H, ∀ b ∈ H, φ a = φ b → a = b)
    (hfix : ∀ h ∈ H, (φ h) x = h x)
    (hcard : H'.card ≤ H.card)
    (hmaj : 2 * (H.filter (fun h => h x ≠ y)).card > H.card) :
    2 * (H'.filter (fun h => h x ≠ y)).card > H'.card := by
  have h1 : (H.filter (fun h => h x ≠ y)).card
      ≤ (H'.filter (fun h => h x ≠ y)).card := by
    apply Finset.card_le_card_of_injOn φ
    · intro h hh
      have ⟨h1, h2⟩ := Finset.mem_filter.mp hh
      refine Finset.mem_filter.mpr ⟨hmap h h1, ?_⟩
      rw [hfix h h1]
      exact h2
    · intro a ha b hb hab
      have ⟨ha1, _⟩ := Finset.mem_filter.mp ha
      have ⟨hb1, _⟩ := Finset.mem_filter.mp hb
      exact hinj a ha1 b hb1 hab
  omega

end Hagi.Autonomy

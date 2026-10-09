/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Supervisor viability: halving monitors and majority persistence

Definitions: `LittlestoneDim` (shattered binary instance
trees; definition only, no property claimed), the version
space, the halving verdict, and the mistake count.

Results:
* `halving_mistake_halves` — a wrong halving verdict at least
  halves the version space.
* `halving_mistake_bound` — for any sequence realizable by
  `H`, `2 ^ mistakeCount H L <= H.card`.
* `majority_wrong_verdict` — a strict wrong majority forces a
  wrong majority verdict.
* `majority_wrong_persists` — an injective class rebuild that
  preserves verdicts on `x` transports a strict wrong
  majority to the new class.

Only the finite-⟸ direction is proved; the converse
(vanishing error ⟹ finite Littlestone dimension) is open.
(Sources: arXiv:2609.36049, arXiv:2606.26294.)
-/

namespace Hagi.Autonomy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Binary instance trees and the Littlestone dimension -/

/-- `H` shatters a binary instance tree `t` of depth `d` (the
instance at each internal node as a function of the binary
answers given so far) when every
root-to-leaf answer path of length `d` is realized by some
hypothesis in `H` consistent with the tree along that path. -/
def Shatters (H : Finset (X → Bool)) (d : ℕ) (t : List Bool → X) : Prop :=
  ∀ path : List Bool, ∀ hpath : path.length = d,
    ∃ h ∈ H, ∀ i : ℕ, ∀ hi : i < d,
      h (t (path.take i)) = path.get ⟨i, hpath ▸ hi⟩

/-- The supremum of shattered tree depths (`0` when no
positive-depth tree is shattered). Definition only. -/
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

/-- A wrong halving verdict on `(x, y)` at least halves the
version space: `2 * |VS (L ++ [(x, y)])| <= |VS L|`. -/
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

/-- For any labeled sequence `L` realizable by `H` (some
`h ∈ H` is consistent with `L`), the halving-monitor mistake
count satisfies `2 ^ mistakeCount H L <= H.card`. -/
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

/-! ## Persistence of wrong majorities -/

omit [Fintype X] [DecidableEq X] in
/-- If a strict majority of `H` answers differently from `y`
on `x`, the majority verdict on `x` is not `y`. -/
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
/-- If `φ` maps `H` injectively into `H'` preserving every
member's verdict on `x`, `|H'| <= |H|`, and a strict majority
of `H` answers differently from `y` on `x`, then a strict
majority of `H'` also answers differently from `y` on `x`. -/
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

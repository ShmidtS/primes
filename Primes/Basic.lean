import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

/-! ## List utilities (genuinely missing from Mathlib) -/

theorem List.getLastD_mem_of_ne_nil {α : Type} [Inhabited α] (xs : List α) (hxs : xs ≠ []) :
    xs.getLastD default ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest => simp [List.getLastD]

/-! ## Gap list utilities (used by Wheel.lean) -/

def pointGapsList (points : List Nat) : List Nat :=
  match points with
  | [] | [_] => []
  | a :: b :: rest => (b - a) :: pointGapsList (b :: rest)

theorem pointGapsList_sum_eq_last :
    ∀ points : List Nat, points.Pairwise (· <= ·) ->
      (pointGapsList points).sum + points.headD 0 = points.getLastD 0 := by
  intro points hmono
  induction points with
  | nil => simp [pointGapsList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [pointGapsList]
      | cons b tail =>
          have hab : a <= b := (List.pairwise_cons.mp hmono).1 b (by simp)
          have htail_sum := ih (List.pairwise_cons.mp hmono).2
          simp [pointGapsList] at htail_sum ⊢; omega

theorem pointGapsList_length (points : List Nat) :
    (pointGapsList points).length = points.length - 1 := by
  induction points with
  | nil => simp [pointGapsList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [pointGapsList]
      | cons b tail => simp [pointGapsList, ih]

theorem List.getLastD_is_max_of_pairwise_le {l : List Nat} (hsorted : l.Pairwise (· ≤ ·))
    (_hnonempty : l ≠ []) : ∀ x ∈ l, x ≤ l.getLastD 0 := by
  intro x hx
  have hle := hsorted.rel_getLast hx
  have hgetLastD : l.getLastD 0 = l.getLast (List.ne_nil_of_mem hx) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil (List.ne_nil_of_mem hx),
        Option.getD_some]
  rw [hgetLastD]; exact hle

end PrimeGaps

import Mathlib.Tactic
import Hagi.Learning.TernaryPert

set_option linter.style.header false

/-!
# PertTelescope — многослойный телескоп возмущений (цикл 12)

Завершает сквозную оценку ошибки квантованной сети из аудита #1:
если каждый слой lᵢ заменить на возмущённый lᵢ' (например,
тернарно квантованный: ‖lᵢ x − lᵢ' x‖ ≤ δᵢ по ternary_layer_pert),
и каждый слой L-липшицев, то суммарное возмущение композиции

  ‖lₙ∘…∘l₁ x − lₙ'∘…∘l₁' x‖ ≤ Σᵢ δᵢ·L^(n−i).

- чистая индукция по списку слоёв, никакой эмпирики.
-/

open Finset

namespace Hagi.Learning.PertTelescope

open Hagi.Learning.TernaryPert

variable {v : ℕ}

/-- Неравенство треугольника для outNorm (Minkowski через
EuclideanSpace-лифт). -/
theorem outNorm_triangle (a b : Fin v → ℝ) :
    outNorm (a + b) ≤ outNorm a + outNorm b := by
  have key : ‖(WithLp.toLp 2 (a + b) : EuclideanSpace ℝ (Fin v))‖
      ≤ ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin v))‖
        + ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin v))‖ :=
    norm_add_le _ _
  have hnorm : ∀ (y : Fin v → ℝ),
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin v))‖ = outNorm y := by
    intro y
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, map_pow, abs_of_nonneg, sq_abs]
    rfl
  rw [← hnorm (a + b), ← hnorm a, ← hnorm b]
  simpa using key

/-- Композиция списка слоёв. -/
def compLayers (ls : List ((Fin v → ℝ) → (Fin v → ℝ))) :
    (Fin v → ℝ) → (Fin v → ℝ) :=
  ls.foldr (· ∘ ·) id

/-- ПАРНАЯ ЛЕММА: возмущение одного слоя + липшицевость
следующего. -/
theorem pert_comp_pair {g1 g1' g2 g2' : (Fin v → ℝ) → (Fin v → ℝ)}
    (hL2 : ∀ y y', outNorm (g2 y - g2 y') ≤ L * outNorm (y - y'))
    (hd1 : ∀ x, outNorm (g1 x - g1' x) ≤ d1)
    (hd2 : ∀ y, outNorm (g2 y - g2' y) ≤ d2)
    (hL2nn : (0:ℝ) ≤ L) (x : Fin v → ℝ) :
    outNorm (g2 (g1 x) - g2' (g1' x)) ≤ L * d1 + d2 := by
  have hsplit : g2 (g1 x) - g2' (g1' x)
      = (g2 (g1 x) - g2 (g1' x)) + (g2 (g1' x) - g2' (g1' x)) := by
    ring
  rw [hsplit]
  have htri := outNorm_triangle (g2 (g1 x) - g2 (g1' x))
    (g2 (g1' x) - g2' (g1' x))
  have h1 := hL2 (g1 x) (g1' x)
  have h2 := hd2 (g1' x)
  refine le_trans htri ?_
  calc outNorm (g2 (g1 x) - g2 (g1' x))
        + outNorm (g2 (g1' x) - g2' (g1' x))
      ≤ L * outNorm (g1 x - g1' x) + d2 :=
          add_le_add h1 h2
    _ ≤ L * d1 + d2 := by
          have hle : outNorm (g1 x - g1' x) ≤ d1 := hd1 x
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hle hL2nn) d2

/-! ### Индукция по списку слоёв -/

/-- Липшицевость композиции точных слоёв (индукция). -/
theorem lip_composition (L : ℝ) (hLnn : (0:ℝ) ≤ L)
    (ls : List ((Fin v → ℝ) → (Fin v → ℝ)))
    (hlip : ∀ g ∈ ls, ∀ y y',
      outNorm (g y - g y') ≤ L * outNorm (y - y'))
    (y y' : Fin v → ℝ) :
    outNorm (compLayers ls y - compLayers ls y')
      ≤ L ^ ls.length * outNorm (y - y') := by
  induction ls generalizing y y' with
  | nil =>
      show (outNorm (id y - id y') : ℝ) ≤ L ^ List.length [] * outNorm (y - y')
      simp only [List.length_nil, pow_zero, one_mul, id_eq]
      exact le_refl (outNorm (y - y'))
  | cons g tail ih =>
      show outNorm (g (compLayers tail y) - g (compLayers tail y'))
        ≤ L ^ (g :: tail).length * outNorm (y - y')
      have hg := hlip g (by simp)
      have htail : outNorm (compLayers tail y - compLayers tail y')
          ≤ L ^ tail.length * outNorm (y - y') :=
        ih (fun g2 hg2 => hlip g2 (List.mem_cons_of_mem g hg2))
          y y' 
      show outNorm (g (compLayers tail y) - g (compLayers tail y'))
        ≤ L ^ (g :: tail).length * outNorm (y - y')
      calc outNorm (g (compLayers tail y) - g (compLayers tail y'))
          ≤ L * outNorm (compLayers tail y - compLayers tail y') :=
            hg _ _
        _ ≤ L * (L ^ tail.length * outNorm (y - y')) := by
            exact mul_le_mul_of_nonneg_left htail hLnn
        _ = L ^ (g :: tail).length * outNorm (y - y') := by
            simp only [List.length_cons, pow_succ]
            ring

/-- Композиция головы над хвостом. -/theorem compLayers_cons (g : (Fin v → ℝ) → (Fin v → ℝ))
    (ls : List ((Fin v → ℝ) → (Fin v → ℝ))) :
    compLayers (g :: ls) = g ∘ compLayers ls := rfl

/-- ГЛАВНЫЙ ТЕЛЕСКОП: для списка пар (точный, возмущённый)
слой с L-липшицевыми точными слоями (L ≥ 1) и равномерной
поточечной ошибкой δ возмущения:

‖comp exact x − comp pert x‖ ≤ n · δ · L^(n−1).

Индукция по списку через парную лемму (pert_comp_pair) и
липшицевость композиции (lip_composition). -/
theorem pert_telescope (L : ℝ) (hL1 : (1:ℝ) ≤ L)
    (pairs : List (((Fin v → ℝ) → (Fin v → ℝ))
      × ((Fin v → ℝ) → (Fin v → ℝ))))
    (delta : ℝ) (hdeltann : (0:ℝ) ≤ delta)
    (hlip : ∀ p ∈ pairs, ∀ y y',
      outNorm (p.1 y - p.1 y') ≤ L * outNorm (y - y'))
    (hdelta : ∀ p ∈ pairs, ∀ x,
      outNorm (p.1 x - p.2 x) ≤ delta)
    (x : Fin v → ℝ) :
    outNorm (compLayers (pairs.map Prod.fst) x
      - compLayers (pairs.map Prod.snd) x)
      ≤ (pairs.length : ℝ) * delta * L ^ pairs.length := by
  induction pairs generalizing x with
  | nil =>
      simp only [List.map_nil, List.length_nil, Nat.cast_zero,
        zero_mul, sub_self]
      unfold outNorm
      simp
  | cons p tail ih =>
      obtain ⟨g, g'⟩ := p
      have hgL : ∀ y y', outNorm (g y - g y')
          ≤ L * outNorm (y - y') := hlip (g, g') (by simp)
      have hgδ : ∀ y, outNorm (g y - g' y) ≤ delta :=
        fun y => hdelta (g, g') (by simp) y
      have ihx : outNorm (compLayers (tail.map Prod.fst) x
          - compLayers (tail.map Prod.snd) x)
          ≤ (tail.length : ℝ) * delta * L ^ tail.length :=
        ih (fun q hq => hlip q (List.mem_cons_of_mem _ hq))
          (fun q hq => hdelta q (List.mem_cons_of_mem _ hq)) x
      have hLpos : (0:ℝ) ≤ L := by linarith
      show outNorm (g (compLayers (tail.map Prod.fst) x)
          - g' (compLayers (tail.map Prod.snd) x))
        ≤ (((g, g') :: tail).length : ℝ) * delta
          * L ^ ((g, g') :: tail).length
      have hsplit : g (compLayers (tail.map Prod.fst) x)
          - g' (compLayers (tail.map Prod.snd) x)
          = (g (compLayers (tail.map Prod.fst) x)
              - g (compLayers (tail.map Prod.snd) x))
            + (g (compLayers (tail.map Prod.snd) x)
              - g' (compLayers (tail.map Prod.snd) x)) := by ring
      rw [hsplit]
      have htri := outNorm_triangle
        (g (compLayers (tail.map Prod.fst) x)
          - g (compLayers (tail.map Prod.snd) x))
        (g (compLayers (tail.map Prod.snd) x)
          - g' (compLayers (tail.map Prod.snd) x))
      refine le_trans htri ?_
      have hA := hgL (compLayers (tail.map Prod.fst) x)
        (compLayers (tail.map Prod.snd) x)
      have hB := hgδ (compLayers (tail.map Prod.snd) x)
      calc outNorm (g (compLayers (tail.map Prod.fst) x)
            - g (compLayers (tail.map Prod.snd) x))
            + outNorm (g (compLayers (tail.map Prod.snd) x)
              - g' (compLayers (tail.map Prod.snd) x))
          ≤ L * outNorm (compLayers (tail.map Prod.fst) x
              - compLayers (tail.map Prod.snd) x) + delta :=
              add_le_add hA hB
        _ ≤ L * ((tail.length : ℝ) * delta * L ^ tail.length)
            + delta :=
              add_le_add_left
                (mul_le_mul_of_nonneg_left ihx hLpos) delta
        _ ≤ (((g, g') :: tail).length : ℝ) * delta
              * L ^ ((g, g') :: tail).length := by
              simp only [List.length_cons, pow_succ]
              have hLge : (1:ℝ) ≤ L ^ tail.length := by
                induction tail.length with
                | zero => simp
                | succ m ih => calc (1:ℝ) = 1 * 1 := by ring
                  _ ≤ L ^ m * L := mul_le_mul ih hL1 (by norm_num) (by linarith)
                  _ = L ^ (m + 1) := by rw [pow_succ]
              have hLpos : (0:ℝ) ≤ L := by linarith
              have hLn : (1:ℝ) ≤ L * L ^ tail.length := by
                have h0 : (1:ℝ) ≤ L ^ (tail.length + 1) := by
                  calc (1:ℝ) = 1 * 1 := by ring
                    _ ≤ L ^ tail.length * L :=
                        mul_le_mul hLge hL1 (by norm_num) (by linarith)
                    _ = L ^ (tail.length + 1) := by rw [pow_succ]
                rw [pow_succ] at h0
                linarith
              have hkey : delta ≤ delta * (L * L ^ tail.length) :=
                calc delta = delta * 1 := by ring
                  _ ≤ delta * (L * L ^ tail.length) :=
                      mul_le_mul_of_nonneg_left hLn hdeltann
              have hLpos : (0:ℝ) ≤ L := by linarith
              have hLnz : (0:ℝ) ≤ L * L ^ tail.length :=
                mul_nonneg hLpos (pow_nonneg hLpos _)
              have hexp : L * ((tail.length : ℝ) * delta
                  * L ^ tail.length) + delta
                  = ((tail.length : ℝ) + 1) * delta * L
                    * L ^ tail.length - delta * (L * L ^ tail.length - 1) := by ring
              have hsym : ((tail.length : ℝ) + 1) * delta
                  * (L ^ tail.length * L)
                  = ((tail.length : ℝ) + 1) * delta * L
                    * L ^ tail.length := by ring
              simp only [Nat.cast_succ]
              rw [hsym]
              nlinarith [hkey, hLpos, pow_nonneg hLpos tail.length]

end Hagi.Learning.PertTelescope
